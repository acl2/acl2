; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; We introduce ev-fncall+ early in this file to support its use in the
; definition of scons-term.

; Essay on Evaluation of Apply$ and Loop$ Calls During Proofs

; (Note: This essay also applies similarly to badge, even though we do not
; discuss badge in it.)

; A goal from the earliest days of ACL2 has been efficient evaluation, not only
; for forms submitted at the top-level loop, but also during proofs.  The
; earliest implementations of apply$, badge, and loop$ limited their evaluation
; during proofs, essentially disallowing apply$ or badge for user-defined
; functions.  This is not particularly unreasonable since attachments are
; disallowed during proofs, which is completely appropriate.

; This situation has been remedied starting in March, 2019, by expanding the
; use in the rewriter of doppelganger-apply$-userfn and
; doppelganger-badge-userfn, for calls of apply$-userfn and badge-userfn on
; concrete arguments, where the first argument has a warrant.  If the warrant
; is not known to be true in the current context, then it is forced (unless it
; is known to be false).  See community book
; books/system/tests/apply-in-proofs.lisp for examples.

; The key idea is that the truth of the warrant for fn justifies replacement of
; (apply$ 'fn '(arg1 ... argk)) by (fn arg1 ... argk); let's call this a
; "warranted replacement".  A version of ev-fncall, ev-fncall+, records the
; warrants that are required to be true in order to make those warranted
; replacements during evaluation.  Ev-fncall+ is actually a small wrapper for
; ev-fncall+-w, which in turn has a raw Lisp implementation that relies on a
; Lisp global, *warrant-reqs*.  The definition of *warrant-reqs* has a comment
; explaining its legal values, and a search of the sources for *warrant-reqs*
; should make reasonably clear how this variable is used; but here is a
; summary.  When *warrant-reqs* has its global value of nil, no special
; behavior occurs: ev-fncall+[-w] essentially reduces to ev-fncall[-w].
; Otherwise, *warrant-reqs* can be initialized to t to represent the empty
; list, and this "list" is extended by maybe-extend-warrant-reqs each time a
; new function requires a true warrant because of a warranted replacement (as
; described above).  Upon completion of a ground evaluation using ev-fncall+,
; this list of functions is returned as the third value of ev-fncall+.  The
; function push-warrants then processes this list of functions as follows: for
; the warrant of each function in that list, either the warrant is known to be
; true or it is forced (except that if it the warrant is known to be false, the
; evaluation is considered to have failed).

; Note that *aokp* must be true for the apply$-lambda and loop$ shortcuts.  So
; for the rewriter as described above, where *aokp* is nil but *warrant-reqs*
; is non-nil, evaluation involving apply$ or loop$ always reduces to evaluation
; of apply$-userfn, which is handled with warranted replacements as described
; above.  At one time we considered allowing these shortcuts for lambdas and
; loop$ forms, and we could reconsider if we want more efficiency.  But the
; current implementation seems to provide sufficient efficiency (until someone
; complains, at least), and has the following advantage: the function symbols
; stored in *warrant-reqs* are exactly those for which warranted replacement is
; used; but if we allow shortcuts for lambdas and loop$ forms, then we will
; need to include all user-defined functions occurring in the lambda body or
; loop$ body even when lying on an IF branch that was not taken during a given
; evaluation.

; We considered handling evaluation in expand-abbreviations as described above
; for the rewriter.  However, there is no type-alist readily available in
; expand-abbreviations for determining which warrants are known to be true.
; Moreover, the rules justifying warranted replacements (with names like
; apply$-fn) are conditional rewrite rules, which we traditionally ignore
; during preprocess-clause (and hence during expand-abbreviations) in favor of
; considering only "simple" rules.  However, we do use ev-fncall+ in
; expand-abbreviations, so that we can avoid wrapping HIDE around the ground
; function application when the evaluation aborted rather than doing a
; warranted replacement.  This case is represented by the case that the third
; value of ev-fncall+[-w] is a function symbol.  Special handling is important
; for this case, to avoid wrapping the call in HIDE, since that would prevent
; the rewriter from later performing a successful evaluation using warranted
; replacements.  Note that we initialize *warrant-reqs* to :nil! in this case
; instead of t, which causes evaluation to abort immediately the first time
; that a warranted replacement is called for.  For very long loops this
; obviously can be important for efficiency!

; We considered also using ev-fncall+ for eval-ground-subexpressions, but that
; seemed to introduce more complexity than it's worth; this could change based
; on user demand.  Since eval-ground-subexpressions does not introduce HIDE, we
; don't have the need for ev-fncall+ that is described above for
; expand-abbreviations.

; Note that our scheme works nicely with the executable-counterpart of apply$
; disabled.  Specifically, all warranted replacements are justified by warrants
; -- actually by rules with names like apply$-fn -- rather than by the
; execution of apply$ calls.

; Next we develop the logical and raw Lisp definitions of ev-fncall+.

(defun warranted-fns-of-world1 (x wrld)

; X is the :badge-userfn-structure of the badge-table.  It is always a
; true-list of elements made by make-badge-userfn-structure-tuple containing a
; fn symbol in the car and a warrantp and badge elsewhere.  We collect each fn
; whose warrantp is non-nil.

; However we must do this in guard-verified manner because the function is used
; in the partial-encapsulate of ev-fncall+-fns.  Since we know x will always be
; of the right shape, it doesn't matter what we do when the shape is wrong, as
; long as we return a list of function symbols.  But we have to check.

  (declare (xargs :mode :logic :guard (plist-worldp wrld)))
  (cond ((atom x) nil)
        ((and (weak-badge-userfn-structure-tuplep (car x))
              (access-badge-userfn-structure-tuple-warrantp (car x))
              (symbolp (car (car x)))
              (function-symbolp (car (car x)) wrld))
         (cons (car (car x))
               (warranted-fns-of-world1 (cdr x) wrld)))
        (t nil)))

(defun warranted-fns-of-world (wrld)

; We return the list of all warranted functions in wrld, but in a way that can
; be guard-verified and can be proved to return a list of function symbols that
; is a subset of the warranted functions of wrld.  The guard verification comes
; later during initialization (in boot-strap-pass-2-a.lisp).

  (declare (xargs :mode :logic
                  :guard (plist-worldp wrld)
                  :verify-guards nil))
  (and (alistp (table-alist 'badge-table wrld))
       (warranted-fns-of-world1
        (cdr (assoc-eq :badge-userfn-structure
                       (table-alist 'badge-table wrld)))
        wrld)))

(partial-encapsulate

; See the Essay on Evaluation of Apply$ and Loop$ Calls During Proofs.

; We think of (ev-fncall+-fns fn args wrld big-n safe-mode gc-off nil) as the
; list of badged functions supplied to apply$-userfn or badge-userfn during
; evaluation of the call of fn on args in wrld using the given
; user-stobj-alist, big-n, safe-mode, and gc-off.  But if the last argument,
; strictp, is non-nil, then we think of the result as the first function symbol
; encountered during evaluation, if any, for which a true warrant was required
; to complete that call of fn.

; The constraint below can almost surely be explicitly strengthened, but we see
; no need at this point.

; Also see ev-fncall+-w.

 (((ev-fncall+-fns * * * * * * *) => *))
 nil

 (logic)

 (local (defun ev-fncall+-fns (fn args wrld big-n safe-mode gc-off strictp)
          (declare (ignore fn args big-n safe-mode gc-off))
          (and (not strictp)
               (warranted-fns-of-world wrld))))

 (local
  (defthm all-function-symbolps-ev-fncall+-fns-lemma
    (all-function-symbolps (warranted-fns-of-world1 x wrld) wrld)))

 (defthm all-function-symbolps-ev-fncall+-fns
   (let ((fns (ev-fncall+-fns fn args wrld big-n safe-mode gc-off nil)))
     (all-function-symbolps fns wrld)))

 (local
  (defthm subsetp-equal-cons
    (implies (subsetp-equal x y)
             (subsetp-equal x (cons a y)))))

 (local
  (defthm subsetp-equal-x-x
    (subsetp-equal x x)))

 (defthm ev-fncall+-fns-is-subset-of-badged-fns-of-world
   (subsetp (ev-fncall+-fns fn args wrld big-n safe-mode gc-off nil)
            (warranted-fns-of-world wrld)))

 (defthm function-symbolp-ev-fncall+-fns-strictp
   (let ((fn (ev-fncall+-fns fn args wrld big-n safe-mode gc-off t)))
     (and (symbolp fn)
          (or (null fn)
              (function-symbolp fn wrld))))))

#+acl2-loop-only
(defun ev-fncall+-w (fn args w safe-mode gc-off strictp)

; See the Essay on Evaluation of Apply$ and Loop$ Calls During Proofs.

; This function allows apply$-userfn and badge-userfn to execute on warranted
; functions even when *aokp* is nil.  It returns an error triple whose
; non-erroneous value is a list of the functions that need warrants in order to
; trust the result.  However, in the case of an error when strictp is true, the
; value is a function symbol responsible for the error when a warrant is
; required so that evaluation is aborted, else nil.  Its implementation is in
; the #-acl2-loop-only definition of this function; the present logical
; definition is incomplete in the sense that ev-fncall+-fns is partially
; constrained.

; This logical definition actually permits a list, computed by constrained
; function ev-fncall+-fns, that properly includes the intended list as a
; subset.  But the under-the-hood implementation of ev-fncall+-w produces
; exactly the set of functions given to apply$-userfn or badge-userfn.

  (let* ((big-n (big-n))
         (fns (ev-fncall+-fns fn args w big-n safe-mode gc-off strictp)))
    (mv-let (erp val latches)
      (ev-fncall-rec-logical fn args
                             nil ; irrelevant arg-exprs (as latches is nil)
                             w
                             nil ; user-stobj-alist
                             big-n safe-mode gc-off
                             nil ; latches
                             t   ; hard-error-returns-nilp
                             nil ; aokp
                             (and (not strictp) fns))
      (declare (ignore latches))
      (mv erp val fns))))

#-acl2-loop-only
(defvar *warrant-reqs*

; See the Essay on Evaluation of Apply$ and Loop$ Calls During Proofs.

; Legal values of this variable are as follows.

; nil -   Always the global value, and always the value when *aokp* is non-nil
; t   -   Represents the empty list, enabling accumulation of function symbols
;         whose (true) warrants support evaluation
; lst   - A non-empty, duplicate-free list, which represents a set of warranted
;         function symbols whose (true) warrants support evaluation
; :nil! - Like nil, but causes evaluation to stop if a warrant is ever required
; fn  -   A function symbol for which evaluation is aborted because its warrant
;         is required (because *warrant-reqs* is :nil!)

  nil)

; The third result of ev-fncall+ is LOGICALLY constrained (in the
; partial-encapsulate in rewrite.lisp before the logic definition of
; ev-fncall+-w) to always be a subset of the functions named in the
; :badge-userfn-structure of the badge-table.  Thus, every function named in
; that third result has a warrant because :badge-userfn-structure is updated
; only by successful defwarrants.  But the COMPUTED value of the third result
; is accumulated in raw Lisp as the value of the special *warrant-reqs*.  This
; comment explains how we know *warrant-reqs* satisfies the constraint.

; The function maybe-extend-warrant-reqs is the only way we add a new element
; to *warrant-reqs*.  That function is called in doppelganger-badge-userfn and
; doppelganger-apply$-userfn.  In both contexts, maybe-extend-warrant-reqs is
; used to extend *warrant-reqs* with a function, fn, that has passed
; query-badge-userfn-structure, which does just what its name suggests: it
; inspects the :badge-userfn-structure.

#-acl2-loop-only
(defun ev-fncall+-w (fn args w safe-mode gc-off strictp)

; See comments in the logic definition of this function.

  (let ((*warrant-reqs*

; See comments in the definition of *warrant-reqs* for a discussion of the
; :nil! and t values of this global.

         (if strictp :nil! t)))
    (declare (special *warrant-reqs*)) ; just to be safe
    (mv-let (erp val latches)
      (ev-fncall-w fn args w
                   nil ; user-stobj-alist
                   safe-mode gc-off
                   t    ; hard-error-returns-nilp
                   nil) ; aok
      (declare (ignore latches))
      (mv erp
          val
          (if (member-eq *warrant-reqs* '(t nil :nil!))
              nil
            *warrant-reqs*)))))

(defun ev-fncall+ (fn args strictp state)

; See the Essay on Evaluation of Apply$ and Loop$ Calls During Proofs.
; Also see comments in the logic definition of ev-fncall+-w.

  (ev-fncall+-w fn args
                (w state)
                (f-get-global 'safe-mode state)
                (gc-off state)
                strictp))

; We start our development of the rewriter by coding one-way-unify and the
; substitution fns.

; Essay on Equivalence, Refinements, and Congruence-based Rewriting

; (Note: At the moment, the fact that fn is an equivalence relation is encoded
; merely by existence of a non-nil 'coarsenings property.  No :equivalence rune
; explaining why fn is an equivalence relation is to be found there -- though
; such a rune does exist and is indeed found among the 'congruences of fn
; itself.  We do not track the use of equivalence relations, we just use them
; anonymously.  It would be good to track them and report them.  When we do
; that, read the Note on Tracking Equivalence Runes in subst-type-alist1.)

; (Note: Some of the parenthetical remarks in this code are extremely trite
; observations -- to the ACL2 aficionado -- added when I sent this commented
; code off to friends to read.)

; We will allow the user to introduce new equivalence relations.  At the
; moment, they must be functions of two arguments only.  Parameterized
; equivalence relations, e.g., x == y (mod n), are interesting and may
; eventually be implemented.  But in the spirit of getting something done right
; and working, we start simple.

; An equivalence relation here is any two argument function that has been
; proved to be Boolean, symmetric, reflexive, and transitive.  The rule-class
; :EQUIVALENCE indicates that a given theorem establishes that equiv is an
; equivalence relation.  (In the tradition of Nqthm, the ACL2 user tells the
; system how to use a theorem when the theorem is submitted by the user.  These
; instructions are called "rule classes".  A typical "event" might therefore
; be:
; (defthm set-equal-is-an-equivalence-rel
;   (and (booleanp (set-equal x y))
;        (set-equal x x)
;        (implies (set-equal x y) (set-equal y x))
;        (implies (and (set-equal x y)
;                      (set-equal y z))
;                 (set-equal x z)))
;   :rule-classes :EQUIVALENCE)
; The rule class :EQUIVALENCE just alerts the system that this formula states
; that something is an equivalence relation.  If the formula is proved, the
; system identifies set-equal as the relation and adds to the database certain
; information that enables the processing described here.)

; The Boolean requirement is imposed for coding convenience.  In
; assume-true-false, for example, when we assume (equiv x y) true, we simply
; give it the type-set *ts-t*, rather than something complicated like its full
; type-set take away *ts-nil*.  In addition, the Boolean requirement means that
; (equiv x y) is equal to (equiv y x) (not just propositionally) and hence we
; can commute it at will.  The other three requirements are the classic ones
; for an equivalence relation.  All three are exploited.  Symmetry is used to
; justify commutativity, which currently shows up in assume-true-false when we
; put either (equiv x y) or (equiv y x) on the type-alist -- depending on
; term-order -- and rely on it to assign the value of either.  Reflexivity is
; used to eliminate (equiv x term) as a hypothesis when x does not occur in
; term or elsewhere in the clause.  Transitivity is used throughout the
; rewriting process.  These are not guaranteed to be all the places these
; properties are used!

; Note: Some thought has been given to the idea of generalizing our work to
; non-symmetric reflexive and transitive relations.  We have seen occasional
; utility for the idea of rewriting with such a monotonic relation, replacing a
; term by a stronger or more defined one.  But to implement that we feel it
; should be done in a completely independent second pass in which monotonic
; relations are considered.  Equivalence relations are of such importance that
; we did not want to risk doing them weakly just to allow this esoteric
; variant.

; Note: We explicitly check that an equivalence relation has no guard because
; we never otherwise consider their guards.  (The "guard" on an ACL2 function
; can be thought of as a "precondition" or a characterization of the domain of
; the function definition.  In Common Lisp many functions, e.g., car and cdr,
; are not defined everywhere and guards are our way of taking note of this.
; Equivalence relations have "no" guard, meaning their guard is t, i.e., they
; are defined everywhere.)

; The motivation behind equivalence relations is to allow their use as :REWRITE
; rules.  For example, after set-equal has been proved to be an equivalence
; relation and union-eq, say, has been proved to be commutative (wrt
; set-equal),

; (implies (and (symbol-listp a)
;               (true-listp a)
;               (symbol-listp b)
;               (true-listp b))
;          (set-equal (union-eq a b) (union-eq b a)))

; then we would like to be able to use the above rule as a rewrite rule to
; commute union-eq expressions.  Of course, this is only allowed in situations
; in which it is sufficient to maintain set-equality as we rewrite.  Implicit
; in this remark is the idea that the rewriter is given an equivalence relation
; to maintain as it rewrites.  This is a generalization of id/iff flag in
; Nqthm's rewriter; that flag indicates whether the rewriter is maintaining
; identity or propositional equivalence.  :CONGRUENCE lemmas, discussed later,
; inform the rewriter of the appropriate relations to maintain as it steps from
; (fn a1 ... an) to the ai.  But given a relation to maintain and a term to
; rewrite, the rewriter looks at all the :REWRITE rules available and applies
; those that maintain the given relation.

; For example, suppose the rewriter is working on (memb x (union-eq b a)),
; where memb is a function that returns t or nil according to whether its first
; argument is an element of its second.  Suppose the rewriter is to maintain
; identity during this rewrite, i.e., it is to maintain the equivalence
; relation equal.  Suppose a :CONGRUENCE rule informs us that equal can be
; preserved on memb expressions by maintaining set-equal on the second
; argument.  Then when rewriting the second argument to the memb, rewrite
; shifts from maintaining equal to maintaining set-equal.  This enables it to
; use the above theorem as a rewrite rule, replacing (union-eq b a) by
; (union-eq a b), just as Nqthm would had the connecting relation been equal
; instead of set-equal.

; This raises the problem of refinements.  For example, we may have some rules
; about union-eq that are expressed with equal rather than set-equal.  For
; example, the definition of union-eq is an equality!  It is clear that a rule
; may be tried if its connecting equivalence relation is a refinement of the
; one we wish to maintain.  By ``equiv1 is a refinement of equiv2'' we mean

; (implies (equiv1 x y) (equiv2 x y)).

; Such rules are called :REFINEMENT rules and are a distinguished rule-class,
; named :REFINEMENT.  Every equivalence relation is a refinement of itself.
; Equal is a refinement of every equivalence relation and no other relation is
; a refinement of equal.

; Every equivalence relation, fn, has a non-nil value for the property
; 'coarsenings.  The value of the property is a list of all equivalence
; relations (including fn itself) known to admit fn as a refinement.  This list
; is always closed under the transitivity of refinement.  That is, if e1 is a
; refinement of e2 and e2 is a refinement of e3, then the 'coarsenings for e1
; includes e1 (itself), e2 (of course), and e3 (surprise!).  This makes it
; easier to answer quickly the question of who is a refinement of whom.

; Equivalence relations are the only symbols with non-nil 'coarsenings
; properties, thus this is the way they are recognized.  Furthermore, the
; 'coarsenings property of 'equal will always list all known equivalence
; relations.

; When we are rewriting to maintain equiv we use any rule that is a known
; refinement of equiv.  Thus, while rewriting to maintain set-equal we can use
; both set-equal rules and equal rules.

; Now we move on to the heart of the matter: knowing what relation to maintain
; at each step.  This is where :CONGRUENCE rules come in.

; To understand the key idea in congruence-based rewriting, consider lemmas of
; the form

; (implies (equiv1 x y)
;          (equiv2 (fn a1 ... x ... an)
;                  (fn a1 ... y ... an))),

; where equiv1 and equiv2 are equivalence relations, the ai, x, and y are
; distinct variables and x and y occur in the kth argument position of the
; n-ary function fn.  These lemmas can be used to rewrite fn-expressions,
; maintaining equiv2, by rewriting the kth argument position maintaining
; equiv1.  In the separate Essay on Patterned Congruences and Equivalences we
; generalize to what we call "patterned congruence rules", but in this Essay we
; focus only on lemmas of the form above.

; We call such a lemma a ``congruence lemma'' and say that it establishes that
; ``equiv2 is maintained by equiv1 in the kth argument of fn.''  The rule-class
; :CONGRUENCE indicates when a lemma is to be so used.

; An example :CONGRUENCE lemma is

; (implies (set-equal a b) (iff (member x a) (member x b))).

; (In my previous example I used memb.  Here I use member, the Common Lisp
; function.  When member succeeds, it returns the tail of its second arg that
; starts with its first.  Thus, (member x a) is not necessary equal to (member
; x b), even when a and b are set-equal.  But they are propositionally
; equivalent, i.e., mutually nil or non-nil.  Iff is just another equivalence
; relation.)

; That is, iff is maintained by set-equal in the second argument of member.
; Thus, when rewriting a member expression while trying to maintain iff it is
; sufficient merely to maintain set-equivalence on the second argument of
; member.  In general we will sweep across the arguments of a function
; maintaining an appropriate equivalence relation for each argument as a
; function of the relation we wish to maintain outside.

; A literal interpretation of the lemma above suggests that one must maintain
; identity on the first argument of member in order to rely on the lemma in the
; second argument.  What then justifies our independent use of :CONGRUENCE
; lemmas in distinct argument positions?

; Congruence Theorem 1.  :CONGRUENCE lemmas for different argument positions of
; the same function can be used independently.  In particular, suppose equiv is
; maintained by e1 in the kth argument of fn and equiv is maintained by e2 in
; the jth argument of fn, where j is not k.  Suppose a is e1 to a' and b is e2
; to b'.  Then (fn ...a...b...) is equiv to (fn ...a'...b'...), where a and b
; occur in the kth and jth arguments, respectively.

; Proof.  By the :CONGRUENCE lemma for equiv and e1 we know that (fn
; ...a...b...) is equiv (fn ...a'...b...).  By the :CONGRUENCE lemma for equiv
; and e2 we know that (fn ...a'...b...) is equiv to (fn ...a'...b'...).  The
; desired result is then obtained via the transitivity of equiv.  Q.E.D.

; Again, we are not considering patterned congruences in the present Essay.
; For the proof above it is important that in the :CONGRUENCE lemma, each
; argument of a call of fn is a distinct variable.

; While we require the user to formulate (non-patterned) :CONGRUENCE lemmas as
; shown above we actually store them in a data structure, called the
; 'congruences property of fn, in which lemmas for different slots have been
; combined.  Indeed, we ``generalize'' still further and allow for more than
; one way to rewrite a given argument position.  If fn has arity n, then the
; 'congruences property of fn is a list of tuples, each of which is of the form
; (equiv slot1 slot2 ... slotn), where equiv is some equivalence relation and
; each slotk summarizes our knowledge of what is allowed in each argument slot
; of fn while maintaining equiv.  The entire n+1 tuple is assembled from many
; different :CONGRUENCE lemmas.  Indeed, it is modified each time a new
; :CONGRUENCE lemma is proved about fn and equiv.  Without discussing yet the
; structure of slotk, such a tuple means:

; (implies (and (or (equiv1.1 x1 y1)
;                   ...
;                   (equiv1.i x1 y1))
;               ...
;               (or (equivn.1 xn yn)
;                   ...
;                   (equivn.j xn yn)))
;          (equiv (fn x1 ... xn)
;                 (fn y1 ... yn))).

; Thus, to rewrite (fn x1 ... xn) maintaining equiv we sweep across the
; arguments rewriting each in turn, maintaining any one of the corresponding
; equivk.l's, which are encoded in the structure of slotk.

; Note that each equivk,l above is attributable to one and only one :CONGRUENCE
; lemma.  Since the ors cause searching, we allow the user to control the
; search by disabling :CONGRUENCE lemmas.  We only pursue paths introduced by
; enabled lemmas.

; The structure of slotk is a list of ``congruence-rules'', which are instances
; of the following record.

(defrec congruence-rule (nume equiv . rune) t)

; The :equiv field is the function symbol of an equivalence relation which, if
; maintained in argument k, is sufficient to maintain equiv for the
; fn-expression; :rune (it stands for "rule name") is the name of the
; :CONGRUENCE lemma that established this link between equiv, :equiv, fn, and
; k; and :nume is the nume of the rune (a "nume" is a unique natural number
; corresponding to a rune, used only to speed up the answer to the question:
; "is the named rule enabled -- i.e., among those the user permits us to apply
; automatically?"), allowing us to query the enabled structure directly.

; Because we allow more than one :CONGRUENCE rule per argument, we have a
; problem.  If we are trying to maintain equiv for fn and are rewriting an
; argument whose slot contains (equivk.1 ... equivk.l), what equivalence
; relation do we try to maintain while rewriting the argument?  We could
; iteratively try them each, rewriting the argument l times.  This suffers
; because some rules would be tried many times due to our use of refinements.
; For example, all of the equality rules would be tried for each equivk.i
; tried.

; It is desirable to eliminate the need for more than one pass through rewrite.
; We would like to rewrite once.  But if we pass the whole set in, with the
; understanding that any refinement of any of them can be used, we are not
; assured that the result of rewrite is equivalent in any of those senses to
; the input.  The reason is that rewrite may recursively rewrite its
; intermediate answer.  (If our rewriter simplifies a to a' it may then rewrite
; a' to a''.)  Thus, a may rewrite to a' maintaining equivk.1 and then a' may
; rewrite to a'' maintaining equivk.2 and it may be that a is not equivalent to
; a'' in either the equivk.1 or equivk.2 sense.  However, note that there
; exists an equivalence relation of which equivk.1 and equivk.2 are
; refinements, and that is the relation being maintained.  Call that the
; ``generated relation.''  Numerous questions arise.  Is the generated relation
; definable in the logic, for if so, perhaps we could allow only one
; equivalence relation per slot per fn and equiv and force the user to invent
; the necessary generalization of the several relations he wants to use.
; Furthermore, if both equivk.1 and equivk.2 maintain equiv in the kth slot of
; fn, does their generated relation maintain it?  We need to know that the
; answer is ``yes'' if we are going to replace a by a'' (which are equivalent
; only in the generated sense) and still maintain the goal relation.

; We have taken the tack of allowing more than one :CONGRUENCE rule per slot by
; automatically (indeed, implicitly) dealing with the generated equivalence
; relations.  To justify our code, we need a variety of theorems about
; generated relations.  We state and prove those now.

; Let e1 and e2 be two binary relations.  We define the relation s ``generated
; by e1 and e2,'' denoted {e1 e2}, as follows.  Because order is unimportant
; below, our set notation {e1 e2} is acceptable.

; (s x y) iff there exists a finite sequence x1, x2, ..., xn such that x = x1,
; y = xn, and for all i, ((e1 xi xi+1) or (e2 xi xi+1)).  We read this as
; saying ``(s x y) iff there is a chain connecting x to y composed entirely of
; e1 and/or e2 links.''

; Congruence Theorem 2. If e1 and e2 are equivalence relations, so is {e1 e2}.

; Proof.  Let s be {e1 e2}.  Then s is reflexive, symmetric, and transitive, as
; shown below.

; Reflexive.  To show that (s x x) holds we must exhibit a sequence linking x
; to x via e1 and/or e2.  The sequence x,x suffices.

; Symmetric.  If (s x y) holds, then there exists a sequence linking x to y via
; e1 and/or e2 steps.  Let that sequence be x, x2, ..., xk, y.  By definition,
; either e1 or e2 links each pair.  Since e1 is symmetric, if a pair, xi, xj,
; is linked by e1 then the pair xj, xi is also linked by e1.  Similarly for e2.
; Thus, the sequence obtained by reversing that above, y, xk, ..., x2, x, has
; the desired property: each pair is linked by e1 or e2.  Therefore, (s y x).

; Transitive.  If (s x y) holds, then there exists a sequence linking x to y,
; say x, x2, ..., xk, y.  If (s y z) holds, there exists a sequence linking y
; to z, say, y, y1, ..., yk, z.  Consider the concatenation of those two
; sequences, x, x2, ..., xk, y, y, y1, ..., yk, z.  It links x and z and every
; pair is linked by either e1 or e2.  Thus, (s x z).

; Q.E.D.

; Thus, the relation generated by two equivalence relations is an equivalence
; relation.

; Congruence Theorem 3. If e1 and e2 are equivalence relations, they are both
; refinements of {e1 e2}.

; Proof.  Let s be {e1 e2}.  We wish to prove (implies (e1 x y) (s x y)) and
; (implies (e2 x y) (s x y)).  We consider the first goal only.  The second is
; symmetric.  But clearly, if x is linked to y by e1 then (s x y) holds, as
; witnessed by the sequence x,y.  Q.E.D.

; Congruence Theorem 4.  Let equiv, e1 and e2 be equivalence relations.
; Suppose equiv is preserved by e1 in the kth argument of fn.  Suppose equiv is
; also preserved by e2 in the kth argument of fn.  Then equiv is preserved by
; {e1 e2} in the kth argument of fn.

; Proof.  Let s be {e1 e2}.  Without loss of generality we restrict our
; attention to a function, fn, of one argument.  We have

; (implies (e1 x y) (equiv (fn x) (fn y)))
; and
; (implies (e2 x y) (equiv (fn x) (fn y)))

; We wish to prove
; (implies (s x y) (equiv (fn x) (fn y)))

; The hypothesis (s x y) establishes that there is a chain linking x to y via
; e1 and/or e2.  Let that chain be x, x2, ..., xk, y.  Since each adjacent pair
; is linked via e1 or e2, and both preserve equiv, we get that (equiv (fn x)
; (fn x2)), (equiv (fn x2) (fn x3)), ... (equiv (fn xk) (fn y)).  By the
; transitivity of equiv, therefore, (equiv (fn x) (fn y)).  Q.E.D.

; Lemma.  If e1 is preserved by e in the kth argument of fn then so is {e1 e2},
; for any relation e2.

; Proof.  We have that (e a b) implies (e1 (f ...a...) (f ...b...)).  Let s be
; {e1 e2}.  We wish to prove that (e a b) implies (s (f ...a...) (f ...b...)).
; But by Congruence Theorem 3 above, e1 is a refinement of s.  Hence, (e1 (f
; ...a...) (f ...b...))  implies (s (f ...a...) (f ...b...)).  Q.E.D.

; Congruence Theorem 5.  Let e1, ..., e4 be equivalence relations.  Then if e2
; is preserved by e1 in the kth argument of fn and e4 is preserved by e3 in the
; kth argument of fn, then {e2 e4} is preserved by {e1 e3} in the kth argument
; of fn.

; Proof.  By the above lemma, we know {e2 e4} is preserved by e1 in the kth
; argument of fn.  Similarly, {e2 e4} is preserved by e3 in the kth argument of
; fn.  Thus, the hypotheses of Theorem 4 are satisfied and we have that {e2 e4}
; is preserved by {e1 e3} in the kth argument of fn.  Q.E.D.

; We generalize the notion of the relation generated by two relations to that
; generated by n relations, {e1, e2, ..., en}.  By the above results, {e1, ...,
; en} is an equivalence relation if each ei is, each ei is a refinement of it,
; and it supports any congruence that all ei support.  We adopt the convention
; that the relation generated by {} is EQUAL and the relation denoted by {e1}
; is e1.

; In our code, generated equivalence relations are represented by lists of
; congruence-rules.  Thus, if cr1 and cr2 are two instances of the
; congruence-rule record having :equivs e1 and e2 respectively, then {e1 e2}
; can be represented by '(cr1 cr2).

; The equivalence relation to be maintained by rewrite is always represented as
; a generated equivalence relation.  In our code we follow the convention of
; always using a variant of the name ``geneqv'' for such an equivalence
; relation.  When a variable contains (or is expected to contain) the name of
; an equivalence relation rather than a :CONGRUENCE rule or geneqv, we use a
; variant of the name ``equiv'' or even ``fn''.

; The geneqv denoting EQUAL is nil.  The geneqv denoting IFF is:

(defconst *geneqv-iff*
  (list (make congruence-rule
              :rune *fake-rune-for-anonymous-enabled-rule*
              :nume nil
              :equiv 'iff)))

; This completes our general essay on the subject.  The theorems proved above
; are mentioned by name elsewhere in our code.  In addition, various details
; are discussed elsewhere.  For a simple example of how all of this works
; together, see the function subst-equiv-expr which implements substitution of
; new for old in term to produce term', where it is given that new is equiv1
; old and term is to be equiv2 term'.

; We now turn to the most primitive functions for manipulating equivalences and
; generated equivalences.  We deal with refinements first and then with the
; question of congruences.

(defun refinementp (equiv1 equiv2 wrld)

; Note: Keep this function in sync with refinementp1.

; (ACL2 is an applicative subset of Common Lisp.  When this
; function, refinementp, is called, its third argument, wrld, will be
; the current "property list world" which is just an association
; list binding symbols and property names to values.  The lookup of
; a symbol's property in wrld is via the ACL2 function getprop.
; Getprop is coded in a clever way so that in the case that the
; world is in fact that implicit in the global property list
; structure of Common Lisp, then getprop is just Common Lisp's
; non-applicative get.  In our code, wrld is always that world,
; but the code works correctly -- if somewhat more slowly -- if
; called on a different world.)

; Both equiv1 and equiv2 are function symbols.  We determine whether
; equiv1 is a known refinement of equiv2, given wrld.  If we return t
; we must be correct.  Nil means ``maybe not.''  For an explanation of
; why our database contains the 'coarsenings property instead of the
; inverse 'refinements property, see the discussion of
; geneqv-refinements below.

  (cond ((eq equiv1 'equal)

; Equal is a refinement of all equivalence relations.

         t)
        ((eq equiv2 'equal)

; No other relation is a refinement of equal.

         nil)
        ((eq equiv1 equiv2)

; Every equivalence relation is a refinement of itself.

         t)
        (t

; Otherwise, look for equiv2 among the known coarsenings of equiv1.
; The database must be kept so that the transitive property of
; refinement is manifested explicitly.  This function is called very
; often and we do not want to go searching through the transitive
; closure of refinementhood or coarseninghood.  So if e1 is a known
; refinement of e2 and e2 is a known refinement of e3, then the
; 'coarsenings property of e1 must include not just e2 but also e3.
; We know the first element in the 'coarsenings of equiv1 is equiv1
; -- which isn't equiv2 -- so we skip it.

         (member-eq equiv2
                    (cdr (getpropc equiv1 'coarsenings nil wrld))))))

; The above function determines if one equivalence symbol is a
; refinement of another.  More often we want to know whether a symbol
; is a refinement of a generated equivalence relation.  That is, is e1
; a refinement of {e2 e3}?  The most common occurrence of this
; question is when we are maintaining {e2 e3} and want to know if we
; can apply a :REWRITE rule about e1.

(defun geneqv-refinementp1 (coarsenings geneqv)

; We determine whether any name in coarsenings is the :equiv of any
; :CONGRUENCE rule in geneqv.  If so, we return the :rune of the rule
; found.

  (cond ((null geneqv) nil)
        ((member-eq (access congruence-rule (car geneqv) :equiv)
                    coarsenings)
         (access congruence-rule (car geneqv) :rune))
        (t (geneqv-refinementp1 coarsenings (cdr geneqv)))))

(defun geneqv-refinementp (equiv geneqv wrld)

; We determine whether the equivalence relation symbol equiv is a
; known refinement of the generated relation geneqv.  If so, we return
; the rune of the :CONGRUENCE rule in geneqv used, or
; *fake-rune-for-anonymous-enabled-rule* if equality was used.
; Otherwise we return nil.

; This function is used both as a function and a predicate.  Its
; primary use is as a predicate, typically to determine whether it is
; permitted to use a :REWRITE rule whose top-level equivalence is
; equiv.  If the function reports success and the rewrite in fact
; succeeds, the caller will typically use the value of the function as
; the rune of the :CONGRUENCE rule used, adding it into the tag-tree of
; the term being rewritten.

; Note: If the database contained only a 'refinements property for e2
; and e3, we would have to access both of them to determine whether e1
; was among the known refinements.  But if the database contains a
; 'coarsenings property for e1 we can access just that and then look
; for e2 or e3 in it.  This saves us doing unnecessary getprops.

; Historical Note: Once we passed around geneqvs that contained
; possibly disabled :CONGRUENCE rules and this function got, as an
; additional argument, the current enabled structure and had the job
; of ignoring those :CONGRUENCE rules.  This proved cumbersome and we
; adopted the idea of passing around geneqvs that are fully enabled.
; It means, of course, filtering out the disabled components when we
; form new geneqvs from those in the database.  In any case, this
; function does not get the enabled structure and takes no note of the
; status of any rule.

  (cond ((eq equiv 'equal) *fake-rune-for-anonymous-enabled-rule*)
        ((null geneqv) nil)
        (t (geneqv-refinementp1 (getpropc equiv 'coarsenings nil wrld)
                                geneqv))))

; We now define the function which constructs the list of generated
; equivalences to be maintained across the arguments of fn, as a
; function of the generated equivalence to be maintained overall and
; the current enabled structure.  Our main concern, technically, here
; is to avoid consing.  Most often, we expect that the list of geneqvs
; stored a given fn will be the list we are to return, because we will
; be trying to maintain just one primitive equivalence and we will
; know at most one way to do it for each arg, and none of the
; :CONGRUENCE rules are disabled.  So we start with the function that
; filters out of the geneqv stored in slot k all of the disabled
; congruences -- and we code it so as to first check to see whether
; anything needs to be removed.  Then we move up to the corresponding
; operation on a stored list of geneqvs.  Finally, we consider the
; problem of unioning together the slot k's for all of the primitive
; equivalences to be maintained.

(defun some-congruence-rule-disabledp (geneqv ens)
  (cond ((null geneqv) nil)
        ((enabled-numep (access congruence-rule (car geneqv) :nume) ens)
         (some-congruence-rule-disabledp (cdr geneqv) ens))
        (t t)))

(defun filter-geneqv1 (geneqv ens)
  (cond ((null geneqv) nil)
        ((enabled-numep (access congruence-rule (car geneqv) :nume) ens)
         (cons (car geneqv) (filter-geneqv1 (cdr geneqv) ens)))
        (t (filter-geneqv1 (cdr geneqv) ens))))

(defun filter-geneqv (geneqv ens)

; Geneqv is a set (list) of :CONGRUENCE rules, generally retrieved from
; slot k of some equiv entry on some function's 'congruences.  We
; return the subset consisting of the enabled ones.  We avoid consing
; if they are all enabled.

  (cond ((some-congruence-rule-disabledp geneqv ens)
         (filter-geneqv1 geneqv ens))
        (t geneqv)))

; Now we repeat this exercise one level higher, where we are dealing with
; a list of geneqvs.

(defun some-geneqv-disabledp (lst ens)
  (cond ((null lst) nil)
        ((some-congruence-rule-disabledp (car lst) ens) t)
        (t (some-geneqv-disabledp (cdr lst) ens))))

(defun filter-geneqv-lst1 (lst ens)
  (cond ((null lst) nil)
        (t (cons (filter-geneqv (car lst) ens)
                 (filter-geneqv-lst1 (cdr lst) ens)))))

(defun filter-geneqv-lst (lst ens)

; It is handy to allow ens to be nil, indicating that nothing is disabled.

  (cond ((null ens)
         lst)
        ((some-geneqv-disabledp lst ens)
         (filter-geneqv-lst1 lst ens))
        (t lst)))

; Next we must union together two lists of :CONGRUENCE rules.  To keep
; the lists from getting large we will eliminate refinements.  That
; is, if we have {e1 e2} U {e3 e4}, and e1 is a refinement of e3, but
; there is no refinement relation between e2, e3 and e4, then the
; answer will be {e2 e3 e4}.  In general, we will assume the two lists
; are free of internal refinement relations and we will generate such
; a list.  It is a little messy because e3 may be a refinement of e2,
; say.  In which case the answer is {e2 e4}.

(defun refinementp1 (equiv1 coarsenings1 equiv2)

; Note: Keep this function in sync with refinementp.

; Both equiv1 and equiv2 are function symbols and coarsenings1 is the
; cdr of the 'coarsenings property of equiv1 (the car of that property
; is equiv1 itself).  We determine whether equiv1 is a known
; refinement of equiv2.  This function should be kept in sync with the
; more general refinementp.

  (cond ((eq equiv1 'equal) t)
        ((eq equiv2 'equal) nil)
        ((eq equiv1 equiv2) t)
        (t (member-eq equiv2 coarsenings1))))

(defun pair-congruence-rules-with-coarsenings (geneqv wrld)

; We pair each congruence rule in geneqv with non-id coarsenings,
; i.e., the cdr of the 'coarsenings property of its :equiv.

  (cond
   ((null geneqv) nil)
   (t (cons (cons (car geneqv)
                  (cdr (getpropc (access congruence-rule (car geneqv) :equiv)
                                'coarsenings nil wrld)))
            (pair-congruence-rules-with-coarsenings (cdr geneqv) wrld)))))

(defun add-to-cr-and-coarsenings
  (new-cr new-cr-coarsenings old-crs-and-coarsenings both-tests-flg)

; New-cr is a congruence rule and new-cr-coarsenings is the
; 'coarsenings property of its :equiv.  Note that the car of
; new-cr-coarsenings is thus the :equiv name.  Old-crs-and-coarsenings
; is a list of pairs of the form (congruence-rule . non-id-coarsenings).
; We assume no member of the old list refines any other member.

; We ``add'' the new pair (new-cr . non-id-new-cr-coarsenings) to the old
; list.  However, if new-cr is a refinement of any equiv in the old
; list, we do nothing.  Furthermore, if any member of the old list is
; a refinement of new-cr, we delete that member.

  (cond
   ((null old-crs-and-coarsenings)

; Add the new-cr and its non-id coarsenings to the list.

    (list (cons new-cr (cdr new-cr-coarsenings))))
   ((and both-tests-flg
         (refinementp1
          (car new-cr-coarsenings) ; new-equiv
          (cdr new-cr-coarsenings) ; new-equiv's non-id coarsenings
          (access congruence-rule  ; first old-equiv
                  (car (car old-crs-and-coarsenings))
                  :equiv)))

; The new equiv is a refinement of the first old one.  Nothing to do.

    old-crs-and-coarsenings)
   ((refinementp1
     (access congruence-rule ; first old-equiv
             (car (car old-crs-and-coarsenings))
             :equiv)
     (cdr (car old-crs-and-coarsenings)) ; first old-equiv's non-id coarsenings
     (car new-cr-coarsenings))           ; new-equiv

; The first old equiv is a refinement of the new one.  Delete the old
; one.  Continue inserting the new one -- it may cause other
; refinements to be deleted.  But there is no possibility that it will
; be dropped because any old cr which it refines would have been
; refined by the one we just dropped.  So we can henceforth only test for
; this case.

    (add-to-cr-and-coarsenings new-cr new-cr-coarsenings
                               (cdr old-crs-and-coarsenings)
                               nil))
   (t (cons (car old-crs-and-coarsenings)
            (add-to-cr-and-coarsenings new-cr new-cr-coarsenings
                                       (cdr old-crs-and-coarsenings)
                                       both-tests-flg)))))

(defun union-geneqv1 (geneqv1 old-crs-and-coarsenings wrld)

; Geneqv1 is a geneqv and old-crs-and-coarsenings is a list of pairs
; of the form (congruence-rule . coarsenings), where the coarsenings
; are the non-id coarsenings of the :equiv of the corresponding
; congruence-rule.  This data structure makes it possible to answer
; refinement questions without going back to the world.  We scan down
; geneqv1 and augment old-crs-and-coarsenings, adding a new
; (congruence-rule . non-id-coarsenings) pair for each congruence rule in
; geneqv1 that is not a refinement of any rule already in the old set.
; In addition, if we find an old rule that is a refinement of some new
; one, we drop it from the old set, replacing it with the new one.

  (cond
   ((null geneqv1) old-crs-and-coarsenings)
   (t (union-geneqv1 (cdr geneqv1)
                     (add-to-cr-and-coarsenings (car geneqv1)
                                                (getpropc
                                                 (access congruence-rule
                                                         (car geneqv1)
                                                         :equiv)
                                                 'coarsenings nil wrld)
                                                old-crs-and-coarsenings
                                                t)
                     wrld))))

(defun union-geneqv (geneqv1 geneqv2 wrld)

; We union together the congruence rules in the two geneqv's, forming
; a set with the property that no element in it is a refinement of any
; other.  Roughly speaking we simply add the equivs of geneqv1 into
; those of geneqv2, not adding any that is a refinement and deleting
; any that is refined by a new one.  To make this process faster we
; first annotate geneqv2 by pairing each congruence rule in it with
; the non-id 'coarsenings property of its :equiv.  Union-geneqv1 does the
; work and returns such an annotated list of congruence rules.  We
; convert that back into a geneqv by stripping out the annotations.

  (strip-cars
   (union-geneqv1
    geneqv1
    (pair-congruence-rules-with-coarsenings geneqv2 wrld)
    wrld)))

; And now we do slotwise union.

(defun pairwise-union-geneqv (lst1 lst2 wrld)

; Lst1 and lst2 are lists of geneqvs that are in 1:1 correspondence.
; We pairwise union their elements.

  (cond ((null lst1) nil)
        (t (cons (union-geneqv (car lst1) (car lst2) wrld)
                 (pairwise-union-geneqv (cdr lst1) (cdr lst2) wrld)))))

; That brings us to the main function we've been wanting: the one that
; determines what generated equivalence relations must be maintained
; across the the arguments of fn in order to maintain a given
; generated equivalence relation for the fn-expression itself.  Because
; we form new geneqvs from stored ones in the database, we have to
; have the enabled structure so we filter out disabled congruence
; rules.

(defun geneqv-lst1 (congruences geneqv ens wrld)

; Congruences is the list of congruences of a certain function, fn.
; Geneqv is a list of congruence-rules whose :equiv relations we are
; trying to maintain as we sweep across the args of fn.  For each
; element of congruences, (equiv slot1 ... slotn), such that equiv is
; an element of geneqv we filter disabled rules out of each slot and
; then union together corresponding slots.

; In coding this, the following question arose.  ``Should we include
; those equiv that are refinements of elements of geneqv or just those
; that are literally elements of geneqv?''  Our answer is ``include
; refinements.''  Suppose geneqv is {set-equal}.  Suppose list-equal
; is a known refinement of set-equal.  Suppose that for the fn in
; question we know a :CONGRUENCE rule that preserves list-equal but we
; know no rules that preserve set-equal.  Then if we do not include
; refinements we will be fooled into thinking that the only way to
; preserve set-equal for the fn is to preserve equal across the args.
; But if we do include refinements we will know that we can admit
; whatever relations are known to maintain list-equal across the args.

  (cond ((null congruences)

; This is a little subtle.  We return nil where we ought to return a
; list of n nils.  But it is ok.  An optimization below (in which we
; avoid pairwise-union-geneqv when the second arg is nil) makes it
; clearly ok.  But even without the optimization it is ok because
; pairwise-union-geneqv is controlled by its first arg!

         nil)
        (t (let ((ans (geneqv-lst1 (cdr congruences) geneqv ens wrld)))
             (cond
              ((geneqv-refinementp (caar congruences) geneqv wrld)
               (cond
                ((null ans)
                 (filter-geneqv-lst (cdar congruences) ens))
                (t (pairwise-union-geneqv
                    (filter-geneqv-lst (cdar congruences) ens)
                    ans
                    wrld))))
              (t ans))))))

; On the Optimization of Geneqv-lst

; Once upon a time we suspected that geneqv-lst might be causing a significant
; slowdown of ACL2 compared to Nqthm.  So we tried the following experiment.
; First we ran the code on the Nqthm package and learned that geneqv-lst is
; called a total of 876843 times.  The entire series of proofs took 1654
; seconds (on Rana, a Sparc 2).  Then we recoded the function so that it saved
; every input and output and reran it on the proof of the Nqthm package to
; collect all io pairs.  Analyzing the io pairs showed that we could reproduce
; the behavior of geneqv-lst on that series of proofs with the following code.
; Note that this does does not look at the property lists nor at the enabled
; structure.  Nor does it do any consing.

;    (defun geneqv-lst (fn geneqv ens wrld)
;     (declare (ignore ens wrld))
;   ; (setq geneqv-cnt (1+ geneqv-cnt))
;     (cond
;      ((and (eq fn 'IFF)
;            (equal geneqv *geneqv-iff*))
;       '(((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
;         ((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))))
;      ((and (eq fn 'IMPLIES)
;            (equal geneqv *geneqv-iff*))
;       '(((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
;         ((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))))
;      ((eq fn 'IF)
;       (cond
;        ((null geneqv)
;         '(((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
;           nil nil))
;        ((equal geneqv *geneqv-iff*)
;         '(((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
;           ((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
;           ((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))))
;        (t nil)))
;      ((and (eq fn 'NOT)
;            (equal geneqv *geneqv-iff*))
;       '(((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))))
;      (t nil)))

; (Note: ((NIL IFF :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL)) is just
; *geneqv-iff*.)

; Then we recompiled the entire ACL2 system with this definition in place (to
; ensure that the calls were all fast) and reran the Nqthm package proofs.  The
; result was that it took 1668 seconds!

; Not wanting to believe these results (it seems so obvious that this function
; is inefficient!) we tried redefining geneqv-lst so that always returned nil.
; This is not the same behavior as the geneqv-lst below, but at least it is
; fast.  The resulting proofs took 1780 seconds but investigation showed that
; some proofs followed different paths, so this experiment was discounted.

; Next, we simply remembered the complete sequence of answers generated by the
; code below (all 876843 of them) and then redefined the function to feed back
; those very answers in the same sequence.  The answers were pushed into a
; stack during one run, the stack was reversed, and the answers were popped off
; during the second run.  The code for geneqv-lst was simply (pop
; geneqv-stack).  We cannot imagine a faster implementation.  The second
; run took 1685 seconds.

; The conclusion of these experiments is that geneqv-lst is not likely to be
; optimized!

(defun geneqv-lst (fn geneqv ens wrld)

; Suppose we are attempting to rewrite a term whose function is fn while
; maintaining the generated equivalence relation geneqv.  Fn may be a lambda
; expression.  We return the list of generated equivalence relations to be
; maintained at each argument position.  See the essay above for some
; experiments on the optimization of this function.

; For example, while rewriting a MEMBER expression, (MEMBER x s) to
; maintain IFF we should rewrite x maintaining EQUAL and rewrite s
; maintaining SET-EQUAL.  That is, given MEMBER and IFF (for fn and
; geneqv) we wish to return (EQUAL SET-EQUAL), a list in 1:1
; correspondence with the formals of fn giving the equivalence
; relations that must be maintained for the arguments in order to
; maintain geneqv.  However, rather than (EQUAL SET-EQUAL) we return a
; list of two geneqvs, namely '(nil (cr)), where cr is the congruence
; rule which establishes that IFF is maintained by SET-EQUAL in the
; 2nd arg of MEMBER.

; The fact that nil denotes the equivalence generated by 'EQUAL,
; combined with the facts that the car and cdr of nil are nil, allows
; us to return nil to denote a list of a suitable number of generated
; equalities.  Thus, the answer nil is always correct and is in fact
; the answer returned for all those functions for which we know no
; :CONGRUENCE rules.

; If fn is a lambda-expression, we return nil.  Otherwise, the
; 'congruences property of the symbol fn is an alist.  The entries of
; the alist are of the form (equiv geneqv1 ... geneqvn).  Consider the
; entry for each refinement of some :equiv in the goal geneqv, after
; filtering out the disabled rules from each:

; (equiv1 geneqv1,1 ... geneqv1,n)
; (equiv2 geneqv2,1 ... geneqv2,n)
; ...
; (equivk geneqvk,1 ... geneqvk,n)

; The union down the first column is geneqv.  Let the union down
; subsequent columns be geneqv1, ... geneqvn.  Then by Congruence
; Theorem 5, we have that geneqv is maintained by geneqvi in the ith
; argument of fn.  Thus, we return (geneqv1 ... geneqvn).

; Observe that if some equivj in geneqv is not mentioned in the
; known congruences then we have, implicitly, the entry

; (equivj {} ... {}) and so its contribution to the union is
; justifiably ignored.

; Observe that if we throw away a disabled rule from a geneqvi,j we
; are just strengthening the equivalence relation to be maintained
; in that slot.  Thus, our heuristic use of ens is sound.

; We allow ens to be nil, to signify that all rules are to be considered as
; enabled.

  (cond ((flambdap fn) nil)
        ((eq fn 'if)

; IF is an unusual function symbol vis-a-vis congruence.  We know that
; equality is preserved by iff in the 1st argument of IF.  But more
; significantly, for every equivalence relation, equiv, we have that
; equiv is preserved by equiv in the 2nd and 3rd arguments of if.
; Thus, we could store a lot of congruences under IF, one for each
; equivalence relation:  (equiv iff equiv equiv).  Instead, we just
; manufacture it when we are asked.  This is inefficient in that we
; may cons up the same structure repeatedly.  But we do not suffer
; as much as one might think because the really heavy-duty users of
; geneqv-lst, e.g., rewrite, build in their handling of IF anyway and
; never call geneqv-lst on 'IF.

         (list *geneqv-iff* geneqv geneqv))
        (t (let ((congruences (getpropc fn 'congruences nil wrld)))
             (cond
              ((null congruences) nil)
              ((null geneqv)

; This is a special case.  If we are trying to maintain equality
; then the likelihood is that we have to maintain equality across
; the args, i.e., return nil.  But it is possible that the congruences
; for fn lists 'equal explicitly.  If so, we use those.  Otherwise nil.
; But we have to filter for disabled rules.

               (filter-geneqv-lst (cdr (assoc-eq 'equal congruences)) ens))
              (t

; This is the general case in which the function has some known congruence
; relations and the equivalence relation we are trying to maintain is not just
; equality.  In this case, we are prepared to to do some consing.

               (geneqv-lst1 congruences geneqv ens wrld)))))))


; As an exercise in the use of the equivalence and congruence stuff, we
; now code the function that substitutes one term for another maintaining
; a given generated equivalence.  We begin with elementary substitution
; because it illustrates the fundamental notion of substitution.

; Elementary Expression Substitution (``Equals for Equals'')

; Students of our code might find it helpful to look at subst-var
; before looking at the following.

; We show how to substitute one term, new, for another term, old,
; in a term.  The presumption is that new and old are known to be
; equal.  This might be used, for example, to substitute
; A for (CAR (CONS A B)) in (FOO (CAR (CONS A B))) to produce
; (FOO A).

(mutual-recursion

(defun subst-expr1 (new old term)
  (declare (xargs :guard (and (pseudo-termp new)
                              (pseudo-termp old)
                              (pseudo-termp term))))
  (cond ((equal term old) new)
        ((variablep term) term)
        ((fquotep term) term)
        (t (cons-term (ffn-symb term)
                      (subst-expr1-lst new old (fargs term))))))

(defun subst-expr1-lst (new old args)
  (declare (xargs :guard (and (pseudo-termp new)
                              (pseudo-termp old)
                              (pseudo-term-listp args))))
  (cond ((endp args) nil)
        (t (cons (subst-expr1 new old (car args))
                 (subst-expr1-lst new old (cdr args))))))

)

(defun subst-expr-error (const)
  (declare (xargs :guard nil))
  (er hard 'subst-expr-error
      "An attempt was made to substitute for the explicit value ~x0.  ~
       The substitution functions were optimized to disallow this."
      const))

(defun subst-expr (new old term)
  (declare (xargs :guard (and (pseudo-termp new)
                              (pseudo-termp old)
                              (not (quotep old))
                              (pseudo-termp term))))
  (cond ((variablep old) (subst-var new old term))
        ((fquotep old) (subst-expr-error old))
        (t (subst-expr1 new old term))))

; Congruence-Based Substitution:

; Below we develop the function that substitutes new for old into
; term, where new is equiv to old and we are supposed to produce an
; answer that is geneqv to term.  The main reason we're developing
; this function is to solidify our ideas on congruence rewriting.

; Note: The relation between new and old is some primitive
; equivalence, i.e., equiv is a function symbol.  But the relation we
; are trying to maintain is a generated equivalence, i.e., a set of
; primitive equivs.  We could pursue the idea of generalizing equiv to
; a generated equivalence.  However, we don't, at the moment, see the
; value in that.  In the first place, this function is meant as a
; model of how rewrite should handle geneqvs and each :REWRITE rule is
; about a single primitive equivalence, not a generated equivalence.
; In the second place, everywhere this function is used, e.g., when we
; eliminate a (set-equal a b) hyp in the conjecture by substituting a
; for b, we have a primitive equiv relating the two.  Now we will need
; the generalized version of this function if we ever obtain b, say,
; by rewriting a under some generated equivalence.  The resulting a
; and b are not related by a primitive equiv.  But we will wait until
; we need that to implement it.

; Here is an example of the kind of substitution we implement.  Let
; list-equal be the equivalence relation that is element by element
; equality on lists (ignoring the final cdr).  Let set-equal be
; permutationp.  Suppose that if a is set-equal to b then (listify a)
; is list-equal to (listify b).  A model of listify is that it removes
; duplicates and sorts with some total ordering, but preserves the
; final cdr just to prevent (listify a) from being equal to (listify
; b).  Suppose further that if x is list-equal to y then (member e x)
; iff (member e y).

; Given the foregoing, we have three equivalence relations,
; list-equal, set-equal, and iff, and two congruences.

; Under the 'congruences property of listify we have the congruence
; (list-equal ((nume set-equal . rune))) which means that list-equal
; is preserved by set-equal in the first argument of listify.

; Under the 'congruences property of member we have (iff nil ((nume
; list-equal . rune))) which means that iff is preserved by list-equal
; in the second argument of member.  The nil implicitly says ``iff is
; preserved by equal in the first argument of member.''

; Now suppose we want to substitute a for b (which are known to be
; set-equal) into (member e (listify b)) maintaining iff.  Then we see
; that iff can be maintained on the member expression if we substitute
; a for b in (listify b) maintaining list-equal.  Then we see that
; list-equal can be maintained on the listify expression if we
; substitute a for b in b maintaining set-equal.  But a is set-equal
; to b.  So we get (member e (listify a)).

; Now let us refine this slightly.  What does it mean for one
; equivalence relation, e1, to be a refinement of another, e2?  It
; means that (implies (e1 a b) (e2 a b)).  That is, if a and b are
; in a refinement of e2 they are in e2.  So for example, EQUAL is a
; refinement of every equivalence relation because (implies (equal a
; b) (e2 a b)) is the same as (e2 a a), which is just reflexivity.

; So suppose a is equiv1 to b and we want to substitute a for b in b
; maintaining equiv2.  What is a sufficient condition on equiv1 and
; equiv2?  Equiv1 must be a refinement of equiv2.  That is, they must
; be ``even more alike'' than equiv2 requires, in the sense of being
; in a smaller equivalence class.

; In our actual implementation equiv2 is generalized to a generated
; equivalence relation.

(defun comment-fn (x y)

; If y is a term, then (comment-fn x y) is a term.  We take advantage of this
; fact when calling comment-fn in hide-with-comment.

  (declare (xargs :guard t))
  `(return-last 'progn '(:comment . ,x) ,y))

(defmacro comment (x y)
  (comment-fn x y))

(defstub hide-with-comment-p () t)
(defattach hide-with-comment-p constant-t-function-arity-0)

(defun hide-with-comment (reason term wrld state)

; Reason should be either nil or of one of the forms (:kwd . data) recognized
; below.

  (declare (xargs :mode :program :stobjs state))
  (cond
   ((or (null reason)
        (null (hide-with-comment-p)))
    (fcons-term* 'hide term))
   (t
    (flet ((reason-string
            (erp scons-term-p wrld state)
            (let* ((fn (and (consp erp)
                            (eq (car erp)
                                'ev-fncall-null-body-er)
                            (symbolp (cdr erp))
                            (cdr erp)))
                   (fn (if (eq fn :non-exec) 'non-exec fn)))
              (and fn
                   (let* ((non-executablep
                           (getpropc fn 'non-executablep nil wrld))
                          (skip-pkg-prefix
                           (symbol-in-current-package-p fn state))
                          (str0 (if scons-term-p
                                    "Failed attempt (when building a term) to ~
                                     call "
                                  "Failed attempt to call "))
                          (str1 (if (eq fn 'non-exec)
                                    ""
                                  (if non-executablep
                                      "non-executable function "
                                    "constrained function "))))
                     (if skip-pkg-prefix
                         (concatenate 'string str0 str1 (symbol-name fn))
                       (concatenate 'string
                                    str0
                                    str1
                                    (symbol-package-name fn)
                                    "::"
                                    (symbol-name fn))))))))
      (case-match reason
        ((:non-executable . erp)
         (let ((reason-string (reason-string erp nil wrld state)))
           (fcons-term* 'hide
                        (if reason-string
                            (comment-fn reason-string term)
                          term))))
        ((:scons-term . erp)
         (let ((reason-string (reason-string erp t wrld state)))
           (fcons-term* 'hide
                        (if reason-string
                            (comment-fn reason-string term)
                          term))))
        ((:expand rune . skip-pkg-prefix)
         (fcons-term* 'hide
                      (comment-fn
                       (let ((name
                              (if skip-pkg-prefix
                                  (symbol-name (base-symbol rune))
                                (concatenate
                                 'string
                                 (symbol-package-name (base-symbol rune))
                                 "::"
                                 (symbol-name (base-symbol rune))))))
                         (concatenate
                          'string
                          "Unable to expand using the rule "
                          name))
                       term)))
        ((:missing-warrant . fn?)
         (fcons-term*
          'hide
          (comment-fn
           (let* ((disabledp (consp fn?))
                  (fn (if disabledp
                          (car fn?) ; apply$-fn
                        fn?))
                  (skip-pkg-prefix (symbol-in-current-package-p fn state))
                  (fn-str (if skip-pkg-prefix
                              (symbol-name fn)
                            (concatenate
                             'string
                             (symbol-package-name fn)
                             "::"
                             (symbol-name fn)))))
             (concatenate
              'string
              "Call failed because "
              (if disabledp
                  (concatenate
                   'string
                   "the rule "
                   fn-str
                   " is disabled")
                (concatenate
                 'string
                 "the warrant for "
                 fn-str
                 " is not known to be true"))))
           term)))
        (& (er hard 'hide-with-comment
               "Unexpected reason supplied to ~x0!"
               'hide-with-comment)))))))

(defun scons-term (fn args ens wrld state ttree)

; This function is (cons-term fn args) except that we evaluate any enabled fn
; on quoted arguments and may do any other replacements that preserve equality
; (e.g., (equal x x) = t).  In addition, we report the executable counterparts
; we use by adding them to ttree.  We return (mv hitp term ttree'), where: hitp
; is t iff term is something different than (cons-term fn args); term is
; provably equal to (cons-term fn args); and ttree' is an extension of ttree
; this equality.

  (cond
   ((and (all-quoteps args)
         (or (flambdap fn)
             (and (enabled-xfnp fn ens wrld)

; We don't mind disallowing constrained functions that have attachments,
; because the call of ev-fncall below disallows the use of attachments (last
; parameter, aok, is nil).

                  (not (getpropc fn 'constrainedp nil wrld)))))

; Note: This code is supposed to be the same as in rewrite.  Keep them in sync
; and see the comment there for explanations.

    (cond ((flambdap fn)

; This is a problematic case.  At first sight, we could just create the term
; (fn . args) and then evaluate it with ev.  (We can't use ev-fncall as we do
; below because it doesn't handle lambdas.)  But this ignores some problems.
; How do we avoid evaluating :program fns that occur in the body?  How do
; we avoid evaluating disabled fns in the body?  How do we report the
; executable-counterparts we use?  Problems, problems.  We punt.

           (mv nil (cons-term fn args) ttree))
          ((eq fn 'if)
           (mv t
               (if (cadr (car args))
                   (cadr args)
                   (caddr args))
               ttree))
          ((programp fn wrld)

; It is March, 2019, and we ask: Is this test needed?  At one time we said "see
; the comment in rewrite", but there seems to be no such comment in rewrite.
; Perhaps it is no longer needed, but we keep this programp case just to be
; safe.  Also, we formerly returned t as the first value in this case, but that
; seems wrong so we return nil now.

           (mv nil (cons-term fn args) ttree))
          (t
           (mv-let
            (erp val bad-fn)
            (pstk
             (ev-fncall+ fn (strip-cadrs args) t state))
            (cond
             (erp
              (cond
               (bad-fn

; Since bad-fn is non-nil, the evaluation failure was caused by aborting when a
; warrant was needed.  This case is handled in rewrite, so we do not want to
; hide the term.  See the Essay on Evaluation of Apply$ and Loop$ Calls During
; Proofs.

                (mv nil (cons-term fn args) ttree))
               (t

; There is a guard violation, probably -- or perhaps there's some other kind of
; error.  We'll just hide this term so we don't see it again.

                (mv t
                    (hide-with-comment (cons :scons-term erp)
                                       (cons-term fn args)
                                       wrld state)
                    (push-lemma (fn-rune-nume 'hide nil nil wrld)
                                ttree)))))
             (t (mv t
                    (kwote val)
                    (push-lemma (fn-rune-nume fn nil t wrld)
                                ttree))))))))
   ((and (eq fn 'equal)
         (equal (car args) (cadr args)))
    (mv t *t* (puffert ttree)))
   (t (mv nil (cons-term fn args) ttree))))

(mutual-recursion

(defun subst-equiv-expr1 (equiv new old geneqv term ens wrld state ttree)

; This function substitutes new for old (which are known to be in the
; equivalence relation equiv) into term (maintaining the generated
; equivalence relation geneqv).  We assume that geneqv contains only
; enabled :CONGRUENCE rules.  We use only enabled :CONGRUENCE rules.
; We return three values: a flag indicating whether we changed term,
; the new term, and a ttree recording the :CONGRUENCE rules used.
; When we create new terms we run enabled fns on constant args.  The
; executable-counterparts used are reported in the ttree.

; (The (mv a b c) expressions below mean we are returning "multiple
; values", in this case, triples consisting of a, b, and c.
; Logically speaking (mv a b c) is just (list a b c), but ACL2's
; syntactic rules ensure that the list structure is never seen, i.e.,
; the three values are immediately plucked out of the structure.
; Analogously, in (mv-let (a b c) term1 term2) term1 evaluates to a
; triple, the three variables a, b, and c are bound to the three items
; of that triple, and then term2 is evaluated under those bindings.
; ACL2 uses mv and mv-let in place of Common Lisp's multiple value
; mechanism because the Common Lisp mechanism is too flexible.  It
; allows a function to return varying numbers of things.  Ours is also
; faster.)

; NOTE:  We ignore occurrences of old inside arguments to HIDE.

  (cond ((and (equal term old)
              (geneqv-refinementp equiv geneqv wrld))
         (mv t new
             (push-lemma (geneqv-refinementp equiv geneqv wrld) ttree)))
        ((or (variablep term)
             (fquotep term)
             (eq (ffn-symb term) 'hide))
         (mv nil term ttree))
        (t (mv-let (hitp1 args ttree)
                   (subst-equiv-expr1-lst equiv new old
                                          (geneqv-lst (ffn-symb term)
                                                      geneqv
                                                      ens
                                                      wrld)
                                          (fargs term)
                                          ens wrld state ttree)

; Note: Observe that we are relying on the IF hack in geneqv-lst here,
; asking that function to generate (iff geneqv geneqv) to control our
; calls.  If we thought this function would see a lot of action on
; IF's it would be better to special-case the substitution into IF
; expressions.

                   (mv-let (hitp2 new-term ttree)
                           (scons-term (ffn-symb term) args ens wrld state ttree)
                           (mv (or hitp1 hitp2)
                               new-term
                               ttree))))))

(defun subst-equiv-expr1-lst (equiv new old geneqv-lst args ens wrld state ttree)

; Here geneqv-lst is in 1:1 correspondence with args.  We substitute
; into each arg.

  (cond ((null args)
         (mv nil nil ttree))
        (t (mv-let (hitp1 arg ttree)
                   (subst-equiv-expr1 equiv new old
                                      (car geneqv-lst)
                                      (car args)
                                      ens wrld state ttree)
                   (mv-let (hitp2 args ttree)
                           (subst-equiv-expr1-lst equiv new old
                                                  (cdr geneqv-lst)
                                                  (cdr args)
                                                  ens wrld state ttree)
                           (mv (or hitp1 hitp2)
                               (cons arg args)
                               ttree))))))

)

(defun subst-equiv-expr (equiv new old geneqv term ens wrld state ttree)
  (cond ((and (nvariablep old)
              (fquotep old))
         (mv (subst-expr-error old) term ttree))
        (t (subst-equiv-expr1 equiv new old geneqv term ens wrld state ttree))))

; This completes the definition of congruence-based substitution.

; Next we develop support for patterned congruence rules.  See the Essay just
; below the following code for an extension of one-way unification.

(defconst *anonymous-var* '|Anonymous variable|)

(mutual-recursion

(defun equal-mod-alist (term1 alist1 term2)

; We determine whether (sublis-var alist1 term1) is equal to term2.
; We just chase vars in term1 and use equal at the tips.  There is
; one subtlety.  Consider

; (equal-mod-alist '(foo x z (cons x y))
;                  '((x . '1) (y . '2))
;                  '(foo '1 z '(1 . 2)))

; The idea is that if term2 is a quoted constant and term1 is some
; function application, then it is possible that the sublis-var will
; convert term1 to a quoted constant.  We know that only happens if
; the top-most function symbol in term1 is a primitive, so we check
; that and do the sublis-var if we have to.  But it only happens on
; the ``tips.''

  (cond ((variablep term1)
         (let ((temp (assoc-eq term1 alist1)))
           (cond (temp (equal (cdr temp) term2))
                 (t (equal term1 term2)))))
        ((fquotep term1)
         (equal term1 term2))
        ((variablep term2) nil)
        ((fquotep term2)
         (cond ((and (not (flambdap (ffn-symb term1)))
                     (assoc-eq (ffn-symb term1)
                               *primitive-formals-and-guards*))
                (equal term2 (sublis-var alist1 term1)))
               (t nil)))
        ((equal (ffn-symb term1) (ffn-symb term2)) ; may be lambdas.
         (equal-mod-alist-lst (fargs term1) alist1 (fargs term2)))
        (t nil)))

(defun equal-mod-alist-lst (term1-lst alist1 term2-lst)
  (cond
   ((endp term1-lst) t)
   (t (and (equal-mod-alist (car term1-lst) alist1 (car term2-lst))
           (equal-mod-alist-lst (cdr term1-lst) alist1 (cdr term2-lst))))))
)

(mutual-recursion

(defun equal-mod-alist2 (term1 alist1 term2 alist2)

; This function is similar to equal-mod-alist, except that term1 and term2 are
; both to be instantiated: we determine whether (sublis-var alist1 term1) is
; equal to (sublis-var alist2 term2).

  (cond ((variablep term1)
         (let ((pair1 (assoc-eq term1 alist1)))
           (cond (pair1 (equal-mod-alist term2 alist2 (cdr pair1)))
                 ((variablep term2)
                  (let ((pair2 (assoc-eq term2 alist2)))
                    (eq term1 (if pair2 (cdr pair2) term2))))
                 (t nil))))
        ((variablep term2)
         (let ((pair2 (assoc-eq term2 alist2)))
           (cond (pair2 (equal-mod-alist term1 alist1 (cdr pair2)))
                 (t nil))))
        ((fquotep term1)
         (equal-mod-alist term2 alist2 term1))
        ((fquotep term2)
         (equal-mod-alist term1 alist1 term2))
        ((equal (ffn-symb term1) (ffn-symb term2)) ; may be lambdas
         (equal-mod-alist2-lst (fargs term1) alist1 (fargs term2) alist2))
        (t nil)))

(defun equal-mod-alist2-lst (term1-lst alist1 term2-lst alist2)
  (cond
   ((endp term1-lst) t)
   (t (and (equal-mod-alist2 (car term1-lst) alist1
                             (car term2-lst) alist2)
           (equal-mod-alist2-lst (cdr term1-lst) alist1
                                 (cdr term2-lst) alist2)))))
)

(mutual-recursion

(defun one-way-unify1-term-alist (pat term term-alist alist)

; Warning; Keep this function in sync with one-way-unify1.

; This function returns (mv ans alist'), where alist' minimally extends alist
; such that pat/alist' = term/term-alist if such an extension exists, in which
; case ans is non-nil, and otherwise ans is nil.  This function differs from
; one-way-unify1 in the following two ways.  First, in the present function,
; alist may contain pairs of the form (v . (:sublis-var u . s)), where u is a
; term, meaning that v is bound to u/s.  (Term-alist, however, is an ordinary
; substitution, without such :sublis-var "calls".)  Second, term is interpreted
; as term/term-alist.

; We optimize by considering term instead of term/term-alist when term-alist is
; nil.  This is certainly sound, and it seems unlikely that it will cause
; problems since we expect that term is in quote-normal form.

; There is an additional difference between this function and one-way-unify1.
; In the present function, we treat every occurrence of *anonymous-var* as a
; distinct, uniquely occurring variable, not bound in the input alist or in the
; resulting alist.

; This function is a "No-Change Loser" meaning that if it fails and returns nil
; as its first result, it returns the unmodified alist as its second.

  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (alistp term-alist)
                              (alistp alist))))
  (cond ((eq pat *anonymous-var*)
         (mv t alist))
        ((variablep pat)
         (let ((pair (assoc-eq pat alist)))
           (cond ((null pair)
                  (mv t
                      (acons pat
                             (if term-alist
                                 (list* :sublis-var term term-alist)
                               term)
                             alist)))
                 ((and (consp pair)
                       (consp (cdr pair))
                       (eq (car (cdr pair)) :sublis-var))
                  (cond ((null term-alist) ; optimization
                         (mv (equal-mod-alist (cadr (cdr pair))
                                              (cddr (cdr pair))
                                              term)
                             alist))
                        (t (mv (equal-mod-alist2 (cadr (cdr pair))
                                                 (cddr (cdr pair))
                                                 term
                                                 term-alist)
                               alist))))
                 ((null term-alist) ; optimization
                  (mv (equal term (cdr pair))
                      alist))
                 (t
                  (mv (equal-mod-alist term term-alist (cdr pair))
                      alist)))))
        ((fquotep pat)
         (cond ((if (null term-alist) ; optimization
                    (equal term pat)
                  (equal-mod-alist term term-alist pat))
                (mv t alist))
               (t (mv nil alist))))
        ((variablep term)
         (let ((pair (assoc-eq term term-alist)))
           (cond (pair (one-way-unify1-term-alist pat (cdr pair) nil alist))
                 (t (mv nil alist)))))
        ((fquotep term) ; then term/term-alist = term; treat term-alist as nil
         (mv-let
          (pat1 term1 pat2 term2)
          (one-way-unify1-quotep-subproblems pat term)
          (cond ((eq pat1 t) (mv t alist))
                ((eq pat1 nil) (mv nil alist))
                ((eq pat2 nil)
                 (one-way-unify1-term-alist pat1 term1 nil alist))
                (t

; We are careful with alist to keep this a no change loser.

                 (mv-let
                  (ans alist1)
                  (one-way-unify1-term-alist pat1 term1 nil alist)
                  (cond ((eq ans nil) (mv nil alist))
                        (t (mv-let
                            (ans alist2)
                            (one-way-unify1-term-alist pat2 term2 nil alist1)
                            (cond (ans (mv ans alist2))
                                  (t (mv nil alist)))))))))))
        ((equal (ffn-symb pat) (ffn-symb term)) ; could be lambdas
         (mv-let
          (ans alist1)
          (one-way-unify1-term-alist-lst (fargs pat) (fargs term)
                                         term-alist alist)
          (cond
           (ans (mv ans alist1))
           ((eq (ffn-symb pat) 'equal)

; Try again, matching by commuting one of the equalities, in analogy to the
; second call of one-way-unify1-equal1 in one-way-unify1-equal.

            (let ((pat1 (fargn pat 1))
                  (pat2 (fargn pat 2))
                  (term1 (fargn term 1))
                  (term2 (fargn term 2)))
              (mv-let
               (ans alist1)
               (one-way-unify1-term-alist pat2 term1 term-alist alist)
               (cond
                (ans
                 (mv-let
                  (ans alist2)
                  (one-way-unify1-term-alist pat1 term2 term-alist alist1)
                  (cond (ans (mv ans alist2))
                        (t (mv nil alist)))))
                (t (mv nil alist))))))
           (t (mv nil alist)))))
        (t (mv nil alist))))

(defun one-way-unify1-term-alist-lst (pl tl term-alist alist)

; Warning: Keep this in sync with one-way-unify1-lst.  See
; one-way-unify1-term-alist.

; This function is NOT a No Change Loser.  That is, it may return nil
; as its first result, indicating that no substitution exists, but
; return as its second result an alist different from its input alist.

  (declare (xargs :guard (and (pseudo-term-listp pl)
                              (pseudo-term-listp tl)
                              (alistp term-alist)
                              (alistp alist))))
  (cond
   ((null pl) (mv t alist))
   (t
    (mv-let
     (ans alist)
     (one-way-unify1-term-alist (car pl) (car tl) term-alist alist)
     (cond
      (ans (one-way-unify1-term-alist-lst (cdr pl) (cdr tl) term-alist alist))
      (t (mv nil alist)))))))

)

; Essay on Patterned Congruences and Equivalences

; This Essay documents the addition of support for pattern-based congruence
; rules: congruence rules that are not based on the application of some
; function to distinct variables.  We assume familiarity both with the Essay on
; Equivalence, Refinements, and Congruence-based Rewriting and with the
; documentation topics for congruence and patterned-congruence.

; We begin with some initial observations that have guided our implementation.

; A key design principle is that the geneqv arguments to existing functions are
; essentially unchanged.  In particular, as rewrite recurs through
; rewrite-args, which recurs back through rewrite, geneqv is passed around much
; as it was before, but can be enhanced by using so-called patterned
; equivalences that are passed through these functions' arguments.  This
; approach has allowed us to continue to use some existing functions, in
; particular geneqv-lst.

; Another basic principle is that we deal with the inherently sequentiality of
; rewrite-args, in the sense that unlike ordinary geneqvs, the use of patterned
; equivalences must be done one argument at a time.  Consider the following
; example.

; (defun triv-equiv (x y)
;      (declare (ignore x y))
;      t)

; (defequiv triv-equiv)

; (defun some-consp (x y)
;   (or (consp x) (consp y)))

; (defthm triv-equiv-implies-equal-some-consp-1
;   (implies (triv-equiv x x-equiv)
;            (equal (some-consp x (cons a b))
;                   (some-consp x-equiv (cons a b))))
;   :rule-classes (:congruence))

; (defthm triv-equiv-implies-equal-some-consp-2
;   (implies (triv-equiv y y-equiv)
;            (equal (some-consp (cons a b) y)
;                   (some-consp (cons a b) y-equiv)))
;   :rule-classes (:congruence))

; (defthm cons-is-nil
;   (triv-equiv (cons x y) nil))

; Now consider the following purported "theorem".

; (thm (equal (some-consp (cons c1 c2) (cons d1 d2))
;             (some-consp nil nil)))

; Each of the two above congruence rules applies to one of the arguments of the
; first call of some-consp in the formula just above.  One might thus expect to
; be able to apply the rule cons-is-nil to each of these arguments, reducing
; the first call above of some-consp to the second call, thus proving the
; formula.  But the formula is clearly not provable; in fact, the first call of
; some-consp is true but the second is false, by definition of some-consp!  We
; therefore must take care not to propagate such congruences independently in
; the arguments of a function call, unlike for example what we do with the
; function geneqv-lst.

; Consider the following new-style congruence rule.

; (implies (inner-equiv y1 y2)
;          (outer-equiv (mv-nth 1 (foo x (g y1) z))
;                       (mv-nth 1 (foo x (g y2) z))))

; We imagine that there may be many such rules about mv-nth, so we index such
; rules not by the outer function symbol (here, mv-nth), but by the next
; function symbol down towards the designated variable (here, foo).  The
; rewriter will consider this rule after it has already dived into a call of
; foo; so the rewriter passes information about the parent call of mv-nth.  Now
; suppose we are rewriting the term (mv-nth 1 (foo a (h b1) c)), and assume
; that some rewrite rule equates (h b1) with (g b1).  As we rewrite inside-out,
; we pick up the congruence rule when we reach the call (foo a (h b1) c).  We
; might be tempted to have the rewriter ignore this congruence rule when
; passing to the term (h b1), but that would be a mistake: at that point, (h
; b1) rewrites to (g b1), and the rewriter is then called recursively.  We want
; this recursive call to notice the congruence rule, so that it will be
; sufficient to preserve inner-equiv when making that recursive call on (g b1).
; Thus, we introduce a notion of a "next" operation that is invoked when
; passing from the call of foo to the call of h, and we do not discard "next"
; data based on a mere failure to match the current call, which here is (h b1).

; This concludes initial observations that have guided our implementation.

; We assume familiarity with the concepts described in the Essay on
; Equivalence, Refinements, and Congruence-based Rewriting, but we begin with a
; brief review.  That Essay describes the notion of rewriting with respect to a
; generated equivalence relation, or geneqv: a list of congruence-rule
; structures that denotes the transitive closure of the union of the
; equivalence relations represented by the :equiv fields of those congruence
; rules.  When ACL2 rewrites a function call with respect to a geneqv, it
; rewrites each argument of that function call with respect to a geneqv derived
; by applying congruence rules to the original geneqv.  A congruence rule has
; the following form, where fn is a function symbol and its two calls are made
; on the same sequence of distinct variables, except that x and y occur
; uniquely in corresponding positions as shown.

; (implies (equiv1 x y)
;          (equiv2 (fn a1 ... x ... an)
;                  (fn a1 ... y ... an))),

; Let us call these rules "classic" congruence rules.  We will refer to equiv1
; as the "inner equivalence", equiv2 as the "outer equivalence", fn as the
; "function symbol", x as the "variable", y as the "replacement variable", and
; the first and second arguments of the above call of equiv2 as the "lhs" and
; "rhs" of the rule, respectively.  In such a case, where x is the kth argument
; of fn in the lhs of the rule, we say that it "suffices to maintain equiv1 at
; the kth argument of a call of fn in order to maintain equiv2".  This notion
; does not depend on a specific congruence rule; that is, it makes sense for
; any pair equiv1 and equiv2 of equivalence relations, any function symbol fn,
; and any positive k not exceeding the arity of fn.

; In this Essay we discuss a generalization of the above notion of congruence
; rules in which the notions of variable, replacement variable, lhs, and rhs
; still apply: congruence rules still have the following form, where lhs and
; rhs are calls of the same function symbol.

; (implies (equiv1 x y)
;          (equiv2 lhs rhs)),

; As before, lhs and rhs must be the same with the exception that the variable
; and replacement variable occur uniquely in the rule and, moreover, at the
; same address (same position) in lhs and rhs, respectively.  But we relax the
; other requirements on the arguments of lhs (and hence rhs): they need not be
; variables, and duplicates are permissible.  The following are examples of
; congruence rules that are not classic, since each lhs has non-variable
; arguments.  (As of this writing, these and other examples may be found in
; community book demos/patterned-congruences.lisp.)  In each case the variable
; is y1 and the replacement variable is y2.

; Inner equivalence e1, outer equivalence iff:

;    (implies (e1 y1 y2)
;             (iff (f1 3 y1 (cons x x))
;                  (f1 3 y2 (cons x x))))

; Inner equivalence e4, outer equivalence equal:

;    (implies (e4 y1 y2)
;             (equal (mv-nth 1 (id (f7 y1)))
;                    (mv-nth 1 (id (f7 y2)))))

; The first of these two rules is called "shallow" because y1 and y2 occur as
; top-level arguments of the lhs and rhs of the rule (respectively), just as
; they do in the classic congruence rule previously displayed above.  The
; second of these rules is not of that form because y1 and y2 occur inside a
; subsidiary function call; the second rule is thus not shallow, so we call it
; "deep".  Both are what we call "patterned congruence rules".  Thus, the class
; of congruence rules is partitioned into the classes of classic and patterned
; congruence rules, and the patterned congruence rules are partitioned into the
; subclasses of shallow and deep congruence rules.

; A shallow or deep patterned congruence rule generates what we call a (shallow
; or deep, respectively) "patterned equivalence relation", or pequiv.

(defrec pequiv
  (pattern     ; a pequiv-pattern record
   unify-subst ; a (unifying) substitution
   .
   congruence-rule ; a congruence-rule record
   )
  t)

; The :unify-subst field is nil for the pequiv generated by a patterned
; congruence rule, but need not be nil in general; we describe its role when we
; give the semantics of pequiv records later below.  The :congruence-rule field
; is the congruence-rule record corresponding to the patterned congruence rule
; from which this pequiv is derived.  Finally, we describe the :pattern field,
; which represents the lhs of a patterned congruence rule.  This field is
; actually a pequiv-pattern record (defined below), which represents a term,
; specifically a function call, along with a variable that occurs uniquely
; within the term.  Function make-pequiv-pattern creates a pattern from the
; term and (the address of the) variable, informally as follows.  The :fn of
; the pattern is the function symbol of the term.  The :posn is the one-based
; position within the arguments of the term under which the variable (uniquely)
; occurs.  The :pre-rev field is the reverse of the list of arguments strictly
; before that position, while the :post field is the list of arguments strictly
; after that position.  Finally, the :next field is either a variable
; (corresponding to the variable of the patterned congruence rule) or else is,
; recursively, the pattern representing the argument at :posn (along with the
; same variable).

(defrec pequiv-pattern ; see description just above
  (fn posn pre-rev post next)
  t)

; The discussion above is perhaps a bit misleading because of the following
; optimization.  Our algorithm attempts to extend a unifying substitution by
; matching the :pre-rev and :post fields with a term.  But we do not need to
; record matching of a variable that will not be encountered further.
; Therefore, before creating the pattern from the term, we replace each
; uniquely-occurring variable in the term by a the variable, *anonymous-var*.
; In order to justify this transformation, we first check that *anonymous-var*
; does not occur anywhere in the term.  (Perhaps it is sufficient that
; *anonymous-var* does not occur in the arguments of lhs other than the
; variable of the rule, but the stronger check avoids the need to think through
; whether that is truly sufficient.)  Then, we use a matching algorithm that
; always succeeds when matching *anonymous-var*, but never binds
; *anonymous-var* in the unifying substitution.  This optimization thus saves
; some consing.  In the rest of this discussion we will ignore the above
; optimization when we believe this will not lead to confusion.

; We will freely abuse terminology when we expect no confusion to result.  For
; example, we may confuse a patterned congruence rule with its corresponding
; pequiv, and we may confuse a term with its corresponding pattern.  Thus, we
; may speak of the "term" of a pequiv to denote the term corresponding to its
; :pattern field; similarly, the "variable" of a pequiv is just the variable of
; the corresponding patterned congruence rule.  (One could expect to reach that
; variable by following the :next field of the :pattern of the pequiv until
; :next is a variable, except of course that the variable will have been
; replaced by the anonymous variable described above.)

; A pequiv record denotes the following equivalence relation, which we may
; refer to as the corresponding "patterned equivalence".  For this discussion
; we assume a global binding of variables to values; intuitively, when you
; submit a formula to ACL2 to prove, the variables in the formula represent
; values provided by an arbitrary such binding.  Recall the notion of an
; equivalence relation generated by a binary relation, namely, the
; equivalential (reflexive, symmetric, transitive) closure of that binary
; relation.  The patterned equivalence relation denoted by a pequiv is the
; equivalential closure of the following binary relation.  Let t0 be the term
; of the pequiv.  Two values v1 and v2 are related if for some substitution s
; that extends the :unify-subst of the pequiv and for variants s1 and s2 of s
; obtained by rebinding only the variable of the pequiv, then v1 = t0/s1 and v2
; = t0/s2.

; Let p be a pequiv, fn be a function symbol, and first-rev and rest be term
; lists.  We next define the notion of the "next equiv" for a pequiv, p, with
; respect to fn, first-rev, and rest.  Let pat be the :pattern field of p.
; This next equiv is either undefined or is obtained from p as described below.
; Let k, pre-rev, post, and next be the :pre-rev, :post, and :next fields of
; pat, respectively.  The next equiv is undefined unless, at a minimum: fn is
; equal to the :fn field of pat, first-rev has the same length as the :pre-rev
; field of pat, and rest has the same length as the :post field of pat.  So
; assume that these conditions hold.  Let s0 be the :unify-subst field of p,
; and let s be the minimal extension of s0 such that pre-rev/s = first-rev and
; post/s = rest, if such s exists; otherwise the next equiv does not exist.  If
; p is a deep pequiv, then the next equiv is the result of replacing the
; :unify-subst of p by s and replacing the :pattern of p by next.  If p is a
; shallow equiv, then the next equiv for p is the equivalence relation of the
; :congruence-rule of p.  Note: If we refer to the next equiv for p and u,
; where u is a term, we are really referring to the next equiv for p with
; respect to fn, first-rev and rest, where u is of the form (cons fn (revappend
; first-rev (cons arg rest))) for some arg and the length of first-rev is the
; value of the :posn field of the :pattern field of p.

; The correctness of our implementation relies on the theorems below, whose
; proofs we leave to the reader.  The first theorem justifies the addition of a
; pequiv to the list of equivalence relations being maintained by the rewriter,
; while the second justifies how a pequiv is used when rewriting an argument of
; a function call.

; Patterned Congruence Theorem 1.  Let E be the pequiv corresponding to a
; provable patterned congruence rule with outer equivalence e2.  Then for terms
; t1 and t2, (implies (E t1 t2) (e2 t1 t2)) is provable.

; Patterned Congruence Theorem 2.  Let p be a pequiv, let u be a term, and
; assume that the next equiv for p and u exists; call it n.  Let arg be the kth
; argument of u, where k is the :posn field of the :pattern field of u, let
; arg' be a term, and let u' be the result of replacing the kth argument of u
; by arg'.  Then (implies (n arg arg') (p u u')).

; A final data structure for supporting patterned congruence rules is the
; pequiv-info record.  The rewrite clique takes a pequiv-info formal parameter
; that is either nil or such a record.

(defrec pequiv-info

; Each function in the rewrite clique has a pequiv-info argument that either is
; nil or is one of these records.  In the latter case, that argument represents
; information from a parent call of rewrite on a function call, where one
; argument of the call is the "current term" being processed, and other
; "sibling arguments" of the call are stored as indicated below.

  (((rewritten-args-rev ; reverse of (rewritten) preceding sibling arguments
     .
     rest-args) ; later sibling arguments, not yet rewritten
    .
    (alist ; alist under which the current term and rest-args are rewritten
     .
     bkptr)) ; one-based position of the current term
   .
   (geneqv ; geneqv of the parent call of rewrite
    fn ; function symbol of the term rewritten by the parent call of rewrite
    .

; Finally, deep-pequiv-lst is a list of (deep) pequivs from the parent call of
; rewrite, each of which has an enabled :congruence-rule field.

    deep-pequiv-lst))
  t)

; When rewrite is called with a pequiv-info argument of nil, its spec is
; unchanged from what it was before the introduction of patterned congruences:
; the term returned by (rewrite term alist ... geneqv ...) is provably in
; relation geneqv to term/alist.  Of course, "provably" should be understood
; relative to the assumptions implicit in the other arguments of rewrite: the
; type-alist, world, and pot-list.

; Subtle Logical Aside.  More subtly, terms u1 and u2 can be understood as
; being "provably in relation geneqv" if there is a sequence of terms t0, ...,
; tk such that t0 = u1, tk = u2, and for each i < k and where j = i+1, there is
; some equivalence relation E in geneqv such that (E ti tj) is provable (again,
; with respect to the implicit assumptions).  We may wish to take this view of
; "provably in relation geneqv" because the geneqv relation is defined in terms
; of a transitive closure, which is not a first-order notion.  In the case of
; ACL2 we could actually provide a first-order definition of geneqv by using
; sequences: it is first-order to state that there is a finite sequence of
; values such that each is in relation E to the next for some E in geneqv.
; Either of these two notions of "provably in relation geneqv" is in fact
; adequate; choose your favorite!  End of Subtle Logical Aside.

; We turn now to modifying the above spec for the case of (rewrite term alist
; bkptr ... geneqv pequiv-info ...), where pequiv-info is a pequiv-info record
; with fields rewritten-args-rev, rest-args, alist, bkptr, parent-geneqv,
; parent-fn, and deep-pequiv-lst, and obvious assumptions are left implicit (in
; particular, bkptr is the length of rewritten-args-rev).  Generate an
; equivalence relation E by extending geneqv by each of the following, as p
; ranges over members of deep-pequiv-lst: the next-equiv for p with respect to
; parent-fn, rewritten-args-rev, and rest-args/alist.  Then the output from the
; above call of rewrite is provably in relation E to term.  (Note: in our
; implementation, p also ranges over some pequivs that provably refine a member
; of parent-geneqv; but we can include these, by the theorems above.)  We
; discuss later how to prove this spec, after summarizing how pequivs are
; processed by the rewriter.

; In order to minimize property list accesses, we store deep and shallow
; equivalences in a single structure, as follows.

(defrec pequivs-property
  (deep shallow . deep-pequiv-p)
  t)

; The :deep and :shallow fields are alists whose elements have the form (equiv
; pequiv1 pequiv2 ... pequivn), where each pequivk is a patterned equivalence
; that refines equiv.  When such a record is the value of the 'pequivs property
; of a function symbol, fn, then fn is the :fn field of the :pattern field of
; each such pequivk in the case of the :shallow field; but in the case of the
; :deep field, each such pequivk is a deep pequiv, and fn is the :fn field of
; the :next field of the :pattern field.  In brief, consider a patterned
; congruence rule with function symbol fn together with outer equivalence e and
; corresponding pequiv, p.  If the rule (and hence also p) is shallow, then we
; will find p in the :shallow field of the 'pequivs property of fn, which is an
; alist with an element (e ... p ...).  Otherwise the rule (and hence also p)
; is deep, with lhs of the form (fn ... (fn2 ...) ...) such that the variable
; of the rule occurs in the displayed call of fn2.  In that case, we will find
; p in the :deep field of the 'pequivs property of fn2, which is an alist with
; an element (e ... p ...).

; Algorithm discussion.  Next, we describe how rewrite passes pequiv
; information to rewrite-args and how rewrite-args passes pequiv information to
; rewrite.

; Rewrite computes a list of deep-pequivs and a list of shallow-pequivs to pass
; to rewrite-args using function pequivs-for-rewrite-args, where the input term
; is a call of function symbol fn, a symbol (not a lambda).  In (a) and (b)
; below, we compute the next pequiv with respect to the following function
; symbol, first-rev, and rest: the function symbol is fn; first-rev is the
; :rewritten-args-rev field of pequiv-info; and for rest, we take the
; :rest-args field of pequiv-info and instantiate it with the :alist field of
; pequiv-info.  Note that the pequiv-info argument is guaranteed not to be nil
; if there are any pequivs in (a) or (b) for which to take the next equiv.

; (a) Derive the list of next equivs from the :deep-pequiv-lst field of the
;     pequiv-info argument, restricting to those (deep) pequivs whose :next
;     field has :fn field equal to fn.  Sort these into a list of deep pequivs
;     and a list of shallow pequivs.

; (b) Derive the list of next equivs from deep pequivs stored in the 'pequivs
;     property of fn, restricting to those that are stored under an outer equiv
;     that is enabled and refines the geneqv of pequiv-info.  Sort these into a
;     list of deep pequivs and a list of shallow pequivs.

; (c) Compute additional shallow pequivs from the shallow pequivs stored in the
;     'pequivs property of fn, restricting to those that are stored under an
;     outer equiv that is enabled and refines the geneqv argument of (the
;     present call of) rewrite.

; Note that rewrite is not passed any shallow pequivs.  Rather, rewrite derives
; shallow-pequivs as described above and passes these to rewrite-args, which
; uses them to augment the geneqv passed to the child call of rewrite.  That
; augmentation is done by geneqv-and-pequiv-info-for-rewrite, which is called
; by rewrite-args in preparation for its call of rewrite; we describe this
; next.

; Now consider a call (rewrite-args args alist bkptr rewritten-args-rev
; deep-pequiv-lst shallow-pequiv-lst parent-geneqv parent-fn ... geneqv-lst
; ...).  These arguments are used by function
; geneqv-and-pequiv-info-for-rewrite to produce the geneqv and pequiv-info
; arguments for its "child call" of rewrite.  That child call's geneqv is
; constructed initially from the geneqv-lst passed to rewrite-args, but is
; extended (by function geneqv-for-rewrite) using the next equiv for each
; member of shallow-pequiv-lst with respect to parent-fn, rewritten-args-rev,
; and (cdr args).  In doing this, we maintain the invariant that a geneqv does
; not contain two equivs such that one refines the other.  The pequiv-info
; record for the child call of rewrite is constructed by function
; pequiv-info-for-rewrite, with fields taken unchanged from the inputs of
; rewrite-args, in particular without taking the "next" for the pequivs.
; Except, nil may be returned for pequiv-info when a pequiv-info record is not
; needed by rewrite, in order to save consing; see pequiv-info-for-rewrite.

; We will briefly sketch the proof by computational induction that the ACL2
; rewriter satisfies the spec given above for rewrite.  The interesting
; induction steps are for calling rewrite on a first argument that is a
; function call when the pequiv-info argument is not nil, and for calling
; rewrite-args on a non-empty first parameter, args.  Our spec for rewrite is
; above, and although a detailed proof would also involve a spec for each
; function in the rewrite clique, for this sketch we give an additional spec
; only for rewrite-args.  (Then we will sketch the proof.)

; Consider a call (rewrite-args args alist bkptr rewritten-args-rev
; deep-pequiv-lst shallow-pequiv-lst parent-geneqv parent-fn ... geneqv-lst
; ...), which results in a term list args', and define the "input term" and
; "output term" to be, respectively, (cons parent-fn (revappend
; rewritten-args-rev args/alist)) and (cons parent-fn args').  Assume that
; geneqv-lst is a list of generated equivalence relations that corresponds
; positionally to args, such that for each element g of this list and
; corresponding position k in the argument list of parent-fn, it suffices to
; preserve g at the kth argument of parent-fn in order to preserve
; parent-geneqv.  Then the input and output terms are provably equivalent with
; respect to the equivalence relation generated by parent-geneqv,
; deep-pequiv-lst, and shallow-pequiv-lst.

; Turning now to the proof sketch, first consider the induction step for
; (rewrite-args (cons arg rest-args) alist bkptr rewritten-args-rev
; deep-pequiv-lst shallow-pequiv-lst parent-geneqv parent-fn ... (cons geneqv
; geneqv-lst) ...).  This call is equal to the call (rewrite-args rest-args
; alist (1+ bkptr) (cons rewritten-arg rewritten-args-rev) deep-pequiv-lst
; shallow-pequiv-lst parent-geneqv parent-fn ... geneqv-lst), where
; rewritten-arg is produced by rewrite using the geneqv and pequiv-info
; returned by the call that rewrite-args makes of
; geneqv-and-pequiv-info-for-rewrite.  It suffices by the inductive hypothesis
; to show that arg/alist and rewritten-arg are provably in the equivalence
; relation generated by parent-geneqv, deep-pequiv-lst, and shallow-pequiv-lst.
; But this follows from Patterned Congruence Theorem 2, since by hypothesis
; geneqv is sufficient for preserving parent-geneqv, and because the spec for
; rewrite is with respect to the next equivs for deep-pequiv-lst and
; shallow-pequiv-lst.

; Now consider the induction step for (rewrite term alist ... pequiv-info ...).
; Now pequivs-for-rewrite-args sets up a call of rewrite-args with next equivs
; generated from pequiv-info (if non-nil) as in (a) and (b) above, and with new
; pequivs as in (c) above.  These next equivs are justified by Patterned
; Congruence Theorems 1 and 2.  By the inductive hypothesis, that call of
; rewrite-args returns a term that is suitably equivalent to term/alist.  Then
; the inductive hypothesis takes care of any ensuing call of rewrite, say from
; rewrite-if or from the right-hand side of an applied rewrite rule.

; We conclude this essay by emphasizing that our support for patterned
; congruence rules is limited; in particular, it is mainly for the rewriter.
; Thus, pequivs fail to be used heuristically in some places that ordinary
; congruences are used: for example, as in test-3 in community book
; books/demos/patterned-congruences.lisp, remove-trivial-equivalences and
; fertilize-clause doesn't use patterned congruence rules.  If we decide to add
; such support, then we should think carefully so that we don't introduce
; unsoundness.  See the examples in the above book involving congruence rules
; triv-equiv-implies-equal-some-consp-1 and
; triv-equiv-implies-equal-some-consp-2; while we don't have similar examples
; at hand to illustrate the danger of careless substitution with
; remove-trivial-equivalences and fertilize-clause, we can imagine that such
; dangers exist.  Finally support for pequivs is provided in the function
; geneqv-at-subterm-top, used in the proof-builder, but is not provided in the
; code the warns about missing opportunities for the use of double-rewrite
; (e.g., double-rewrite-opportunities).

; End of Essay on Patterned Congruences and Equivalences

(defconst *empty-pequivs-property*
  (make pequivs-property
        :deep nil
        :shallow nil
        :deep-pequiv-p nil))

(defmacro pequivs-property-field (prop field)

; We currently store nil as the 'pequivs property of a newly defined function
; (see defuns-fn1 and intro-udf), which accounts for the test below that prop
; is non-nil.  We could instead store *empty-pequivs-property* initially, in
; which case we could eliminate this macro and just use access directly.

  (declare (xargs :guard (and (member-eq field
                                         '(:deep :shallow :deep-pequiv-p))
                              (not (keywordp prop))))) ; avoid capture
  `(let ((prop ,prop))
     (and prop
          (access pequivs-property prop ,field))))

(defun next-pequiv (pequiv rewritten-args-rev rest-args alist)

; We return the next equiv for the given deep pequiv with respect to an
; implicit function symbol (already checked by the caller) together with
; rewritten-args-rev and rest-args/alist.  See the Essay on Patterned
; Congruences and Equivalences.

  (let ((pattern (access pequiv pequiv :pattern)))
    (mv-let
     (flg unify-subst)
     (one-way-unify1-term-alist-lst (access pequiv-pattern pattern :pre-rev)
                                    rewritten-args-rev
                                    nil
                                    (access pequiv pequiv :unify-subst))
     (cond ((null flg) nil)
           (t (mv-let
               (flg unify-subst)
               (one-way-unify1-term-alist-lst (access pequiv-pattern pattern
                                                      :post)
                                              rest-args alist unify-subst)
               (cond ((null flg) nil)
                     ((equal (access pequiv pequiv :unify-subst)
                             unify-subst) ; to avoid consing
                      (change pequiv pequiv
                              :pattern
                              (access pequiv-pattern pattern :next)))
                     (t (change pequiv pequiv
                                :pattern
                                (access pequiv-pattern pattern :next)
                                :unify-subst
                                unify-subst)))))))))

(defun next-pequivs (deep-pequiv-lst rewritten-args-rev rest-args alist bkptr
                                     parent-fn child-fn ens
                                     next-deep-pequiv-lst
                                     next-shallow-pequiv-lst)

; We return next equivs for (deep) pequivs in deep-pequiv-lst, as described
; below.  See the Essay on Patterned Congruences and Equivalences.

; This function is really a combination of two functions.  In one case, we
; expect all congruences within deep-pequiv-lst to be enabled; then child-fn is
; required to be the function symbol of the child and ens is irrelevant.  In
; the other case, we expect all pequivs in deep-pequiv-lst to have :next
; patterns whose :fn is the child function, so we pass in child-fn = nil but we
; also pass in ens as an enabled structure, in order to filter deep-pequiv-lst
; by enabled congruences.

  (cond
   ((endp deep-pequiv-lst)
    (mv next-deep-pequiv-lst next-shallow-pequiv-lst))
   (t (let* ((deep-pequiv (car deep-pequiv-lst))
             (pat (access pequiv deep-pequiv :pattern))
             (next (access pequiv-pattern pat :next))
             (next-pequiv
              (assert$
               (not (variablep next)) ; deep-equiv is deep
               (and (eq parent-fn (access pequiv-pattern pat :fn))
                    (eql bkptr (access pequiv-pattern pat :posn))
                    (if child-fn
                        (eq child-fn (access pequiv-pattern next :fn))
                      (enabled-numep
                       (access congruence-rule
                               (access pequiv deep-pequiv :congruence-rule)
                               :nume)
                       ens))
                    (next-pequiv deep-pequiv rewritten-args-rev rest-args
                                 alist)))))
        (cond
         ((not next-pequiv)
          (next-pequivs (cdr deep-pequiv-lst) rewritten-args-rev rest-args
                        alist bkptr parent-fn child-fn ens
                        next-deep-pequiv-lst next-shallow-pequiv-lst))
         ((variablep (access pequiv-pattern next :next)) ; next is shallow
          (next-pequivs
           (cdr deep-pequiv-lst) rewritten-args-rev rest-args alist
           bkptr parent-fn child-fn ens
           next-deep-pequiv-lst
           (cons next-pequiv next-shallow-pequiv-lst)))
         (t ; next is deep
          (next-pequivs
           (cdr deep-pequiv-lst) rewritten-args-rev rest-args alist
           bkptr parent-fn child-fn ens
           (cons next-pequiv next-deep-pequiv-lst)
           next-shallow-pequiv-lst)))))))

(defun next-pequivs-alist (deep-pequiv-alist rewritten-args-rev rest-args
                                             alist bkptr parent-fn
                                             parent-geneqv wrld ens
                                             next-deep-pequiv-lst
                                             next-shallow-pequiv-lst)

; Deep-pequiv-alist is a list of entries of the form (equiv pequiv1
; ... pequivk).  For each such entry for which equiv refines parent-geneqv, and
; then for each pequivi -- which is a deep pequiv -- whose congruence-rule is
; enabled, accumulate into next-deep-pequiv-lst and next-shallow-pequiv-lst the
; next equiv with respect to parent-fn, rewritten-args-rev, and
; rest-args/alist.  See the Essay on Patterned Congruences and Equivalences.

  (cond ((endp deep-pequiv-alist)
         (mv next-deep-pequiv-lst next-shallow-pequiv-lst))
        ((geneqv-refinementp (caar deep-pequiv-alist) parent-geneqv wrld)
         (mv-let (next-deep-pequiv-lst next-shallow-pequiv-lst)
                 (next-pequivs (cdar deep-pequiv-alist)
                               rewritten-args-rev rest-args alist bkptr
                               parent-fn
                               nil ; child-fn
                               ens
                               next-deep-pequiv-lst next-shallow-pequiv-lst)
                 (next-pequivs-alist (cdr deep-pequiv-alist)
                                     rewritten-args-rev rest-args
                                     alist bkptr parent-fn
                                     parent-geneqv wrld ens
                                     next-deep-pequiv-lst
                                     next-shallow-pequiv-lst)))
        (t (next-pequivs-alist (cdr deep-pequiv-alist)
                               rewritten-args-rev rest-args
                               alist bkptr parent-fn
                               parent-geneqv wrld ens
                               next-deep-pequiv-lst
                               next-shallow-pequiv-lst))))

(defun extend-pequiv-lst (pequiv-lst ens acc)
  (cond ((endp pequiv-lst) acc)
        (t (extend-pequiv-lst
            (cdr pequiv-lst)
            ens
            (cond ((enabled-numep (access congruence-rule
                                          (access pequiv (car pequiv-lst)
                                                  :congruence-rule)
                                          :nume)
                                  ens)
                   (cons (car pequiv-lst) acc))
                  (t acc))))))

(defun accumulate-shallow-pequiv-alist (alist geneqv wrld ens acc)

; Alist associates each of its keys, an equivalence relation, with a list of
; shallow pequivs.  We accumulate those pequivs into acc for which the key
; refines geneqv and the congruence-rule is enabled.

  (cond ((endp alist) acc)
        (t (accumulate-shallow-pequiv-alist
            (cdr alist) geneqv wrld ens
            (cond ((geneqv-refinementp (caar alist) geneqv wrld)
                   (extend-pequiv-lst (cdar alist) ens acc))
                  (t acc))))))

(defun pequivs-for-rewrite-args (fn geneqv pequiv-info wrld ens)

; See the Essay on Patterned Congruences and Equivalences, in particular the
; discussion of computations of a list of deep-pequivs and a list of
; shallow-pequivs to pass to rewrite-args shown there as (a), (b), and (c).

; Consider a call of rewrite whose term argument, u, has input fn as its
; function symbol, whose rcnst argument has input ens as its enabled structure,
; and whose geneqv, pequiv-info, and wrld arguments are corresponding inputs of
; the present function.  We return two values, next-deep-pequiv-lst and
; next-shallow-pequiv-lst, which are suitable for the ensuing call of
; rewrite-args on the arguments of u.  These are lists of deep and of shallow
; pequivs, respectively, except that next-deep-pequiv-lst can take the special
; value of :none, which represents the empty list but indicates that the
; :deep-pequiv-p field is true for the 'pequivs property of fn, indicating that
; some deep pequiv has a :pattern whose :fn is fn.

  (cond
   ((flambdap fn) ; no chance of a match by child rewrite call
    (mv nil nil))
   (t (let* ((prop (getpropc fn 'pequivs nil wrld))
             (shallow-pequiv-alist (pequivs-property-field prop :shallow)))
        (cond
         ((not pequiv-info) ; no pequivs for which to take the "next"
          (mv (and (pequivs-property-field prop :deep-pequiv-p)
                   :none)
              (accumulate-shallow-pequiv-alist ; (c)
               shallow-pequiv-alist geneqv wrld ens nil)))
         (t
          (let ((deep-pequiv-lst (access pequiv-info pequiv-info
                                         :deep-pequiv-lst))
                (rewritten-args-rev (access pequiv-info pequiv-info
                                            :rewritten-args-rev))
                (rest-args (access pequiv-info pequiv-info
                                   :rest-args))
                (alist (access pequiv-info pequiv-info
                               :alist))
                (bkptr (access pequiv-info pequiv-info
                               :bkptr))
                (parent-fn (access pequiv-info pequiv-info
                                   :fn)))
            (mv-let
             (next-deep-pequiv-lst next-shallow-pequiv-lst) ; (a)
             (next-pequivs deep-pequiv-lst rewritten-args-rev rest-args alist
                           bkptr parent-fn fn
                           nil ; or ens -- irrelevant argument
                           nil nil)
             (mv-let
              (next-deep-pequiv-lst next-shallow-pequiv-lst) ; (b)
              (next-pequivs-alist (pequivs-property-field prop :deep)
                                  rewritten-args-rev rest-args alist bkptr
                                  parent-fn
                                  (access pequiv-info pequiv-info :geneqv)
                                  wrld ens
                                  next-deep-pequiv-lst next-shallow-pequiv-lst)
              (mv (or next-deep-pequiv-lst
                      (and (pequivs-property-field prop :deep-pequiv-p)
                           :none))
                  (accumulate-shallow-pequiv-alist ; (c)
                   shallow-pequiv-alist
                   geneqv wrld ens next-shallow-pequiv-lst)))))))))))

(defun pequiv-info-for-rewrite (fn bkptr rewritten-args-rev args alist geneqv
                                   deep-pequiv-lst)

; See the Essay on Patterned Congruences and Equivalences.

  (cond ((or (null deep-pequiv-lst) ; common case (note: nil, not :none)
             (flambdap fn)
             (variablep (car args))
             (fquotep (car args)))

; In this case we return nil in order to avoid consing, as the ensuing child
; call of rewrite from rewrite-args will not need a pequiv-info record.  Why
; won't such a record be needed?

; If the term passed to the parent call of rewrite is a lambda application --
; that is, fn is a lambda -- then no matching will take place, as we do not
; allow lambdas in patterned congruence rules (see the call of
; lambda-subtermp-lst in interpret-term-as-congruence-rule); so the child
; rewrite call will not need pequiv-info.  If the term passed to the child call
; of rewrite is a variable or a quotep, then we don't expect a recursive call
; of rewrite and hence we don't expect an ensuing call of rewrite-args, so
; again we won't need pequiv-info.  Otherwise, it suffices that deep-pequiv-lst
; be nil, as we can see by considering the two potential sources of next equivs
; whose computation would require pequiv-info -- conditions (a) and (b) from
; the Essay on Patterned Congruences and Equivalences.  One source (from (a))
; is the :deep-pequiv-lst field of pequiv-info, which will be empty if the
; deep-pequivs argument of rewrite-args is empty.  The other source (from (b))
; is the deep pequivs stored in the 'pequivs property of fn (so, fn is a
; function symbol in this case, not a lambda).  But if there are any such deep
; pequivs, then deep-pequiv-lst is either a non-empty list or :none (as
; computed by pequivs-for-rewrite-args), not nil.

         nil)
        (t (make pequiv-info
                 :rewritten-args-rev rewritten-args-rev
                 :rest-args (cdr args)
                 :alist alist
                 :bkptr bkptr
                 :fn fn
                 :geneqv geneqv
                 :deep-pequiv-lst
                 (and (consp deep-pequiv-lst) ; rule out :none
                      deep-pequiv-lst)))))

(defun reduce-geneqv-for-equiv (equiv wrld geneqv)

; We will be adding equiv to geneqv.  Here, in preparation for that addition,
; return the result of deleting every refinement of equiv from geneqv.

  (cond ((endp geneqv) (mv nil nil))
        (t (mv-let
            (changedp rest)
            (reduce-geneqv-for-equiv equiv wrld (cdr geneqv))
            (cond
             ((refinementp (access congruence-rule (car geneqv) :equiv)
                           equiv
                           wrld)
              (mv t rest))
             (changedp
              (mv t (cons (car geneqv) rest)))
             (t (mv nil geneqv)))))))

(defun geneqv-for-rewrite (shallow-pequiv-lst fn bkptr rewritten-args-rev
                                              rest-args alist wrld geneqv)

; See the Essay on Patterned Congruences and Equivalences.  Here we return the
; result of extending geneqv using every non-nil next equiv for each (shallow)
; pequiv in shallow-pequiv-lst, with respect to fn, rewritten-args-rev, and
; rest-args/alist.  This function assumes that every congruence rule of
; shallow-pequiv-lst is enabled.

  (cond
   ((null shallow-pequiv-lst) geneqv)
   (t (let* ((pequiv (car shallow-pequiv-lst))
             (pat (access pequiv pequiv :pattern))
             (congruence-rule (access pequiv pequiv :congruence-rule))
             (equiv (access congruence-rule congruence-rule :equiv)))
        (geneqv-for-rewrite
         (cdr shallow-pequiv-lst)
         fn bkptr rewritten-args-rev rest-args alist wrld
         (cond
          ((or (not (eq fn (access pequiv-pattern pat :fn)))
               (not (eql bkptr (access pequiv-pattern pat :posn)))
               (geneqv-refinementp equiv geneqv wrld))
           geneqv)
          (t (mv-let
              (flg unify-subst)
              (one-way-unify1-term-alist-lst
               (access pequiv-pattern pat :pre-rev)
               rewritten-args-rev
               nil
               (access pequiv pequiv :unify-subst))
              (cond
               ((null flg) geneqv)
               (t (mv-let
                   (flg unify-subst)
                   (one-way-unify1-term-alist-lst
                    (access pequiv-pattern pat :post)
                    rest-args alist unify-subst)
                   (declare (ignore unify-subst))
                   (cond
                    ((null flg) geneqv)
                    (t

; We extend geneqv by the equiv of the congruence rule of pequiv.  If some
; member of geneqv is a refinement of equiv then we delete that member.  This
; process may be inefficient if many such equiv are processed, since we will
; continually be taking the coarsenings of geneqv.  But for now, at least, we
; pay that price rather than the alternative of building an alist that pairs
; each congruence rule in geneqv with the coarsenings of its :equiv.

                     (mv-let
                      (changedp geneqv)
                      (reduce-geneqv-for-equiv equiv wrld geneqv)
                      (declare (ignore changedp))
                      (cons congruence-rule geneqv)))))))))))))))

(defun geneqv-and-pequiv-info-for-rewrite (fn bkptr rewritten-args-rev args
                                              alist parent-geneqv child-geneqv
                                              deep-pequiv-lst
                                              shallow-pequiv-lst
                                              wrld)
  (mv (geneqv-for-rewrite shallow-pequiv-lst fn bkptr rewritten-args-rev
                          (cdr args) alist wrld child-geneqv)
      (pequiv-info-for-rewrite fn bkptr rewritten-args-rev args alist
                               parent-geneqv deep-pequiv-lst)))

; Next we develop clausify, the function that reduces a term to a set
; of clauses.

(mutual-recursion

(defun ffnnamesp (fns term)

; We determine whether some function fn (possibly a lambda-expression)
; in fns is used as a function in term.  So this function is:
; (exists fn in fns s.t. (ffnnamep fn term)).

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (member-equal (ffn-symb term) fns)
             (ffnnamesp fns (lambda-body (ffn-symb term)))
             (ffnnamesp-lst fns (fargs term))))
        ((member-eq (ffn-symb term) fns) t)
        (t (ffnnamesp-lst fns (fargs term)))))

(defun ffnnamesp-lst (fns l)
  (if (null l)
      nil
    (or (ffnnamesp fns (car l))
        (ffnnamesp-lst fns (cdr l)))))

)

(mutual-recursion

(defun collect-ffnnames (fns term ans)

; We collect onto ans those members of fns used as functions in term.
; If ffnnamesp returns non-nil, then this function returns the non-nil
; subset of fns responsible.

  (cond
   ((variablep term) ans)
   ((fquotep term) ans)
   ((flambda-applicationp term)
    (collect-ffnnames fns
                      (lambda-body (ffn-symb term))
                      (collect-ffnnames-lst
                       fns
                       (fargs term)
                       (if (member-equal (ffn-symb term) fns)
                           (add-to-set-equal (ffn-symb term) ans)
                           ans))))
   (t (collect-ffnnames-lst fns (fargs term)
                            (if (member-eq (ffn-symb term) fns)
                                (add-to-set-eq (ffn-symb term) ans)
                                ans)))))

(defun collect-ffnnames-lst (fns l ans)
  (cond ((null l) ans)
        (t (collect-ffnnames-lst fns (cdr l)
                                 (collect-ffnnames fns (car l) ans)))))

 )

(defun comm-equal (fn lhs rhs term)

; This function is equivalent to
; (or (equal `(,fn ,lhs ,rhs) term)
;     (equal `(,fn ,rhs ,lhs) term))

  (and (nvariablep term)
       (not (fquotep term))
       (eq fn (ffn-symb term))
       (if (equal rhs (fargn term 2))
           (equal lhs (fargn term 1))
         (and (equal rhs (fargn term 1))
              (equal lhs (fargn term 2))))))

(defun member-term2 (fn lhs rhs cl)

; We determine whether either `(,fn ,lhs ,rhs) or `(,fn ,rhs ,lhs) is
; a member of cl.

; Note on Nomenclature: This is a subroutine of member-term.  It ought
; to be named member-term1, but in symmetry with
; member-complement-term, we named it member-term2.  Member-equal
; plays the role of member-term1.

  (cond ((null cl) nil)
        ((comm-equal fn lhs rhs (car cl)) cl)
        (t (member-term2 fn lhs rhs (cdr cl)))))

(defun member-complement-term2 (fn lhs rhs cl)
  (cond ((null cl) nil)
        ((and (ffn-symb-p (car cl) 'not)
              (comm-equal fn lhs rhs (fargn (car cl) 1)))
         cl)
        (t (member-complement-term2 fn lhs rhs (cdr cl)))))

(defun member-complement-term1 (lit cl)

; Lit is known not to be an equality or iff.  This fn is equivalent to
; (member-equal `(not ,lit) cl).

  (cond ((null cl) nil)
        ((and (ffn-symb-p (car cl) 'not)
              (equal lit (fargn (car cl) 1)))
         cl)
        (t (member-complement-term1 lit (cdr cl)))))

(mutual-recursion

(defun member-term (lit cl)

; We determine whether lit is a member-equal of cl, except that if the
; atom of lit is an equality or iff term, we also look for its
; commuted version.

  (cond ((variablep lit) (member-eq lit cl))
        ((fquotep lit) (member-equal lit cl))
        ((or (eq (ffn-symb lit) 'equal)
             (eq (ffn-symb lit) 'iff))
         (member-term2 (ffn-symb lit) (fargn lit 1) (fargn lit 2) cl))
        ((eq (ffn-symb lit) 'not)
         (member-complement-term (fargn lit 1) cl))
        (t (member-equal lit cl))))

(defun member-complement-term (lit cl)

; We determine whether the complement of lit is a member-equal of cl,
; except that if the atom of lit is an equality or iff we recognize
; its commuted version.

  (cond ((variablep lit) (member-complement-term1 lit cl))
        ((fquotep lit) (member-complement-term1 lit cl))
        ((or (eq (ffn-symb lit) 'equal)
             (eq (ffn-symb lit) 'iff))
         (member-complement-term2 (ffn-symb lit) (fargn lit 1) (fargn lit 2)
                                  cl))
        (t

; Before Version_8.4, in the case (eq (ffn-symb lit) 'not), we only checked
; (member-term (fargn lit 1) cl).  But we found a case where lit was of the
; form (not u) and cl contains (not (not u)), and we want to catch that case,
; too.  This problem was evidenced as follows; after the fix, we get a more
; appropriate result (NIL NIL).

;   ACL2 !>(GUARD-CLAUSES '(FLOOR X Y)
;                          NIL T
;                          '((NOT (RATIONALP X))
;                            (NOT (RATIONALP Y))
;                            (NOT (NOT (EQL Y '0))))
;                          (w state) NIL 'NEWV)
;   ((((NOT (NOT (EQL Y '0)))
;      (NOT (RATIONALP Y))
;      (NOT (RATIONALP X))
;      (NOT (EQL Y '0))))
;    NIL)
;   ACL2 !>

; The term (NOT (NOT (EQL Y '0))) arises from clausify, specifically from a
; call of call-stack under if-interp.  A long comment in call-stack explains
; why we return (list 'not x), but not "simplify (not (not x)) to x".

         (or (and (eq (ffn-symb lit) 'not)
                  (member-term (fargn lit 1) cl))
             (member-complement-term1 lit cl)))))

)

(defun instr-listp (l)
  (cond ((atom l)
         (equal l nil))
        (t (and (or (integerp (car l))
                    (let ((carl (car l)))
                      (case-match carl
                                  (('push . x)
                                   (pseudo-termp x))
                                  (('push-local . n)
                                   (integerp n))
                                  (('push-frame-ptr) t)
                                  (('go . x) (integerp x))
                                  (('test . x) (integerp x))
                                  (('call . term)
                                   (pseudo-termp term))
                                  (('ret . lst)
                                   (pseudo-term-listp lst)))))
                (instr-listp (cdr l))))))

(defun spliced-instr-listp (l)
  (cond ((atom l)
         (equal l nil))
        (t (and (let ((carl (car l)))
                  (case-match carl
                              (('push . x)
                               (pseudo-termp x))
                              (('push-local . n)
                               (integerp n))
                              (('push-frame-ptr) t)
                              (('test . x)
                               (spliced-instr-listp x))
                              (('call . term)
                               (pseudo-termp term))
                              (('ret . lst)
                               (pseudo-term-listp lst))))
                (spliced-instr-listp (cdr l))))))

(defun next-tag (l)
  (declare (xargs :guard (instr-listp l)))
  (cond ((null l) 1)
        ((and (consp (car l))
              (eq (caar l) 'test))
         (+ 2 (cdr (car l))))
        (t (next-tag (cdr l)))))

(defun if-compile-formal (var rformals i)
  (declare (xargs :guard (and (symbolp var)
                              (true-listp rformals)
                              (member-eq var rformals))))
  (cond ((eq var (car rformals)) i)
        (t (if-compile-formal var (cdr rformals) (1+ i)))))

; Rockwell Addition: Repeatedly in this new code we will be concerned
; with the question of whether we look inside of lambdas or not.  Many
; functions have an additional lambda-exp arg, telling them whether to
; go inside lambda applications.  These extra args will show up in a
; window comparison but aren't commented upon henceforth.

(mutual-recursion

(defun ffnnamep-hide (fn term lambda-exp)

; We determine whether the function fn (possibly a lambda-expression)
; is used as a function in term, without diving inside calls of HIDE.
; If lambda-exp is t we look inside of lambda bodies.  Otherwise we
; don't.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (equal fn (ffn-symb term))
             (and lambda-exp
                  (ffnnamep-hide fn (lambda-body (ffn-symb term))
                                 lambda-exp))
             (ffnnamep-hide-lst fn (fargs term) lambda-exp)))
        ((eq (ffn-symb term) fn) t)
        ((eq (ffn-symb term) 'hide) nil)
        (t (ffnnamep-hide-lst fn (fargs term) lambda-exp))))

(defun ffnnamep-hide-lst (fn l lambda-exp)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-listp l))))
  (if (null l)
      nil
    (or (ffnnamep-hide fn (car l) lambda-exp)
        (ffnnamep-hide-lst fn (cdr l) lambda-exp))))

)

(mutual-recursion

(defun if-compile (term lambda-exp ac rformals)

; We compile term.  If lambda-exp is t, we expand lambda applications.
; Otherwise, we don't.  Rformals is the list of formal parameters that
; occur in term.  It is nil outside of lambdas.  It MIGHT be nil
; inside of a lambda: ((lambda nil ...)).

; Here is the target language of our compiler:
; (push . term)      push term onto the stack.
; (push-local . n)   push the nth local onto the stack, where we
;                    enumerate the locals 0-based, starting from
;                    the right-most!  That is, in the compiled
;                    code for body in
;                    ((lambda (x y z) body) a b c)
;                    z is the 0th local, y is the 1st, and x is the
;                    2nd.
; (push-frame-ptr)   the current stack represents a complete frame;
;                    think of this as marking this point on the stack
;                    so that (push-local . n) fetches from here, offset
;                    back by n.
; (go . n)           transfer control to the instruction labeled n
; (test . n)         pop and test the top of the stack and if nil,
;                    transfer control to the instruction labeled n,
;                    else execute the next instruction.
; (call fn . lst)    Lst is a list that is completely irrelevant
;                    except for its length, n.  Pop n things off
;                    the stack, apply fn to them (top-most item
;                    on the stack being the last arg to fn), and
;                    push the result.
; (ret . lst)        Lst is a list that is irrelevant except for
;                    its length, n.  Pop one value off the stack and
;                    hold it as the returned value of the lambda
;                    expression just evaluated, then pop n things
;                    off the stack, clearing the most recent frame,
;                    and finally push the returned value.

  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term)

; Note:  What if rformals is nil?  Then we couldn't have hit a variable
; and we aren't in a lambda.

         (cond (rformals
                (cons (cons 'push-local (if-compile-formal term rformals 0))
                      ac))
               (t (cons (cons 'push term) ac))))
        ((or (fquotep term)
             (eq (ffn-symb term) 'hide))
         (cons (cons 'push term) ac))
        ((flambdap (ffn-symb term))

; This is a lambda application.  If we are supposed to expand lambdas
; and there is an IF inside the body of this one, we compile the body.
; Otherwise we treat it the same way we do ordinary function symbol
; applications.

         (cond
          ((and lambda-exp
                (ffnnamep-hide 'if (lambda-body (ffn-symb term)) lambda-exp))
           (cons (cons 'ret (lambda-formals (ffn-symb term)))
                 (if-compile (lambda-body (ffn-symb term))
                             lambda-exp
                             (cons '(push-frame-ptr)
                                   (if-compile-lst (fargs term)
                                                   lambda-exp ac rformals))
                             (revappend (lambda-formals (ffn-symb term))
                                        nil))))
          ((or (ffnnamep-hide-lst 'if (fargs term) lambda-exp)
               rformals)
           (cons (cons 'call term)
                 (if-compile-lst (fargs term)
                                 lambda-exp ac rformals)))
          (t (cons (cons 'push term) ac))))
        ((eq (ffn-symb term) 'if)
         (let* ((test-seg (if-compile (fargn term 1)
                                      lambda-exp ac rformals))
                (n (next-tag test-seg)))
           (cons (+ n 1)
                 (if-compile (fargn term 3)
                             lambda-exp
                             (cons n (cons (cons 'go (+ n 1))
                                           (if-compile (fargn term 2)
                                                       lambda-exp
                                                       (cons (cons 'test n)
                                                             test-seg)
                                                       rformals)))
                             rformals))))
        ((or (ffnnamep-hide-lst 'if (fargs term) lambda-exp)
             rformals)

; If there is an IF in some arg, we compile the args to get rid of the
; IFs.  Alternatively, if we are compiling a lambda body (with
; rformals), we must compile the args to deref them via the stack.

         (cons (cons 'call term)
               (if-compile-lst (fargs term)
                               lambda-exp ac rformals)))
        (t (cons (cons 'push term) ac))))

(defun if-compile-lst (l lambda-exp ac rformals)
  (declare (xargs :guard (pseudo-term-listp l)))
  (cond ((null l) ac)
        (t (if-compile-lst (cdr l)
                           lambda-exp
                           (if-compile (car l) lambda-exp ac rformals)
                           rformals))))

)

; The following code is a little weird.  We implement a data structure called
; "assumptions" for representing assumed terms.  In particular, we can add to
; the data structure to assume a term true and then we can quickly convert that
; structure to one in which the term is assumed false.  The pair of these
; assumptions always costs exactly two conses, total: either the first costs 1
; cons and the next does also, or the first costs 2 and the next is free.  Our
; representation of assumptions relies upon the fact that the keywords :NOT and
; :IGNORE-WHEN-CONVERTING-TO-CLAUSE are not legal variable symbols.  Our
; machinery for manipulating assumptions also exploits the fact that we never
; assume a quoted term -- we simply decide the issue.  Thus, (nvariablep x)
; means (ffn-symb x) is a function symbol or lambda expression.

; To assume an atm true, we add it to the list (one cons).  To assume an atom
; false, we add it to the list and then add :NOT in front of it (two conses).
; To negate the last assumption you either add a :NOT (one cons) or delete a
; :NOT (no conses).  The element :IGNORE-WHEN-CONVERTING-TO-CLAUSE plays no
; special role in determining the value of an atom -- it looks like a variable
; symbol assumed true.  We never "negate" it though!  That is, the process of
; "negating the last assumption" must be done in a disciplined way in which you
; negate an assumption that you were responsible for adding in the first place.

; Below we first write the function for recovering from this structure the
; assumed value of a term, getting the answer t (for assumed true), 'f (for
; assumed false) or nil (for unassumed).  Like member-term and
; member-complement-term this recovering process knows about the commutativity
; of equal and iff.  But this is faster than those two, both because
; assumptions cost fewer conses and because we get the answer to the question
; "is it assumed and if so which way?" in the same time we can use member-term
; or member-complement-term to get only half the answer.

; Then we write the function for converting an assumptions structure into a
; clause.  All assumptions after the :IGNORE-WHEN-CONVERTING-TO-CLAUSE marker
; are ignored during the process.  Thus, it is possible to load into an initial
; assumption a bunch of literals that will be known true or false appropriately
; during the clausification process but which will not be transferred into the
; answer clauses produced.

; Finally we write the function that converts a clause into an initial set of
; assumptions, marked :IGNORE-WHEN-CONVERTING-TO-CLAUSE.

; All of this is in support of our fast clausifier.  The whole idea, here
; exposed at the very end of this long comment, is to make it fast to explore
; and recognize tautologies, paying the price for creating the clause only when
; we have to.

(defun if-interp-assume-true (not-flg term assumptions)

; Adds the assumption that term is true/false according to whether
; not-flg is nil/t.  Thus, to assume term true, use not-flg nil.
; These assumptions must be used in a propositional setting.  That is,
; if p is assumed true in assumptions then (if-interp-assumed-value p
; assumption) will be t, but this doesn't mean that p equals t, it
; means (iff p t).  Note that term should not be a quotep.

  (cond ((variablep term)
         (if not-flg
             (cons :not (cons term assumptions))
           (cons term assumptions)))
        ((eq (ffn-symb term) 'not)
         (if-interp-assume-true (not not-flg) (fargn term 1) assumptions))
        (t
         (if not-flg
             (cons :not (cons term assumptions))
           (cons term assumptions)))))

(defun if-interp-switch (assumptions)

; Converts assumptions to the opposite parity on the most recent
; assumption.  I.e., if assumptions was created by assuming term true,
; the after this switch, the assumptions assume term false.

  (cond ((eq (car assumptions) :not) (cdr assumptions))
        (t (cons :not assumptions))))

; We now start the development of the lookup functions.  See
; if-interp-assumed-value for the top-level function.  All the others
; are just subroutines of that one.

(defun if-interp-assumed-value0 (var assumptions)

; Look up the assumed value of a variable symbol.

  (cond ((null assumptions) nil)
        ((eq (car assumptions) :not)
         (cond ((eq var (cadr assumptions)) 'f)
               (t (if-interp-assumed-value0 var (cddr assumptions)))))
        ((eq (car assumptions) var) 't)
        (t (if-interp-assumed-value0 var (cdr assumptions)))))

(defun if-interp-assumed-value1 (term assumptions)

; Look up the assumed value of an arbitrary non-NOT term -- i.e., just
; like the variable case but using equal instead of eq to compare.

  (cond ((null assumptions) nil)
        ((eq (car assumptions) :not)
         (cond ((equal term (cadr assumptions)) 'f)
               (t (if-interp-assumed-value1 term (cddr assumptions)))))
        ((equal (car assumptions) term) 't)
        (t (if-interp-assumed-value1 term (cdr assumptions)))))

(defun if-interp-assumed-value2-equal-constant (arg const1 assumptions)

; This function is an optimization of if-interp-assumed-value2, which looks up
; the assumed value of an EQUAL or IFF term.  However, here, we know the term
; is of the form (EQUAL arg const1), where const1 is a quoted constant.  The
; key difference between this situation and the more general one is that if
; assumptions contains (EQUAL arg const2), where const2 is different from
; const1, we know the answer is 'f.

  (cond ((null assumptions) nil)
        ((eq (car assumptions) :not)
         (let ((term (cadr assumptions)))
           (cond
            ((variablep term)
             (if-interp-assumed-value2-equal-constant arg const1 (cddr assumptions)))
            ((and (eq 'EQUAL (ffn-symb term))
                  (or (and (equal arg (fargn term 1))
                           (equal const1 (fargn term 2)))
                      (and (equal arg (fargn term 2))
                           (equal const1 (fargn term 1)))))
             'f)
            (t (if-interp-assumed-value2-equal-constant arg const1 (cddr assumptions))))))
        (t (let ((term (car assumptions)))
             (cond
              ((variablep term)
               (if-interp-assumed-value2-equal-constant arg const1 (cdr assumptions)))
              (t (let ((term-fn (ffn-symb term)))

; Term-fn is either a function symbol or a lambda expression.

                   (cond
                    ((eq term-fn 'EQUAL)
                     (cond
                      ((or (and (equal arg (fargn term 1))
                                (equal const1 (fargn term 2)))
                           (and (equal arg (fargn term 2))
                                (equal const1 (fargn term 1))))
                       't)
                      ((or (and (equal arg (fargn term 1))
                                (quotep (fargn term 2))
                                (not (equal const1 (fargn term 2))))
                           (and (equal arg (fargn term 2))
                                (quotep (fargn term 1))
                                (not (equal const1 (fargn term 1)))))
                       'f)
                      (t (if-interp-assumed-value2-equal-constant arg const1
                                                                  (cdr assumptions)))))
                    (t (if-interp-assumed-value2-equal-constant arg const1
                                                                (cdr assumptions)))))))))))

(defun if-interp-assumed-value2 (fn arg1 arg2 assumptions)

; Look up the assumed value of (fn arg1 arg2), where fn is a function
; symbol (e.g., EQUAL or IFF) that is known to be commutative.  This is
; like (or (if-interp-assumed-value1 `(,fn ,arg1 ,arg2) assumptions)
;          (if-interp-assumed-value1 `(,fn ,arg2 ,arg1) assumptions)).

  (cond ((null assumptions) nil)
        ((eq (car assumptions) :not)
         (let ((term (cadr assumptions)))
           (cond
            ((variablep term)
             (if-interp-assumed-value2 fn arg1 arg2 (cddr assumptions)))
            ((and (eq fn (ffn-symb term))
                  (or (and (equal arg1 (fargn term 1))
                           (equal arg2 (fargn term 2)))
                      (and (equal arg1 (fargn term 2))
                           (equal arg2 (fargn term 1)))))
             'f)
            (t (if-interp-assumed-value2 fn arg1 arg2 (cddr assumptions))))))
        ((let* ((term (car assumptions))
                (term-fn (and (nvariablep term)
                              (ffn-symb term))))

; Term-fn is either nil (in case term is a variable), or else a function symbol
; or a lambda expression.  Once upon a time, the (and (nvariablep term) ...)
; above included the conjunct (not (fquotep term)).  That is unnecessary.  If
; (nvariablep term), then we know (ffn-symb term) is a function symbol or
; lambda expression.  Thus, term could not be a quotep.

           (and (eq fn term-fn) ;nil is not a function symbol
                (or (and (equal arg1 (fargn term 1))
                         (equal arg2 (fargn term 2)))
                    (and (equal arg1 (fargn term 2))
                         (equal arg2 (fargn term 1))))))
         't)
        (t (if-interp-assumed-value2 fn arg1 arg2 (cdr assumptions)))))

(defun if-interp-assumed-value3 (term assumptions)

; Look up the assumed value of an arbitrary non-NOT (RATIONALP x) term.
; This function is very similar to if-interp-assumed-value1 except that
; if we find (INTEGERP x) assumed true, we know (RATIONALP x) is true.

  (cond ((null assumptions) nil)
        ((eq (car assumptions) :not)
         (cond ((equal term (cadr assumptions)) 'f)
               (t (if-interp-assumed-value3 term (cddr assumptions)))))
        ((equal (car assumptions) term) 't)
        ((and (ffn-symb-p (car assumptions) 'INTEGERP)
              (equal (fargn term 1) (fargn (car assumptions) 1)))
         't)
        (t (if-interp-assumed-value3 term (cdr assumptions)))))

(defun if-interp-assumed-value4 (term assumptions)

; Look up the assumed value of an arbitrary non-NOT (INTEGERP x) term.
; This function is very similar to if-interp-assumed-value1 except that
; if we find (RATIONALP x) assumed false, we know (INTEGERP x) is false.

  (cond ((null assumptions) nil)
        ((eq (car assumptions) :not)
         (cond ((equal term (cadr assumptions)) 'f)
               ((and (ffn-symb-p (cadr assumptions) 'RATIONALP)
                     (equal (fargn term 1) (fargn (cadr assumptions) 1)))
                'f)
               (t (if-interp-assumed-value4 term (cddr assumptions)))))
        ((equal (car assumptions) term) 't)
        (t (if-interp-assumed-value4 term (cdr assumptions)))))

(defun if-interp-assumed-value-x (term assumptions)

; Look up the assumed value of an arbitrary non-NOT term, treating
; EQUAL and IFF as commutative and recognizing that INTEGERP
; implies RATIONALP.

  (cond ((variablep term)
         (if-interp-assumed-value0 term assumptions))
        ((eq (ffn-symb term) 'EQUAL)
         (cond
          ((quotep (fargn term 1))
           (if-interp-assumed-value2-equal-constant (fargn term 2)
                                                    (fargn term 1)
                                                    assumptions))
          ((quotep (fargn term 2))
           (if-interp-assumed-value2-equal-constant (fargn term 1)
                                                    (fargn term 2)
                                                    assumptions))
          (t (if-interp-assumed-value2 (ffn-symb term)
                                       (fargn term 1)
                                       (fargn term 2)
                                       assumptions))))
        ((eq (ffn-symb term) 'IFF)
         (if-interp-assumed-value2 (ffn-symb term)
                                   (fargn term 1)
                                   (fargn term 2)
                                   assumptions))
        ((eq (ffn-symb term) 'RATIONALP)
         (if-interp-assumed-value3 term assumptions))
        ((eq (ffn-symb term) 'INTEGERP)
         (if-interp-assumed-value4 term assumptions))
        (t (if-interp-assumed-value1 term assumptions))))

(defun if-interp-assumed-value (term assumptions)

; Look up the assumed value of an arbitrary term, treating EQUAL and
; IFF as commutative.  This function returns t, f, or nil.  The last
; means that no assumptions about term are available.  The other
; indicate that term has been assumed true or false, respectively.
; Note that a value of t does not mean (EQUAL term T) but (IFF term
; T), under the assumptions.

  (cond ((variablep term)
         (if-interp-assumed-value0 term assumptions))
        ((eq (ffn-symb term) 'NOT)
         (let ((temp (if-interp-assumed-value-x (fargn term 1) assumptions)))
           (cond ((eq temp t) 'f)
                 ((eq temp 'f) t)
                 (t nil))))
        (t (if-interp-assumed-value-x term assumptions))))

(defun convert-assumptions-to-clause-segment (assumptions ans known-constants)

; We convert an assumptions structure to a clause segment, a list of disjoined
; literals to use as the hypothesis.  Assumptions represents a conjunction of
; assumptions.  E.g., (A :NOT B C D) represents (AND A (NOT B) C D).  Observe
; that this is the same as (NOT (OR (NOT A) B (NOT C) (NOT D))).  Thus, the
; clause segment is ((NOT A) B (NOT C) (NOT D)).  We reverse it as we create
; it.  When we get to the special marker :ignore-when-converting-to-clause we
; stop and act as though assumptions were nil.  This allows us to load up
; assumptions with some initial implicit literals that do not get transferred
; into the clauses we generate.

; We implement the optimization that if one of our assumptions is
; (EQUAL x 'const1) then any subsequent (NOT (EQUAL x 'const2)) is T and
; can be omitted, where const1 and const2 are different constants.
; That is, if assumptions is
; ((EQUAL x 'const1) :NOT (equal x 'const2) P Q)
; we return
; ((NOT (EQUAL x 'const1)) (NOT P) (NOT Q))
; instead of
; ((NOT (EQUAL x 'const1)) (EQUAL x 'const2) (NOT P) (NOT Q)).
; (Actually, our answer is reversed.)

; We always know that the positive equality precedes the negative one in
; the input assumptions.  That is, we will never see
; (:NOT (equal x 'const2) (EQUAL x 'const1) P Q)
; as our assumptions.  The reason is that if (EQUAL x 'const1) is already
; assumed, then when if-interp gets the value of (equal x 'const2) under the
; assumptions it will come back 'f.

; Thus, whenever we see a positive equality with a constant, (EQUAL x 'const1), we
; add the pair (x . const1) onto known-constants.  Whenever we see a negative
; equality with a constant, we ask if we know what the value is.

  (cond ((or (null assumptions)
             (eq (car assumptions) :ignore-when-converting-to-clause))
         ans)
        ((eq (car assumptions) :not)
         (let ((test (cadr assumptions)))

; Everything in the first branch of the cond below is devoted to the optimization
; of (NOT (EQUAL x 'const2)) when x is known to be a different 'const1.  To see
; the simple case of this function, skip to the T clause of this cond.

           (cond ((and (ffn-symb-p test 'equal)
                       (or (quotep (fargn test 1))
                           (quotep (fargn test 2))))
                  (cond ((quotep (fargn test 1))
                         (let* ((x (fargn test 2))
                                (const2 (fargn test 1))
                                (temp (assoc-equal x known-constants)))

; We are processing (NOT (EQUAL x const2)), where const2 is a quoted constant.
; If x is bound on known-constants to a different object, this assumption is
; trivially T and can be omitted from our answer.

                           (cond ((and temp
                                       (not (equal const2 (cdr temp))))
                                  (convert-assumptions-to-clause-segment
                                   (cddr assumptions)
                                   ans
                                   known-constants))
                                 (t (convert-assumptions-to-clause-segment
                                     (cddr assumptions)
                                     (cons test ans)
                                     known-constants)))))
                        ((quotep (fargn test 2))
                         (let* ((x (fargn test 1))
                                (const2 (fargn test 2))
                                (temp (assoc-equal x known-constants)))

; We are processing (NOT (EQUAL x const2)), where const2 is a quoted constant.
; If x is bound on known-constants to a different object, this assumption is
; trivially T and can be omitted from our answer.

                           (cond ((and temp
                                       (not (equal const2 (cdr temp))))
                                  (convert-assumptions-to-clause-segment
                                   (cddr assumptions)
                                   ans
                                   known-constants))
                                 (t (convert-assumptions-to-clause-segment
                                     (cddr assumptions)
                                     (cons test ans)
                                     known-constants)))))
                        (t (convert-assumptions-to-clause-segment
                            (cddr assumptions)
                            (cons test ans)
                            known-constants))))
                 (t
                  (convert-assumptions-to-clause-segment
                   (cddr assumptions)
                   (cons test ans)
                   known-constants)))))
        (t
         (let ((test (car assumptions)))
           (cond ((and (ffn-symb-p test 'equal)
                       (or (quotep (fargn test 1))
                           (quotep (fargn test 2))))
                  (cond
                   ((quotep (fargn test 1))
                    (convert-assumptions-to-clause-segment
                     (cdr assumptions)
                     (cons (list 'not test) ans)
                     (cons (cons (fargn test 2) (fargn test 1))
                           known-constants)))
                   ((quotep (fargn test 2))
                    (convert-assumptions-to-clause-segment
                     (cdr assumptions)
                     (cons (list 'not test) ans)
                     (cons (cons (fargn test 1) (fargn test 2))
                           known-constants)))
                   (t (convert-assumptions-to-clause-segment
                       (cdr assumptions)
                       (cons (list 'not test) ans)
                       known-constants))))
                 (t (convert-assumptions-to-clause-segment
                     (cdr assumptions)
                     (cons (list 'not test) ans)
                     known-constants)))))))

(defun convert-clause-to-assumptions (clause ans)

; The falsity of each literal in clause is encoded into our assumptions format.
; We then cover the entire list of assumptions with the mark
; :ignore-when-converting-to-clause.  The function if-interp-assumed-value
; properly recovers from these assumptions the values of the literals assumed
; false here.  The :ignore-when-converting-to-clause marker is innocuous since
; it looks like a variable assumed true, but we will never ask about a keyword
; "variable".  As if-interp explores its term to construct clauses it will
; extend our assumptions and if-interp-assumed-value continues to recover
; values of new and old assumptions.  But when if-interp finally builds a
; clause from assumptions, it ignores the ones stemming from clause.

  (cond ((null clause)
         (cons :ignore-when-converting-to-clause ans))
        (t (convert-clause-to-assumptions
            (cdr clause)
            (if-interp-assume-true t (car clause) ans)))))

; Rockwell Addition: Minor change.  We used to create the instantiation
; sublis-var.  Now I chase vars.

(defun simplifiable-mv-nth1 (n cons-term alist)

; N is a natural number.  If cons-term/alist is of the form (cons v0 ... (cons
; vn ...)), we return (mv vn rewritep), where rewritep is a flag indicating
; whether vn is an already-rewritten term extracted from the alist (nil), or a
; term that still needs to be rewritten with respect to the alist (t).  We
; return (mv nil nil) if we do not like what we see.

  (cond ((variablep cons-term)
         (let ((temp (assoc-eq cons-term alist)))
           (cond (temp (mv-let (term1 rewritep)
                         (simplifiable-mv-nth1 n (cdr temp) nil)
                         (declare (ignore rewritep))

; The rewritep returned by this call is t if a term was returned, because alist
; = nil.  But since (cdr temp) has already been rewritten, so has term1 (if
; non-nil); so we return rewritep = nil.  The use of rewritep in the definition
; of rewrite, where simplifiable-mv-nth is called, is a change after
; Version_8.2.  At one time we always rewrote the new term (called term1 here),
; but Sol Swords noticed that such double rewriting can be very expensive.

                         (mv term1 nil)))
                 (t (mv nil nil)))))
        ((fquotep cons-term)

; If the guts of this quote is a true-list of sufficient length, we
; return the correct answer.  Otherwise, we indicate that we cannot
; determine the value.  We could, always, determine the value in this
; case, but we are lazy and there seems little point.

         (cond ((and (true-listp (cadr cons-term))
                     (> (length (cadr cons-term)) n))
                (mv (kwote (nth n (cadr cons-term)))

; We could perhaps return nil here, but instead we return t so that this quotep
; result is handled in the usual way by rewrite -- at this writing, it is
; returned unchanged -- rather than passing it to rewrite-solidify-plus.

                    t))
               (t (mv nil nil))))
        ((eq (ffn-symb cons-term) 'cons)
         (if (= n 0)
             (mv (fargn cons-term 1) t)
           (simplifiable-mv-nth1 (1- n) (fargn cons-term 2) alist)))
        (t (mv nil nil))))

(defstub simplifiable-mv-nth-p () t)
(defattach simplifiable-mv-nth-p constant-t-function-arity-0)

(defun simplifiable-mv-nth (term alist)

; Term must be of the form (mv-nth & &), i.e., the ffn-symb of term is known to
; be 'mv-nth.  We determine whether we can simplify this and if so we return
; (mv term' rewritep) as the simplification.  If we cannot, we return (mv nil
; nil).  We look for (mv-nth 'i (cons v1 ... (cons vi ...))), but we allow the
; two arguments of term to be variable symbols that are looked up.  That is, we
; allow (MV-NTH I V) where I is bound in alist to a quoted constant and V is
; bound to a CONS term.  The second value, rewritep, is T unless the second
; argument to the mv-nth was a variable, in which case it is NIL to indicate
; that the resulting term has already been rewritten and should not be
; rewritten again.

  (cond ((simplifiable-mv-nth-p)
         (let ((arg1 (cond ((variablep (fargn term 1))
                            (let ((temp (assoc-eq (fargn term 1) alist)))
                              (cond (temp (cdr temp))
                                    (t (fargn term 1)))))
                           (t (fargn term 1)))))
           (cond ((and (quotep arg1)
                       (integerp (cadr arg1))
                       (>= (cadr arg1) 0))
                  (simplifiable-mv-nth1 (cadr arg1) (fargn term 2) alist))
                 (t (mv nil nil)))))
        (t (mv nil nil))))

(defun call-stack (fn lst stack assumptions ac)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp stack)
                              (>= (length stack) (length lst)))))
  (cond ((null lst)
         (cons (cond
                ((eq fn 'not)
                 (let ((x (car ac)))
                   (cond
                    ((quotep x)
                     (if (eq (cadr x) nil)
                         *t*
                       *nil*))
                    (t (let ((temp (if-interp-assumed-value x
                                                            assumptions)))
                         (cond ((eq temp t) *nil*)
                               ((eq temp 'f) *t*)
;                              ((variablep x) (list 'not x))

; Note: In Version_2.7 it was noticed by Qiang Zhang that the there
; was an unsoundness which we traced to the two lines commented out
; below.  This unsoundness goes fairly far back into the history of
; ACL2 and allowed us to prove (equal (and p q) (not (or (not p) (not
; q)))).  If it is found important to simplify (not (not x)) to x, as
; is done here, it will be necessary to determine whether we are in a
; propositional context, e.g., IFF-FLG = T or geneqv = *geneqv-iff*.
; But we have no such contextual information in the compiled code
; being traversed by if-interp.  It would be necessary to change the
; if-compile to insert some kind of iff-flg into the instructions
; generated to code the fact that this value is destined to be used in
; a propositional way.  If we restore the lines below, then we will
; need to restore the line commented out above (with the variablep
; test).

;                              ((eq (ffn-symb x) 'not)
;                               (fargn x 1))

                               (t (list 'not x))))))))
                ((eq fn 'equal)
                 (cond
                  ((equal (car ac) (cadr ac))
                   *t*)
                  ((and (quotep (car ac))
                        (quotep (cadr ac)))
                   *nil*)
                  ((and (equal (car ac) *t*)
                        (ffn-symb-p (cadr ac) 'equal))

; Note:  (equal t (equal a b)) = (equal a b).

                   (cadr ac))
                  ((and (equal (cadr ac) *t*)
                        (ffn-symb-p (car ac) 'equal))
                   (car ac))
                  (t (fcons-term fn ac))))

; Rockwell Addition: Now during clausification we know that (< x x) is
; nil and (< 'i 'j) can be decided when i and j are rationals.

                ((eq fn '<)
                 (cond
                  ((equal (car ac) (cadr ac))
                   *nil*)
                  ((and (quotep (car ac))
                        (quotep (cadr ac))
                        (rationalp (cadr (car ac)))
                        (rationalp (cadr (cadr ac))))
                   (if (< (cadr (car ac)) (cadr (cadr ac)))
                       *t*
                     *nil*))
                  (t (cons-term fn ac))))
                ((eq fn 'iff)
                 (let ((arg1 (car ac))
                       (arg2 (cadr ac)))
                   (cond
                    ((equal arg1 arg2)
                     *t*)
                    (t (let ((temp1 (if (quotep arg1)
                                        (if (eq (cadr arg1) nil)
                                            'f
                                          t)
                                      (if-interp-assumed-value arg1 assumptions)))
                             (temp2 (if (quotep arg2)
                                        (if (eq (cadr arg2) nil)
                                            'f
                                          t)
                                      (if-interp-assumed-value arg2 assumptions))))
                         (cond ((and temp1
                                     temp2)
                                (if (eq temp1 temp2)
                                    *t*
                                  *nil*))

; There is a temptation here to simplify (iff t x) to x, which
; preserves iff but not equal.  But this call of IFF might be in a
; equal-preserving slot, e.g., (CONS (IFF T (IF A X Y)) TL).

                               (t (fcons-term fn ac))))))))
                ((eq fn 'mv-nth)

; This optimization of clausify is slightly tainted by the fact that it is
; using the definition of mv-nth without reporting it in a ttree (there is no
; ttree).

                 (let ((term (fcons-term fn ac)))
                   (mv-let (term1 rewritep)
                     (simplifiable-mv-nth term nil)
                     (declare (ignore rewritep))
                     (or term1 term))))
                (t (cons-term fn ac)))
               stack))
        (t (call-stack fn (cdr lst) (cdr stack)
                       assumptions
                       (cons (car stack) ac)))))

(defun ret-stack (lst stack)
  (cond ((null lst) stack)
        (t (ret-stack (cdr lst) (cdr stack)))))

(defun extra-info-lit-p (lit)
  (and (ffn-symb-p lit 'not)
       (let ((atm (fargn lit 1)))
         (and (nvariablep atm)
              (eq (ffn-symb atm) *extra-info-fn*)))))

(defun subsetp-equal-mod-extra-info-lits (x y)
  (declare (xargs :guard (and (true-listp y)
                              (true-listp x))))
  (cond ((endp x) t)
        ((or (extra-info-lit-p (car x))
             (member-equal (car x) y))
         (subsetp-equal-mod-extra-info-lits (cdr x) y))
        (t nil)))

(defun quick-and-dirty-subsumption-replacement-step1 (cl1 cl2)
  (cond ((null cl1) 'subsumed2)
        ((extra-info-lit-p (car cl1))
         (quick-and-dirty-subsumption-replacement-step1 (cdr cl1) cl2))
        ((null cl2) 'subsumed1)
        ((extra-info-lit-p (car cl2))
         (quick-and-dirty-subsumption-replacement-step1 cl1 (cdr cl2)))
        ((equal (car cl1) (car cl2))
         (let ((ans (quick-and-dirty-subsumption-replacement-step1 (cdr cl1) (cdr cl2))))
           (cond ((symbolp ans)

; Experiments show that (symbolp ans) is marginally faster than (or (null ans)
; (eq ans 'subsumed2) (eq ans 'subsumed1)).

                  ans)
                 (t (cons (car cl1) ans)))))
        ((and (complementaryp (car cl1) (car cl2))
              (subsetp-equal-mod-extra-info-lits (cdr cl1) (cdr cl2)))
         (cdr cl2))
        (t nil)))

(defun quick-and-dirty-subsumption-replacement-step (cl1 lst)

; Aka The Satriani Hack (Note on the Derivation of the Name: The theme music of
; this exercise was Joe Satriani's "Motorcycle Driver" on The Extremist album.
; That track was not just what I was listening to while this code was written;
; the structure of the music sort of inspired the code.  The music starts out
; boringly repetitive and "slow."  A fairly decent guitar solo at 2:02 doesn't
; do the job, in the sense that after this attempted speedup the plodding drums
; still dominate and the repetitive theme reemerges.  But then, at 3:33 the
; guitar, spewing frustration, breaks out into a really wild solo that persists
; into the next reoccurrence of the theme and ends the song.  The sense I get
; while listening to that solo is that the guitarist simply abandoned the
; structure and did whatever it took.  That is the theme of the Satriani Hack,
; which actually is not localized here but involves little tweaks and patches
; in several places, to get the speedup I wanted.  JSM.)

; This function is akin to subsumption-replacement-loop except that it only
; takes one step and is much more limited in its detection of the
; subsumption/replacement conditions.  Let lst be a set of clauses we have to
; prove.  Imagine that we are going to add cl1 to that set.  If cl1 is subsumed
; by any clause in lst, we needn't add it.  Among other things, this function
; checks a limited form of that condition; if we return 'subsumed1 then cl1 is
; subsumed by some clause in lst.  Otherwise, suppose that cl1 can be resolved
; against some clause, cl2, of lst to produce a clause cl3 that subsumes cl2.
; We call this a "replacement resolution."  For example, suppose

; cl1 = {a b  c d   e}
; cl2 = {a b -c d f e g}
; cl3 = {a b    d f e g}

; Then when we add cl1 to the set of clauses to prove we can delete cl2 from
; the set and replace it with cl3.  In addition, if cl1 simply subsumes some
; cl2, we can delete cl2 from the set.  If this function does not return
; 'subsumed1 then it returns a new set of clauses in which some of those
; subsumed by cl1 have been deleted and some of those that participate in
; replacement resolution with cl1 have been appropriately replaced.  Thus, if
; this function does not return 'subsumed1 it is sound to add cl1 to the output
; of this function and attack that set of clauses.

; The "quick and dirty" part of this is that we do not consider all possible
; literals upon which to do replacement resolution but rather only consider
; resolving on the first literal in cl1 that differs from the corresponding
; literal of cl2, and we insist that the corresponding literal of cl2 be the
; required complement.  The "step" part comes from the fact that we don't
; consider every possible pair of cl1 and cl2 but only the about-to-be-added
; cl1 against the already added cl2s.

; This rather draconian restriction is judged heuristically important because
; of the order in which clauses are generated.  The motivating example was of
; the form

;     (clausify
;      '(not (if A
;                (if (if E1
;                        't
;                        (if E2
;                            't
;                            E3))
;                    B
;                    'nil)
;                'nil))
;      nil
;      t    ; or nil, no lambdas here.
;      (sr-limit (w state)))

; Before we added this quick and dirty test, we created
; {-a -e1         -b}
; {-a  e1 -e2     -b}
; {-a  e1  e2 -e3 -b}
; The general-purpose subsumption-replacement-loop would work this down to
; {-a -e1         -b}
; {-a     -e2     -b}
; {-a         -e3 -b}

; But that was slow because it considers all possible ways of resolving and
; subsuming.  After a couple of days of Satriani and some false starts, it was
; realized (in the shower, no less) that the clauses were probably generated in
; just the right order to let us detect this condition quickly on the fly.

; Another motivating example comes from clausifying the opened up version of
; (not (member x '(1 2 ... 128))).  This arises when the member term is used as
; a hypothesis.  The problem becomes:

; (clausify '(not (if e1 't (if e2 't (if e3 't ...(if e127 't e128)...))))
;           nil t (sr-limit (w state)))

; which is like the (if e1 ...) nest above.  In Nqthm the clausifier had
; special purpose rules for handling a negated disjunction, but that is harder
; in ACL2 because the compiled form of the term hides the negation.  But the
; Satriani hack takes care of it, by cleaning up the clause set locally as it
; is produced, leaving the quadratic general-purpose
; subsumption-replacement-loop with nothing to do.

; To see this hack in action, first define the function that maps
; the list of standard chars into the list of standard codes:

;     (defun make-standard-codes (lst)
;      (if (endp lst)
;          nil
;          (cons (char-code (car lst)) (make-standard-codes (cdr lst)))))

; and use it to define the appropriate constant

;     (defconst *standard-codes* (make-standard-codes *standard-chars*))

; Then prove

;     (thm (implies (member x *standard-chars*)
;                   (member (char-code x) *standard-codes*)))

; With the Satriani hack in place, the proof takes 3.87 seconds.  With the
; Satriani hack omitted, it takes 431.92 seconds!  (Note: to omit the Satriani
; hack from these sources redefine the function if-interp-add-clause below so
; that ans is bound to ac rather than to the call of
; quick-and-dirty-subsumption-replacement-step.)

  (cond
   ((null lst) nil)
   ((time-limit5-reached-p ; nil, or throws
     "Out of time in subsumption ~
      (quick-and-dirty-subsumption-replacement-step).")
    nil)
   (t (let ((cl3 (quick-and-dirty-subsumption-replacement-step1 cl1 (car lst))))
        (cond
         ((eq cl3 'subsumed1) 'subsumed1)
         (t (let ((ans
                   (quick-and-dirty-subsumption-replacement-step cl1
                                                                 (cdr lst))))
              (cond
               ((eq cl3 'subsumed2)
                ans)
               ((eq ans 'subsumed1) ans)
               ((null cl3)
                (cons (car lst) ans))
               (t (cons cl3 ans))))))))))

(defstub quick-and-dirty-srs (cl1 ac) t)

(defun quick-and-dirty-srs-builtin (cl1 ac)
  (declare (ignore cl1 ac)
           (xargs :mode :logic :guard t))
  t)

(defattach quick-and-dirty-srs quick-and-dirty-srs-builtin)

(defun if-interp-add-clause (assumptions cl ac pflg)

; This is how we add a new clause to if-interp's accumulator, ac.  The clause
; we add is the one recovered from the current assumptions, starting with the
; clause cl.  If pflg is t then the caller is not interested in the set of
; clauses but just whether the set is empty or not.  In that case, we return t
; if the set of clauses is non-empty and nil if it is empty.

  (cond
   (pflg t)
   (t
    (let ((cl1 (convert-assumptions-to-clause-segment assumptions cl nil)))
      (cond
       ((quick-and-dirty-srs cl1 ac)
        (let ((ans (quick-and-dirty-subsumption-replacement-step cl1 ac)))
          (cond ((eq ans 'subsumed1) ac)
                (t (cons cl1 ans)))))
       (t (cons cl1 ac)))))))

(defun if-interp (instrs stack frame-ptr-stack assumptions ac pflg)

; First consider the case that pflg is nil.  Then we return the set of clauses
; extracted from instrs, together with those already in ac.

; Otherwise pflg is a natural number, and we quit as soon as we know that there
; will be at least one clause.  When we so quit, we return t.  Otherwise we
; return pflg, which counts down as steps are taken.  Thus if we return 0, then
; there might or might not be at least one clause, but if we return a positive
; integer, then the term encoded in instrs is a tautology.

  (declare (type (or null (unsigned-byte 29)) pflg))
  (cond ((null instrs)
         (let ((v (car stack)))
           (or (cond ((quotep v)
                      (cond ((equal v *nil*)
                             (if-interp-add-clause assumptions nil ac pflg))
                            (t ac)))
                     (t (let ((assumed-val (if-interp-assumed-value v assumptions)))
                          (cond ((eq assumed-val t) ac)
                                ((eq assumed-val 'f)
                                 (if-interp-add-clause assumptions nil ac pflg))
                                (t (if-interp-add-clause assumptions (list v) ac pflg))))))
               pflg)))
        ((and pflg (zpf pflg))
         0)
        (t (let ((caarinstrs (caar instrs))
                 (pflg (and pflg (1-f pflg))))
             (declare (type (or null (unsigned-byte 29)) pflg))
             (case caarinstrs
               (push (if-interp (cdr instrs)
                                (cons (cdr (car instrs))
                                      stack)
                                frame-ptr-stack
                                assumptions
                                ac
                                pflg))
               (push-local (if-interp (cdr instrs)
                                      (cons (nth (cdr (car instrs))
                                                 (car frame-ptr-stack))
                                            stack)
                                      frame-ptr-stack
                                      assumptions
                                      ac
                                      pflg))
               (push-frame-ptr (if-interp (cdr instrs)
                                          stack
                                          (cons stack frame-ptr-stack)
                                          assumptions
                                          ac
                                          pflg))
               (ret (if-interp (cdr instrs)
                               (cons (car stack)
                                     (ret-stack (cdr (car instrs)) (cdr stack)))
                               (cdr frame-ptr-stack)
                               assumptions
                               ac
                               pflg))
               (call (if-interp (cdr instrs)
                                (call-stack (cadr (car instrs))
                                            (cddr (car instrs))
                                            stack
                                            assumptions
                                            nil)
                                frame-ptr-stack
                                assumptions
                                ac
                                pflg))
               (test (let* ((v (car stack))
                            (stack (cdr stack)))
                       (cond ((quotep v)
                              (cond ((equal v *nil*)
                                     (if-interp (cdr (car instrs))
                                                stack
                                                frame-ptr-stack
                                                assumptions
                                                ac
                                                pflg))
                                    (t (if-interp (cdr instrs)
                                                  stack
                                                  frame-ptr-stack
                                                  assumptions
                                                  ac
                                                  pflg))))
                             (t (let ((temp (if-interp-assumed-value
                                             v
                                             assumptions)))
                                  (cond
                                   ((eq temp 'f)
                                    (if-interp (cdr (car instrs))
                                               stack
                                               frame-ptr-stack
                                               assumptions
                                               ac
                                               pflg))
                                   ((eq temp t)
                                    (if-interp (cdr instrs)
                                               stack
                                               frame-ptr-stack
                                               assumptions
                                               ac
                                               pflg))
                                   (pflg
                                    (let ((assumptions
                                           (if-interp-assume-true
                                            nil
                                            v
                                            assumptions)))
                                      (let ((pflg (if-interp (cdr instrs)
                                                             stack
                                                             frame-ptr-stack
                                                             assumptions
                                                             ac
                                                             pflg)))
                                        (cond
                                         ((eq pflg t) t)
                                         (t (if-interp (cdr (car instrs))
                                                       stack
                                                       frame-ptr-stack
                                                       (if-interp-switch
                                                        assumptions)
                                                       ac
                                                       pflg))))))
                                   (t
                                    (let ((assumptions
                                           (if-interp-assume-true
                                            nil v assumptions)))
                                      (if-interp (cdr instrs)
                                                 stack
                                                 frame-ptr-stack
                                                 assumptions
                                                 (if-interp (cdr (car instrs))
                                                            stack
                                                            frame-ptr-stack
                                                            (if-interp-switch assumptions)
                                                            ac
                                                            pflg)
                                                 pflg))))))))))))))

(defun splice-instrs1 (instrs ans alist)
  (declare (xargs :guard (instr-listp instrs)))
  (cond ((null instrs)
         ans)
        ((atom (car instrs))
         (splice-instrs1 (cdr instrs)
                         ans
                         (cons (cons (car instrs)
                                     ans)
                               alist)))
        (t (let ((caarinstrs (caar instrs)))
             (case caarinstrs
                   ((push push-local push-frame-ptr call ret)
                    (splice-instrs1
                     (cdr instrs)
                     (cons (car instrs) ans)
                     alist))
                   (test
                    (splice-instrs1
                     (cdr instrs)
                     (cons (cons 'test
                                 (cdr (assoc (cdr (car instrs)) alist)))
                           ans)
                     alist))
                   (go
                    (splice-instrs1
                     (cdr instrs)
                     (cdr (assoc (cdr (car instrs)) alist))
                     alist)))))))

(defun splice-instrs (instrs)
  (declare (xargs :guard (instr-listp instrs)))
  (splice-instrs1 instrs nil nil))

(defun strip-branches (term assumptions lambda-exp)

; We return a set of clauses whose conjunction is equivalent to term in the context
; of the assumptions given.  See clausify.

  (declare (xargs :guard (pseudo-termp term)))
  (cond
   ((and (ffn-symb-p term 'if)
         (equal (fargn term 3) *nil*))

; Term is of the form (if p q 'nil).  We will strip the branches of each in
; isolation and union them together.  The original justification of this was
; so that when we clausify the translation of (and (implies p q) r) we get
; back two clauses, {~p q} and {r}.  Without this modification, we get back
; three clauses, {p r}, {~p q}, and {~q r}.  Except for here, strip-branches
; is not recursive and this special treatment of conjuncts is not done in
; other contexts.

    (union-equal
     (strip-branches (fargn term 1) assumptions lambda-exp)
     (strip-branches (fargn term 2) assumptions lambda-exp)))
   (t
    (if-interp (splice-instrs (if-compile term lambda-exp nil nil)) nil nil
               assumptions
               nil nil))))

(defun merge-length (l1 l2)
  (declare (xargs :guard (and (true-list-listp l1)
                              (true-list-listp l2))))
  (cond ((null l1) l2)
        ((null l2) l1)
        ((<= (length (car l1)) (length (car l2)))
         (cons (car l1) (merge-length (cdr l1) l2)))
        (t (cons (car l2) (merge-length l1 (cdr l2))))))

(defun merge-sort-length (l)
  (declare (xargs :guard (true-list-listp l)))
  (cond ((null (cdr l)) l)
        (t (merge-length (merge-sort-length (evens l))
                         (merge-sort-length (odds l))))))

(defun member-equal-+- (lit clause)

; We return '+ if lit is a member of clause.  We return '- if the complement of
; lit is a member of clause.  Otherwise we return nil.  If both conditions are
; met, we return either '+ or '- depending on which occurs first.  For example,
; let clause be '(A (NOT B)).  Then if lit is A we return '+.  If lit is (NOT
; A) we return '-.  We also return '- when lit is B.  If lit is C we return
; nil.

  (cond ((null clause) nil)
        ((equal lit (car clause)) '+)
        ((complementaryp lit (car clause)) '-)
        (t (member-equal-+- lit (cdr clause)))))

(defun arg1-almost-subsumes-arg2 (arg1 arg2)
  (declare (xargs :guard (and (pseudo-term-listp arg1)
                              (pseudo-term-listp arg2))))

; We are interested in ``throwing away,'' or at least shortening, the
; clause arg2.  We return 'subsumed, a cons, or nil.

; If the clause arg1 subsumes (i.e. is a subset of) arg2, then
; 'subsumed is returned.  This means we can ``throw away arg2'',
; because arg1 <-> (arg1 & arg2) since if arg1 is true, so is arg2,
; whereas if arg1 is false, so is the conjunction.

; If arg1 is a subset of arg2 except for one literal of arg1 which occurs
; complemented in arg2, we return a cons whose car is that literal.
; Note that the resolvent of arg1 and arg2 on this literal produces a
; clause that subsumes arg2:  the clause obtained by deleting the
; complement of the literal in question.

; Here is a more careful argument that we can delete the complement.
; If the subsumption fails but arg1 has the form {x} u arg1' (x not
; in arg1'), arg1' subsumes arg2, and -x occurs in arg2, then the
; tail of arg1 starting at x (which will be non-nil, of course) is
; returned.  In this case, we can REPLACE arg2 with arg2 - {-x},
; which has one less literal.  This replacement is justified by the
; fact that arg1 & arg2 <-> arg1 & (arg2 - {-x}).  Proof.  If arg1 is
; false, both sides are false.  If arg1 is true, then the equivalence
; reduces to arg2 <-> arg2 - {-x}.  But if arg1 is true, either x or
; arg1' is true.  If arg1' is true, then so is arg2 and arg2 - {-x}.
; On the other hand, if x is true, then -x is false, so the
; equivalence is the observation that we can throw out false
; disjuncts.

  (cond ((null arg1)
         'subsumed)
        ((extra-info-lit-p (car arg1))
         (arg1-almost-subsumes-arg2 (cdr arg1) arg2))
        (t (let ((sign (member-equal-+- (car arg1) arg2)))

; Sign is +, -, or nil, meaning (car arg1) occurs in arg2, the complement of
; (car arg1) occurs in arg2, or neither occur.

             (cond
              ((null sign) nil)
              ((eq sign '+)
               (arg1-almost-subsumes-arg2 (cdr arg1) arg2))
              ((subsetp-equal-mod-extra-info-lits (cdr arg1) arg2)
               arg1)
              (t nil))))))

(defun find-subsumer-replacement-rec (cl l len-cl)
  (declare (xargs :guard (and (pseudo-term-listp cl)
                              (pseudo-term-list-listp l)
                              (equal len-cl (length cl)))))

; See find-subsumer-replacement.

  (cond ((null l) (mv nil nil))
        ((> (len (car l)) len-cl)

; Although in principle it seems that (car l) could "almost subsume" cl (in the
; sense of arg1-almost-subsumes-arg2 below), we rather expect that to be rare,
; since "almost subsume" is a sort of subset relation.

         (find-subsumer-replacement-rec cl (cdr l) len-cl))
        (t (let ((here (arg1-almost-subsumes-arg2 (car l) cl)))
             (cond ((eq here 'subsumed) (mv here (car l)))
                   (t (mv-let (rst cl0)
                        (find-subsumer-replacement-rec cl (cdr l) len-cl)
                        (cond ((eq rst 'subsumed) (mv rst cl0))
                              (t (mv (or here rst) nil))))))))))

(defun find-subsumer-replacement (cl l)
  (declare (xargs :guard (and (pseudo-term-listp cl)
                              (pseudo-term-list-listp l))))

; We return (mv val cl0), where val is nil to indicate that no subsumer or
; replacer was found, or 'subsumed to indicate cl is subsumed by clause cl0 in
; l, or if neither of these cases applies, then a pair (indicating that the
; complement of the car of the pair may be removed from cl).  The last case
; means that somewhere in l we found a clause that when resolved with cl
; produces a resolvent that subsumes cl.

  (find-subsumer-replacement-rec cl l (length cl)))

(defun remove-one-complement (lit cl)
  (declare (xargs :guard (and (pseudo-termp lit)
                              (pseudo-term-listp cl))))
  (cond ((null cl) nil)
        ((complementaryp lit (car cl)) (cdr cl))
        (t (cons (car cl) (remove-one-complement lit (cdr cl))))))

(defun weak-disc-tree (x)
  (and (or (consp x) (equal x nil))
       (cond ((equal (car x) 'node)
              (and (true-listp x)
                   (equal (length x) 4)
                   (pseudo-termp (cadr x))
                   (weak-disc-tree (caddr x))
                   (weak-disc-tree (cadddr x))))
             (t (pseudo-term-list-listp (cdr x))))))

(defun sweep-clauses1 (tree ac)
  (declare (xargs :guard (weak-disc-tree tree)))
  (cond ((eq (car tree) 'node)
         (sweep-clauses1 (caddr tree) (sweep-clauses1 (cadddr tree) ac)))
        (t (append (cdr tree) ac))))

(defun sweep-clauses (tree)
  (declare (xargs :guard (weak-disc-tree tree)))
  (sweep-clauses1 tree nil))

(defun filter-with-and-without (x l with-lst without-lst)

; L is a list of clauses.  X is a literal.  We partition l into two sets:  the
; with-lst contains those clauses with x as a (positive or negative) literal;
; the without-lst are all others.  Then we return (mv with-lst without-lst).

; We consider a negated call of EXTRA-INFO to belong to every clause!

  (cond ((null l) (mv with-lst without-lst))
        ((or (extra-info-lit-p x)
             (member-equal-+- x (car l)))
         (filter-with-and-without x (cdr l)
                                  (cons (car l) with-lst)
                                  without-lst))
        (t (filter-with-and-without x (cdr l)
                                    with-lst
                                    (cons (car l) without-lst)))))

(defun disc-tree (x)

; A disc-tree, or ``discrimination tree'' is a data structure that organizes a
; set of clauses.  The basic shape is

; disc-tree := (TIP clauses) | (NODE lit disc-tree_1 disc-tree_2),

; The ``clauses in a disc-tree'' is just the set of all the clauses occurring
; in some tip.  This is computed by sweep-clauses.

; But the important invariant of a disc-tree NODE is that all the clauses in
; disc-tree_1 contain a (positive or negative) occurrence of lit, and none of
; the clauses in disc-tree_2 contain such an occurrence.

; We test this invariant below by collecting all the clauses in disc-tree_i
; and confirming that either every clause or no clause contains the lit.  We
; use filter-with-and-without to partition the clauses in a list according to
; whether they contain an occurrence of lit.  If we partition the clauses in
; disc-tree_i into ``with lit'' and ``without lit'' buckets, the ``with lit''
; bucket is set equal to the entire set of disc-tree_1 and the ``without lit''
; bucket is set equal to the entire set for disc-tree_2.  But rather than test
; set equality we exploit the fact that we know filter-with-and-without really
; partitions and just test that the ``without lit'' bucket is empty for
; disc-tree_1 and the ``with lit'' bucket is empty for disc-tree_2.

  (and (or (consp x) (equal x nil))
       (cond ((equal (car x) 'node)
              (and (true-listp x)
                   (equal (length x) 4)
                   (pseudo-termp (cadr x))
                   (disc-tree (caddr x))
                   (disc-tree (cadddr x))
                   (mv-let (with-lst without-lst)
                     (filter-with-and-without (cadr x)
                                              (sweep-clauses (caddr x))
                                              nil nil)
                     (declare (ignore with-lst))
                     (null without-lst))
                   (mv-let (with-lst without-lst)
                     (filter-with-and-without (cadr x)
                                              (sweep-clauses (cadddr x))
                                              nil nil)
                     (declare (ignore without-lst))
                     (null with-lst))))
             (t (pseudo-term-list-listp (cdr x))))))

(defun find-clauses1 (clause tree ac)
  (declare (xargs :guard (and (disc-tree tree)
                              (pseudo-term-listp clause)
                              (pseudo-term-list-listp ac))))

; We compute a superset of all those clauses stored in tree which
; could subsume clause or which, when resolved with clause, could
; produce a new clause that subsumed clause.  If the key of a node
; does not occur+- in clause, then none of the clauses on the yes
; branch of the node can be relevant because all of the clauses
; on the yes branch contain+- the key.

  (cond ((eq (car tree) 'node)
         (cond ((or (extra-info-lit-p (cadr tree))
                    (member-equal-+- (cadr tree) clause))
                (find-clauses1 clause (caddr tree)
                               (find-clauses1 clause (cadddr tree) ac)))
               (t (find-clauses1 clause (cadddr tree) ac))))
        (t (append (cdr tree) ac))))

(defun find-clauses (clause tree)
  (find-clauses1 clause tree nil))

(defun remove-one-+- (x l)
  (cond ((null l) nil)
        ((equal x (car l)) (cdr l))
        ((complementaryp x (car l)) (cdr l))
        (t (cons (car l) (remove-one-+- x (cdr l))))))

(defun store-clause1 (clause undisc-lits tree)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (pseudo-term-listp undisc-lits)
                              (disc-tree tree))))
  (cond
   ((eq (car tree) 'node)
    (cond ((extra-info-lit-p (cadr tree))
           (list 'node
                 (cadr tree)
                 (store-clause1 clause
                                undisc-lits
                                (caddr tree))
                 (cadddr tree)))
          ((member-equal-+- (cadr tree) clause)
           (list 'node
                 (cadr tree)
                 (store-clause1 clause
                                (remove-one-+- (cadr tree) undisc-lits)
                                (caddr tree))
                 (cadddr tree)))
          (t (list 'node
                   (cadr tree)
                   (caddr tree)
                   (store-clause1 clause
                                  undisc-lits
                                  (cadddr tree))))))
   ((null undisc-lits)
    (cons 'tip (cons clause (cdr tree))))
   ((extra-info-lit-p (car undisc-lits))
    (store-clause1 clause (cdr undisc-lits) tree))
   (t (mv-let (with-lst without-lst)
              (filter-with-and-without (car undisc-lits) (cdr tree) nil nil)
              (store-clause1
               clause undisc-lits
               (list 'node (car undisc-lits)
                     (cons 'tip with-lst)
                     (cons 'tip without-lst)))))))

(defun store-clause (cl tree)

; Store-clause implements a specialized discrimination network for
; storing clauses during the subsumption/replacement phase of
; clausify.  Here the tree is either of the form:

; (NODE lit with-tree without-tree)

; or

; (TIP . clauses)

; A tree is said to contain a clause if that clause is a member of the clause
; list at some TIP in the tree.  Every clause in the with-tree of a NODE
; contains the node's lit either positively or negatively as an element.  No
; clause in the without-tree of a NODE contains the lit.

  (store-clause1 cl cl tree))

(defun substitute1-ac (new old seq acc)
  (declare (xargs :guard (and (true-listp acc)
                              (true-listp seq)
                              (member-equal old seq))))
  (cond
   ((endp seq)
    (er hard 'substitute
        "Attempted to substitute ~x0 for ~x1 into a sequence in which the ~
         latter was not an element."
        new old))
   ((equal old (car seq))
    (revappend acc (cons new (cdr seq))))
   (t
    (substitute1-ac new old (cdr seq) (cons (car seq) acc)))))

(defun substitute1 (new old seq)
  (declare (xargs :guard (and (true-listp seq)
                              (member-equal old seq))))
  (substitute1-ac new old seq nil))

(defun replace-clause1 (clause undisc-lits new-clause tree)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (pseudo-term-listp undisc-lits)
                              (disc-tree tree))))
  (cond
   ((eq (car tree) 'node)
    (cond ((member-equal-+- (cadr tree) clause)
           (list 'node
                 (cadr tree)
                 (replace-clause1 clause
                                  (remove-one-+- (cadr tree) undisc-lits)
                                  new-clause
                                  (caddr tree))
                 (cadddr tree)))
          (t (list 'node
                   (cadr tree)
                   (caddr tree)
                   (replace-clause1 clause
                                    undisc-lits
                                    new-clause
                                    (cadddr tree))))))
   ((member-equal clause (cdr tree))
    (cons (car tree) ; 'tip
          (substitute1 new-clause clause (cdr tree))))
   (t tree)))

(defun replace-clause (clause new-clause tree)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (disc-tree tree))))
  (replace-clause1 clause clause new-clause tree))

(defun extra-info-lits (cl acc)
  (cond ((endp cl) acc)
        ((extra-info-lit-p (car cl))
         (extra-info-lits (cdr cl) (cons (car cl) acc)))
        (t (extra-info-lits (cdr cl) acc))))

(defun merge-extra-info-lits (cl cl0 tree)

; cl0 is in tree.  We want to merge the extra-info-lit elements of cl into cl0.

  (let ((lits (extra-info-lits cl nil)))
    (cond (lits (replace-clause cl0 (rev-union-equal lits cl0) tree))
          (t tree))))

(defun subsumption-replacement-loop (todo done-tree again-flg)
  (declare (xargs :guard (and (pseudo-term-list-listp todo)
                              (disc-tree done-tree))))

; Precondition:  todo should have the shortest clauses first in order for this
; code to catch all possible subsumptions.  Use merge-sort-length to sort the
; input todo.

; Caution:  If there are tautologies in the input clause set, todo, then the
; output clause set may not be propositionally equivalent.  The output clause
; set will imply the input.  For example, let todo be
; ((A (NOT B) B)   ; c1
;  (A B))          ; c2
; Then c1 is a tautology.  However, it is used to replace c2 by (A), which
; then subsumes c1.  The output is thus ((A)).  But the input set is
; propositionally equivalent to ((A B)).

  (cond ((null todo)
         (cond
          (again-flg
           (cond
            ((time-limit5-reached-p ; nil, or throws
              "Out of time in subsumption (subsumption-replacement-loop).")
             nil)
            (t
             (subsumption-replacement-loop
              (merge-sort-length (sweep-clauses done-tree)) nil nil))))
          (t (sweep-clauses done-tree))))
        (t (mv-let (x cl0)
                   (find-subsumer-replacement
                    (car todo)
                    (find-clauses (car todo) done-tree))
                   (cond ((null x)
                          (subsumption-replacement-loop
                           (cdr todo)
                           (store-clause (car todo) done-tree)
                           again-flg))
                         ((eq x 'subsumed)
                          (subsumption-replacement-loop
                           (cdr todo)
                           (merge-extra-info-lits (car todo) cl0 done-tree)
                           again-flg))
                         (t (subsumption-replacement-loop
                             (cdr todo)
                             (store-clause (remove-one-complement (car x)
                                                                  (car todo))
                                           done-tree)
                             t)))))))

; Rockwell Addition: Same old lambda-exp arg.  Clausify is called in
; many places and now has a new last arg.  This will show up many
; times.

(defun clausify (term assumptions lambda-exp sr-limit)

; We return a conjunction of clauses equivalent to term under the assumptions
; given.  Assumptions must be nil (meaning no assumptions) or something
; generated by convert-clause-to-assumptions.  In the latter case, assumptions
; will start with the mark :ignore-when-converting-to-clause, which means that
; the assumptions in assumptions do not get transferred into the clauses built.

; If context is nil, then (bar (if test a b)) would clausify to two clauses,
; ((not test) (bar a)) and (test (bar b)).  But if (bar a) is assumed true in
; assumptions, e.g., assumptions is (:ignore-when-converting-to-clause (bar a))
; then the first clause above is recognized as true.  While the initial
; assumptions filter out literals and clauses they do not otherwise contribute;
; in particular, our answer is not a set of clauses representing context ->
; term.

; It would be nice for clausify to know all sorts of things, like type-set and
; the removal of trivial equivalences.  The trouble is that if we do that, we
; need to track what was done with ttrees.  But if clausify returns a ttree
; many of its callers have great difficulty accommodating it.  For example, in
; the translation of :by hints, there is no provision for recording or
; reporting the rules used to "translate" the hint into a clause.  For this
; reason, we've left clausify "dumb."

; Lambda-exp indicates whether we should go inside of lambdas.

  (declare (xargs :guard (pseudo-termp term)))
  (let ((clauses (pstk
                  (strip-branches term assumptions lambda-exp))))
    (cond
     ((or (null sr-limit) (<= (length clauses) sr-limit))
      (pstk
       (subsumption-replacement-loop
        (merge-sort-length
         clauses)
        nil
        nil)))
     (t clauses))))

; Now we get into the immediate subroutines of rewrite itself.

(defun find-rewriting-equivalence (lhs type-alist geneqv wrld ttree)

; We search type-alist for a binding to *ts-t* of a term of the form
; (equiv lhs rhs), where equiv is a refinement of geneqv and lhs is as
; given in the arguments.  If we find it, we return the entire binding
; and a ttree in which we have added the name of the :CONGRUENCE rule
; as a 'lemma.  Equiv is known to be an equivalence relation and as
; such we know that lhs is bigger than rhs in the term-order.

; A heuristic question arises.  Suppose we have several such
; equiv-terms for lhs, all different refinements of geneqv.  What do
; we do?  Well, we will chose the first we find.  Ugh.  But suppose
; they are refinements of each other.  E.g., we have three hypotheses,
; (set-equal b a1), (list-equal b a2) and (equal b a3), where
; list-equal is a refinement of set-equal.  Then because we know, for
; every equivalence relation equiv, that iff is preserved by equiv in
; both slots of equiv, we will eventually rewrite the b in each of the
; hypotheses above, maintaining the equivalence relation concerned.
; Thus, in (set-equal b a1) we will rewrite b maintaining set-equal
; and will choose either to replace b by a2 or a3, since list-equal
; and equal are both refinements.  The point is that ultimately in the
; rewriting process the three hypotheses will become (set-equal b a3),
; (list-equal b a3) and (equal b a3) because the finest refinement
; will ultimately get to rewrite each of the others.

; No Change Loser on the ttree

  (cond ((null type-alist) (mv nil nil ttree))
        (t (let ((entry (car type-alist)))
             (cond
              ((not (variablep (car entry)))

; This code is a bit contorted because we have found (specifically, in
; (verify-guards exec-send ...) in community book
; books/workshops/2000/lusk-mccune/lusk-mccune-final/stepproc1.lisp) that the
; ts= call below is noticeably more efficient than the (ts-disjointp ...).

               (let ((rw-equivp (cond ((and (eq (ffn-symb (car entry))
                                                'hide)
                                            (not (variablep (fargn (car entry)
                                                                   1)))
                                            (eq (ffn-symb (fargn (car entry)
                                                                 1))
                                                'rewrite-equiv))
                                       (car entry)))))
                 (cond
                  ((if rw-equivp
                       (ts-disjointp (cadr entry) *ts-nil*)
                     (ts= (cadr entry) *ts-t*))
                   (let* ((equiv-term
                           (cond (rw-equivp (fargn (fargn (car entry) 1)
                                                   1))
                                 (t (car entry))))
                          (rune (and (not (flambdap (ffn-symb equiv-term)))
                                     (geneqv-refinementp (ffn-symb equiv-term)
                                                         geneqv wrld))))
                     (cond ((and rune
                                 (equal (fargn equiv-term 1) lhs))
                            (mv rw-equivp
                                equiv-term
                                (cons-tag-trees
                                 (cddr entry)
                                 (push-lemma rune ttree))))
                           (t (find-rewriting-equivalence
                               lhs (cdr type-alist) geneqv wrld ttree)))))
                  (t (find-rewriting-equivalence
                      lhs (cdr type-alist) geneqv wrld ttree)))))
              (t (find-rewriting-equivalence
                  lhs (cdr type-alist) geneqv wrld ttree)))))))

(defun obj-table (term ts ts-ttree obj geneqv wrld ttree)

; This function is (mv term' ttree'), where term' is equivalent modulo geneqv
; (see the essay on Equivalence, Refinements and Congruence- based Rewriting)
; to term and ttree' includes ttree and may include additional stuff.
; Depending on ts, the type-set of term (which is supported by the ts-ttree),
; we may coerce term to 0, 1, t, or nil.

; Note: This function used to depend on the objective, obj, of the rewrite.
; When obj was nil, that dependency prevented obj-table from reducing term to t
; when term was known to have non-nil type-set.  That, in turn, caused
; relieve-hyp to force (not term), even though (not term) was known nil.  We
; now reduce term to t, nil or 0 as appropriate by the geneqv and ts,
; regardless of obj.  However, we have left the obj parameter in place, in case
; we someday want to restore dependency on it.

  (declare (ignore obj))
  (cond
   ((ts= ts *ts-t*)
    (mv *t*

; At one time we tested whether (equal term *t*), so that when this holds we
; can avoid a call of cons-tag-trees.  However, we only call obj-table on
; non-quotep terms, so we know that this test will be false.

        (cons-tag-trees ts-ttree ttree)))
   ((ts= ts *ts-nil*)
    (mv *nil*
        (cons-tag-trees ts-ttree ttree)))
   ((ts= ts *ts-zero*)
    (mv *0*
        (cons-tag-trees ts-ttree ttree)))

; After a new type-set bit for the set {1}, we considered adding a case for
; (ts= ts *ts-one*), to return (mv *1* (cons-tag-trees ts-ttree ttree)) in that
; case to coerce the term to '1.  However, some books failed.  For example, a
; problem in community book books/demos/proofs/tightness-lemma-proof.lisp
; simplifies to the following example.

;   (defun i-from (n len)
;     (cond ((zp len) nil)
;           (t (cons n
;                    (i-from (1+ n) (1- len))))))
;   (defthm <-0-+-negative-1
;     (iff (< 0 (+ (- y) x)) (< y x)))
;   (defthm consp-i-from
;     (equal (consp (i-from i len))
;            (not (zp len))))

; The problem was presumably that under a proof by induction, obj-table was
; replacing the goal

;   (IMPLIES (AND (NOT (ZP LEN)) (ZP (+ -1 LEN)))
;            (CONSP (I-FROM I LEN)))

; by the goal

;   (IMPLIES (AND (NOT (ZP LEN)) (<= LEN 1))
;            (CONSP (I-FROM I 1)))

; and although the term (I-FROM I LEN) was a term to be expanded under
; induction, (I-FROM I 1) was not.  We had 27 other failures that might have
; been due to this same problem, but we didn't investigate them.  Instead, we
; are omitting a case here for *ts-one*.

; We have also had problems when including this (deleted) case, depending on
; other heuristics involving *ts-one*, for the lemma symbolic-computation in
; models/jvm/m5/demo.lisp, projects/symbolic/m5/demo.lisp, and
; books/workshops/2003/moore_vcg/support/.  Sol Swords noticed that a
; forward-chaining lemma, (implies (and (integerp (+ 1 k)) (acl2-numberp k))
; (integerp k)), solves that problem; but without this case, we don't need that
; lemma.

; For more discussion regarding *ts-one*, see the Essay on Strong Handling of
; *ts-one*.

   (t (let ((rune (geneqv-refinementp 'iff geneqv wrld)))
        (cond
         (rune
          (cond
           ((ts-subsetp *ts-nil* ts)
            (mv term ttree))
           (t (mv *t*
                  (push-lemma rune
                              (cons-tag-trees ts-ttree
                                              ttree))))))
         (t (mv term ttree)))))))

(defun rewrite-solidify-rec (bound term type-alist obj geneqv ens wrld ttree
                                   pot-lst pt)
  (declare (type (unsigned-byte 29) bound))
  (cond
   ((quotep term)
    (cond ((equal term *nil*) (mv *nil* ttree))
          (t (let ((rune (geneqv-refinementp 'iff geneqv wrld)))
               (cond (rune
                      (mv *t* (push-lemma rune ttree)))
                     (t (mv term ttree)))))))
   ((ffn-symb-p term 'if)

; Is this case important?  It doesn't seem so, and we were tempted to delete it
; when we modified find-rewriting-equivalence after Version_3.0.1 to look for
; calls of (hide ('rewrite-equiv ..)).  But at one time, deletion caused
; failure of lemma lop3-34 in community book
; books/rtl/rel5/support/lop3-proofs.lisp, so we leave this case for backward
; compatibility.

    (mv term ttree))
   ((and (ffn-symb-p term 'hide)
         (let ((e (fargn term 1)))
           (case-match e
             (('rewrite-equiv (equiv x x))
              (prog2$ x ; avoid "not used" error
                      (equivalence-relationp equiv wrld)))
             (& nil))))

; Here we rewrite terms of the form (hide (rewrite-equiv (equiv x x))) to true,
; where equiv is a known equivalence relation.  This is clearly sound.  It
; avoids some loops.  The following example, based closely on one sent by Dave
; Greve, loops in ACL2 Version_3.2 but not in later versions (which have this
; fix).  If you trace rewrite and rewrite-solidify in TEST below, you'll see
; that where formerly (HIDE (REWRITE-EQUIV (EQUAL RES (GOO X)))) rewrote (with
; RES bound to (GOO X), and thanks to running BETA-REDUCE-HIDE-WRAPPER), to
; (HIDE (REWRITE-EQUIV (EQUAL (GOO X) (GOO X)))) now instead it rewrites to
; *T*.


;     (DEFEVALUATOR UNHIDE-EVAL UNHIDE-EVAL-LIST
;       ((IF X Y Z) (HIDE X)))
;
;     (DEFUN BETA-REDUCE-HIDE-WRAPPER (X)
;       (IF (EQUAL X '(HIDE ((LAMBDA (RES X)
;                                    (REWRITE-EQUIV (EQUAL RES (GOO X))))
;                            (GOO X)
;                            X)))
;           '(HIDE (REWRITE-EQUIV (EQUAL (GOO X) (GOO X))))
;           X))
;
;     (DEFTHM
;       *META*-BETA-REDUCE-HIDE
;       (IMPLIES (PSEUDO-TERMP TERM)
;                (EQUAL (UNHIDE-EVAL TERM A)
;                       (UNHIDE-EVAL (BETA-REDUCE-HIDE-WRAPPER TERM)
;                                    A)))
;       :HINTS (("Goal" :EXPAND (:FREE (X) (HIDE X))
;                :IN-THEORY (ENABLE UNHIDE-EVAL-CONSTRAINT-0)))
;       :RULE-CLASSES ((:META :TRIGGER-FNS (HIDE))))
;
;     (DEFUN GOO (X) X)
;     (DEFUN FOO (X) (GOO X))
;     (IN-THEORY (DISABLE FOO GOO))
;
;     (DEFUN CONCLUSION (X)
;       (LET ((RES (FOO X)))
;            (AND
;             (HIDE (REWRITE-EQUIV (EQUAL RES (GOO X))))
;             (INTEGERP RES))))
;
;     (DEFTHM TEST
;       (IMPLIES
;        (HIDE (REWRITE-EQUIV (EQUAL (FOO X) (GOO X))))
;        (CONCLUSION X))
;       :HINTS (("GOAL" :IN-THEORY (DISABLE CONCLUSION)
;                :DO-NOT '(PREPROCESS))
;               (AND STABLE-UNDER-SIMPLIFICATIONP
;                    '(:IN-THEORY (ENABLE CONCLUSION)))))

    (mv *t* (push-lemma
             (fn-rune-nume 'hide nil nil wrld)
             (push-lemma
              (fn-rune-nume 'rewrite-equiv nil nil wrld)

; We do not track the use of equivalence relations; see comment in
; equivalence-relationp.

              ttree))))
   (t
    (mv-let (rw-equivp eterm ttree)
            (find-rewriting-equivalence term type-alist geneqv wrld ttree)
            (cond
             (eterm

; If rw-equivp is true, then the equivalence is from a call of rewrite-equiv.
; The following recursive call is guaranteed to be made on a term that is
; smaller according to term-order, by the Third invariant on type-alists.  See
; the Essay on the Invariants on Type-alists, and Canonicality.

              (let ((new-bound
                     (cond
                      ((not rw-equivp)
                       bound)
                      ((zpf bound)
                       (prog2$ (er hard 'rewrite-solidify
                                   "You appear to have hit the unusual case ~
                                    of a loop in the replacement of terms by ~
                                    equivalent terms using rewrite-equiv.  ~
                                    The term ~x0 is involved in the loop."
                                   rw-equivp)
                               0))
                      (t (1-f bound)))))
                (declare (type (unsigned-byte 29) new-bound))
                (rewrite-solidify-rec new-bound (fargn eterm 2) type-alist
                                      obj geneqv ens wrld ttree
                                      pot-lst pt)))
             (t (mv-let (ts ts-ttree)

; See the comment just after rewrite-solidify for some historical waffling.

                        (cond ((not (eq obj '?))
                               (type-set term nil t type-alist
                                         ens wrld nil pot-lst pt))
                              (t (assoc-type-alist term type-alist wrld)))
                        (if (null ts)
                            (mv term ttree)
                          (obj-table term ts ts-ttree
                                     obj geneqv wrld ttree)))))))))

(defconst *rewrite-equiv-solidify-iteration-bound*

; The number below is pretty generous, since it bounds the number of recursive
; calls of rewrite-solidify-rec on behalf of rewrite-equiv.

  100)

(defun rewrite-solidify (term type-alist obj geneqv ens wrld ttree
                               pot-lst pt)
  (rewrite-solidify-rec *rewrite-equiv-solidify-iteration-bound* term
                        type-alist obj geneqv ens wrld ttree pot-lst pt))

; Comment on Historical Waffling over Calling Type-Set in Rewrite-Solidify
;
; Back in v1-7 we called
; (type-set term nil force-flg type-alist nil ens wrld nil)
; here, where force-flg was passed into rewrite-solidify.
;
; We abandoned that in v1-8 and most of v1-9 and replaced it with a simple
; lookup of term in the type-alist,
;
; (assoc-type-alist term type-alist wrld)
;
; and marked the occasion by writing the following comment:
;
; ; At one time we called type-set here.  As a result, the prover could simplify
; ;
; ; (thm (implies (and (not (< y 0))
; ;                    (rationalp y)
; ;                    (not (equal 0 y)))
; ;               (equal aaa (< 0 y))))
; ;
; ; to
; ;
; ; (implies (and (not (< y 0))
; ;               (rationalp y)
; ;               (not (equal 0 y)))
; ;          (equal aaa t))
; ;
; ; However, in the interest of performance we have decided to avoid a full-blown
; ; call of type-set here.  You get what you pay for, perhaps.
;
; However, then Rich Cohen observed that when trying to relieve a hypothesis in
; a lemma, if the hyp rewrote to an explicit cons expression then we failed to
; recognize that it is non-nil!  Here is a thm that failed for that reason:
;
;  (defstub foo (x a) t)
;  (defaxiom lemma
;   (implies (member x a) (equal (foo x a) x)))
;  (thm (equal (foo x (cons x y)) x))
;
; We have decided to revert to the use of type-set in rewrite-solidify, but
; only when we have an objective of t or nil.  Under this condition we use
; force-flg nil and dwp t.  We tried the div proofs with force-flg t here
; and found premature forcing killed us.

; On 1/17/2019, after Version_8.1, we tried modifying rewrite-solidify-rec to
; call type-set unconditionally, not merely when (not (eq obj '?)).  There were
; 46 failures in the "everything" regression, which we killed before it
; completed since there were three very-long running certifications still in
; progress (about 3 hours each).  Among those, we noticed
; books/nonstd/workshops/2017/cayley/cayley1c.lisp, whose certification went
; far enough for us to see the the proof of 8-COMPOSITION-LAW completed but
; took 7560.97 seconds, far exceeding the 6.49 seconds taken in a recent run.
; It thus seemed obvious that such a change would likely cause massive changes
; to be necessary not only in the community books, but also in proprietary
; books elsewhere.

(defun rewrite-if11 (term type-alist geneqv wrld ttree)
  (mv-let (ts ts-ttree)
    (look-in-type-alist term type-alist wrld)
    (cond ((ts= ts *ts-nil*)
           (mv *nil* (cons-tag-trees ts-ttree ttree)))
          ((and (equal geneqv *geneqv-iff*)
                (ts-disjointp ts *ts-nil*))
           (mv *t* (cons-tag-trees ts-ttree ttree)))
          (t
           (mv term ttree)))))

(defstub rewrite-if-avoid-swap () => *)

(defattach (rewrite-if-avoid-swap constant-nil-function-arity-0))

(defun rewrite-if1 (test left right swapped-p type-alist geneqv ens ok-to-force
                         wrld ttree)

; Test, left and right are rewritten terms.  They were rewritten under
; appropriate extensions of type-alist.  We implement the following
; rules here:

; (if x y y) = y
; (if x x nil) = x
; (if x t nil) = x, if x is Boolean

; Note: In Version  2-5 days, the following comment was in type-set:
; Note: Because IF's are not bound on the type-alist, we need not ....

; This was not true then, nor is it true now (Version  2-7).  Therefore,
; when the above three rules fail we try looking up `(if ,test ,left ,right)
; on the type-alist.  This is done in rewrite-if11.

; Once upon a time we used known-whether-nil to determine if right was
; nil under type-alist and wrld.  But since right is the result of
; rewriting, we claim that if it is known to be nil then it is in fact
; *nil* because of rewrite-solidify.  So we no longer use
; known-whether-nil here.

  (flet ((if-call (test left right swapped-p)
                  (cond ((and swapped-p (rewrite-if-avoid-swap))
                         (mcons-term* 'if (dumb-negate-lit test) right left))
                        (t (mcons-term* 'if test left right)))))
    (cond ((equal left right) (mv left ttree))
          ((equal right *nil*)
           (cond
            ((equal test left)
             (mv test ttree))
            ((equal left *t*)
             (mv-let (ts ts-ttree)
               (type-set test ok-to-force nil type-alist ens wrld ttree nil nil)
               (cond ((ts-subsetp ts *ts-boolean*)
                      (mv test ts-ttree))
                     (t (rewrite-if11 (if-call test left right swapped-p)
                                      type-alist geneqv wrld ttree)))))
            (t (rewrite-if11 (if-call test left right swapped-p)
                             type-alist geneqv wrld ttree))))
          ((and swapped-p
                (equal left *nil*)
                (equal right *t*)
                (rewrite-if-avoid-swap))
           (mv (fcons-term* 'not test) ttree))
          (t (rewrite-if11 (if-call test left right swapped-p)
                           type-alist geneqv wrld ttree)))))

; Rockwell Addition: In the not-to-be-rewritten test below, we used to
; create an instantiation with sublis-var.  Now we chase var bindings.
; But there is a subtlety with constants created by sublis-var.

(defun member-equal-mod-alist (term1 alist1 term2-lst)
  (cond ((endp term2-lst) nil)
        ((equal-mod-alist term1 alist1 (car term2-lst))
         t)
        (t (member-equal-mod-alist term1 alist1 (cdr term2-lst)))))

(defun not-to-be-rewrittenp1 (fn lst)

; This function determines whether fn is the ffn-symb of any term on
; lst.  We assume lst is a true list of non-variablep non-quotep
; terms.

  (cond ((null lst)
         nil)
        ((equal fn (ffn-symb (car lst))) ; Both may be LAMBDAs.
         t)
        (t (not-to-be-rewrittenp1 fn (cdr lst)))))

(defun not-to-be-rewrittenp (term alist terms-to-be-ignored-by-rewrite)

; We assume term is a nonvariable non-quotep and that
; terms-to-be-ignored-by-rewrite contains no vars or quoteps.  Let
; term' be (sublis-var alist term).  If term' is a member of
; terms-to-be-ignored-by-rewrite we return term' else nil.  We have
; a faster preliminary check, namely, whether terms-to-be-ignored-
; by-rewrite contains any terms with the same top-level function
; symbol as term.

  (cond ((not-to-be-rewrittenp1 (ffn-symb term)
                                terms-to-be-ignored-by-rewrite)
         (member-equal-mod-alist term alist
                                 terms-to-be-ignored-by-rewrite))
        (t nil)))

(defun rewrite-recognizer (recog-tuple arg type-alist ens force-flg wrld ttree
                           pot-lst pt)

; This function returns (mv term' ttree'), where term' is equivalent
; to (fn arg), where fn is the fn field of recog-tuple, and ttree' is
; an extension of ttree that supports whatever was done to reduce (fn
; arg) to term'.  (We use ``ttree+'' for ttree' below.  Observe that we
; sometimes return ttree+ and other times return ttree.)

  (mv-let (ts ttree+)
          (type-set arg force-flg nil type-alist ens wrld ttree pot-lst pt)
    (cond
     ((ts-intersectp ts (access recognizer-tuple recog-tuple :true-ts))
      (cond ((ts-intersectp ts (access recognizer-tuple recog-tuple :false-ts))
             (mv (mcons-term* (access recognizer-tuple recog-tuple :fn)
                              arg)
                 ttree))
            (t (mv *t*
                   (push-lemma (access recognizer-tuple recog-tuple :rune)
                               ttree+)))))

; Once upon a time we had:

;    ((ts-intersectp ts (access recognizer-tuple recog-tuple :false-ts))
;     (mv *nil* ttree+))
;    (t
;     (mv (mcons-term* (access recognizer-tuple recog-tuple :fn)
;                      arg)
;         ttree))

; here.  But we noticed that if the type-set of arg, ts, does not
; intersect true-ts then we know that (not (fn arg)):  either (fn arg)
; or (not (fn arg)) and we know the former implies that ts a subset of
; true-ts.  Since it is not, the latter must hold.  A consequence of
; this insight is that we can see that if ts does not intersect
; true-ts then it MUST intersect false-ts.

     (t (mv *nil*
            (push-lemma (access recognizer-tuple recog-tuple :rune)
                        ttree+))))))

; In a departure from Nqthm, we use a lexicographic order on lists of
; terms for the loop-stopping algorithm.  This change was motivated by
; an example in which there were two variables involved in the
; loop-stopper, and one of the corresponding actuals was unchanged.
; Consider for example a rewrite rule like

; (equal
;  (variable-update var1
;                   val1 (variable-update var2 val2 vs))
;  (variable-update var2
;                   val2 (variable-update var1 val1 vs)))

; which has a loop-stopper of ((val1 . val2) (var1 . var2)), and could
; be applied where val1 and val2 are both x but var2 is instantiated
; by a term that precedes the instantiation of var1 in the term-order.
; Nqthm's loop stopper would prevent this application of the rule, but
; the implementation below allows it.

(defun remove-invisible-fncalls (term invisible-fns)

; Given a term and a list of unary function symbols considered invisible,
; strip off all the invisible outermost function symbols from the term.

  (cond
   ((or (variablep term)
        (fquotep term)
        (flambda-applicationp term))
    term)
   ((member-eq (ffn-symb term) invisible-fns)
    (remove-invisible-fncalls (fargn term 1) invisible-fns))
   (t term)))

(defun term-order+ (x1 x2 invisible-fns)

; See the doc string for loop-stopper to find an implicit description
; of this function.  See the comment below for a proof that this
; function is a total order, provided term-order is a total order.

  (let ((x1-guts (remove-invisible-fncalls x1 invisible-fns))
        (x2-guts (remove-invisible-fncalls x2 invisible-fns)))
    (cond
     ((equal x1-guts x2-guts)
      (term-order x1 x2))
     (t
      (term-order x1-guts x2-guts)))))

; We wish to prove that term-order+ is a total ordering on terms, which,
; recall, means that it is antisymmetric, transitive, and enjoys the trichotomy
; property.  However, because term-order+ and its main subroutine, term-order,
; are :program functions we cannot do this directly without reclassifying them.
; In addition, we would first need to prove the lemma that term-order is a
; total ordering.  Rather than undertake such a large proof effort, we attack a
; slightly different problem.  The basic idea is to constrain the new functions
; xtermp, xterm-order, and xremove-invisible-fncalls to have the properties we
; are willing to assume about the corresponding :program functions.  In
; particular, we assume that xterm-order is a total ordering on xtermps and
; that xremove-invisible-fncalls preserves xtermp.  Then we define xterm-order+
; analogously to the definition above of term-order+ and we prove that
; xterm-order+ is a total ordering on xterms.


; Introduce xtermp, xterm-order and xremove-invisible-fncalls by constraint.
; Observe that in the three properties characterizing xterm-order as a total
; ordering we restrict our claims to the cases where only xtermps are involved.
; We also require that xremove-invisible-fncalls preserve xtermp.

;   (encapsulate (((xtermp *) => *)
;                 ((xterm-order * *) => *)
;                 ((xremove-invisible-fncalls * *) => *))

; We witness xtermp with rationalp, xterm-order with <= on the rationals,
; and xremove-invisible-fncalls by the identify function.

;    (local (defun xtermp (x) (rationalp x)))
;    (local (defun xterm-order (x y)
;             (and (xtermp x) (xtermp y) (<= x y))))
;    (local (defun xremove-invisible-fncalls (x lst) (declare (ignore lst)) x))

; Here we establish that xremove-invisible-fncalls preserves xtermp.

;    (defthm xtermp-xremove-invisible-fncalls
;      (implies (xtermp x) (xtermp (xremove-invisible-fncalls x lst))))

; We now prove the three total ordering properties.  In each case we
; state the property elegantly and then store it as an effective
; rewrite rule.

;    (defthm antisymmetry-of-xterm-order
;      (implies (and (xtermp x)
;                    (xtermp y)
;                    (xterm-order x y)
;                    (xterm-order y x))
;               (equal x y))
;
;      :rule-classes
;      ((:rewrite :corollary
;                 (implies (and (xtermp x)
;                               (xtermp y)
;                               (xterm-order x y)
;                               (xterm-order y x))
;                          (equal (equal x y) t)))))
;
;    (defthm transitivity-of-xterm-order
;      (implies (and (xtermp x)
;                    (xtermp y)
;                    (xtermp z)
;                    (xterm-order x y)
;                    (xterm-order y z))
;               (xterm-order x z))
;
;      :rule-classes
;      ((:rewrite :corollary
;                 (implies (and (xtermp x)
;                               (xterm-order x y)
;                               (xtermp y)
;                               (xtermp z)
;                               (xterm-order y z))
;                          (xterm-order x z)))))
;
;    (defthm trichotomy-of-xterm-order
;      (implies (and (xtermp x)
;                    (xtermp y))
;               (or (xterm-order x y) (xterm-order y x)))
;
;      :rule-classes
;      ((:rewrite :corollary
;                 (implies (and (xtermp x)
;                               (xtermp y)
;                               (not (xterm-order x y)))
;                          (xterm-order y x))))))

; Introduce the derived order, xterm-order+, that transduces with
; xremove-invisible-fncalls.  This is exactly analogous to the definition
; of term-order+ above.

;    (defun xterm-order+ (x1 x2 invisible-fns)
;     (let ((x1-guts (xremove-invisible-fncalls x1 invisible-fns))
;           (x2-guts (xremove-invisible-fncalls x2 invisible-fns)))
;       (cond
;        ((equal x1-guts x2-guts)
;         (xterm-order x1 x2))
;        (t
;         (xterm-order x1-guts x2-guts)))))

; Prove the three properties of xterm-order+, restricted to the xtermp cases.

;    (defthm antisymmetry-of-xterm-order+
;     (implies (and (xtermp x)
;                   (xtermp y)
;                   (xterm-order+ x y invisible-fns)
;                   (xterm-order+ y x invisible-fns))
;              (equal x y))
;     :rule-classes nil)
;
;    (defthm transitivity-of-xterm-order+
;     (implies (and (xtermp x)
;                   (xtermp y)
;                   (xtermp z)
;                   (xterm-order+ x y invisible-fns)
;                   (xterm-order+ y z invisible-fns))
;              (xterm-order+ x z invisible-fns)))
;
;    (defthm trichotomy-of-xterm-order+
;     (implies (and (xtermp x)
;                   (xtermp y))
;              (or (xterm-order+ x y invisible-fns)
;                  (xterm-order+ y x invisible-fns)))
;     :rule-classes nil)

(defun invisible-fns (fns alist acc)

; Fns is a list of function symbols.  Alist is an alist that maps each function
; symbol to a (possibly empty) list of corresponding invisible unary function
; symbols.  Acc should be t initially.  We return the intersection of the lists
; of invisible functions associated with each function in the list fns.

; We understand "intersection" to mean NIL when intersecting the empty list of
; lists; recall the set-theoretic definition of the intersection of a family of
; sets as containing those elements of the union of that family that belong to
; every set in that family.

  (declare (xargs :guard (and (symbol-listp fns)
                              (or (true-listp acc)
                                  (eq acc t)))))
  (cond
   ((null fns)
    (if (eq acc t) nil acc))
   ((eq acc t)
    (invisible-fns (cdr fns)
                   alist
                   (cdr (assoc-eq (car fns) alist))))
   ((null acc)

; This case is a minor optimization that could be omitted.

    nil)
   (t
    (invisible-fns (cdr fns)
                   alist
                   (intersection-eq (cdr (assoc-eq (car fns) alist))
                                    acc)))))

(defun loop-stopperp-rec (loop-stopper sbst wrld)

; Only call this at the top level when loop-stopper is non-nil.

  (cond
   ((null loop-stopper) nil)
   (t
    (let ((pre (cdr (assoc-eq (car (car loop-stopper)) sbst)))
          (post (cdr (assoc-eq (cadr (car loop-stopper)) sbst))))
      (cond
       ((equal pre post)
        (loop-stopperp-rec (cdr loop-stopper) sbst wrld))
       (t (term-order+ post pre
                       (invisible-fns
                        (cddr (car loop-stopper))
                        (invisible-fns-table wrld)
                        t))))))))

(defun loop-stopperp (loop-stopper sbst wrld)
  (or (null loop-stopper)
      (loop-stopperp-rec loop-stopper sbst wrld)))

(defrec rewrite-rule (rune nume hyps equiv lhs rhs
                           subclass heuristic-info

; Warning: Do not change the cheap flag, currently nil, without revisiting
; macro get-rule-field.

; The backchain-limit-lst must be nil, a natp, or a list of these of the same
; length as hyps.  For subclass 'meta, only the first two of these are legal.
; Otherwise, only the first and third of these are legal.

                           backchain-limit-lst

; For subclass 'backchain or 'abbreviation, var-info is t or nil according to
; whether or not there are free variables on the left-hand side of the rule.
; For subclass 'definition, var-info is a list that positionally associates
; each argument of lhs with the number of its occurrences in rhs.  Var-info is
; ignored for subclass 'meta.

                           var-info
                           .

; The match-free field should be :all or :once if there are free variables in
; the hypotheses, else nil.

                           match-free)

; See the warning above.

  nil)

; There are five subclasses of rewrite rule, distinguished by the :subclass
; slot.

; 'backchain - the traditional rewrite rule.  In this case, :heuristic-info is
;   the loop-stopper for the rule: a list of elements of the form (x y . fns),
;   indicating that in replacing lhs by rhs (the binding of) y moves forward to
;   the spot occupied by (the binding of) x, and that x and y only appear on
;   the left-hand side as arguments to functions in fns.  Thus, to prevent
;   loops we adopt the heuristic convention of replacing lhs by rhs only if
;   each y is smaller than the corresponding x, with respect to functions that
;   are considered "invisible" if they are invisible with respect to every
;   function in fns.

; 'abbreviation - the special case where there are no hyps, a nil loop-stopper,
;   and the rhs satisfies the abbreviationp predicate.  Heuristic-info is
;   irrelevant here.  Non-recursive definitions whose bodies are abbreviationps
;   are stored this way rather than as :subclass 'definition.

; 'meta - a rule justified by a metatheorem.  In this case, the lhs is the
;   metafunction symbol to be applied, and hyps is a function of one (term)
;   argument that generates a hypothesis for the metatheorem.  In this case the
;   :heuristic-info is of the form (name fn thm-name1 hyp-fn thm-name2)
;   . combined-arities-alist); see rewrite-with-lemma.

;   Rockwell Addition: The recursivep property used to be the fn name if the
;   fn in question was singly recursive.  Now it is a singleton list (fn).

; 'definition - a rule implementing a non-abbreviational definitional equation.
; In this case :heuristic-info is the pair (recursivep . controller-alist)
; where recursivep is nil (if this is a nonrec definition) or a truelist of
; symbols naming all the fns in the ``clique'' (singly recursive functions have
; a singleton list as their recursivep property); and controller-alist is an
; alist pairing each fn named in recursivep to a mask of t's and nil's in 1:1
; correspondence with the formals of the fn and indicating with t's which
; arguments control the recursion for this definition.

; 'rewrite-quoted-constant - rewrite rules that only apply to evgs.  See the
;  Essay on Rewriting Quoted Constants.  In this case, :heuristic-information
;  is a list (n . loop-stopper), where n is a natural number that the rule is of
;  Form [n] as discussed in the essay.

(defun relevant-ground-lemmas (hyp wrld)
  (mv-let (not-flg hyp)
          (strip-not hyp)
          (declare (ignore not-flg))
          (cond
           ((variablep hyp) nil)
           ((fquotep hyp) nil)
           ((flambda-applicationp hyp) nil)
           (t (getpropc (ffn-symb hyp) 'lemmas nil wrld)))))

(defun search-ground-units1
  (hyp unify-subst lemmas type-alist ens force-flg wrld ttree)
  (cond ((null lemmas) (mv nil unify-subst ttree nil))
        ((and (enabled-numep (access rewrite-rule (car lemmas) :nume) ens)
              (not (eq (access rewrite-rule (car lemmas) :subclass) 'meta))
              (null (access rewrite-rule (car lemmas) :hyps))
              (not (access rewrite-rule (car lemmas) :var-info))
              (geneqv-refinementp (access rewrite-rule (car lemmas) :equiv)
                                  *geneqv-iff*
                                  wrld))

; The tests above select enabled, non-meta, unconditional lemmas of
; the form (equiv lhs rhs), where equiv is a refinement of iff and lhs
; has no variables in it.  We do not know that rhs has no variables in
; it, but if it does, they can clearly be instantiated to whatever we
; wish and we will act as though they are instantiated with the
; corresponding variables of our current problem.  We now want to know
; if rhs is non-nil.  If it is, this lemma may be a way to establish
; hyp.

         (mv-let
          (knownp nilp nilp-ttree)
          (known-whether-nil (access rewrite-rule (car lemmas) :rhs)
                             type-alist
                             ens
                             force-flg
                             nil ; dwp
                             wrld
                             ttree)

; Observe that nilp-ttree extends ttree.  We may use either, depending on
; how things work out.

          (cond
           ((and knownp (not nilp))
            (mv-let (ans unify-subst)
                    (one-way-unify1 hyp
                                    (access rewrite-rule (car lemmas) :lhs)
                                    unify-subst)
                    (cond (ans
                           (let ((rune (access rewrite-rule (car lemmas) :rune)))
                             (with-accumulated-persistence
                              rune
                              (flg final-unify-subst final-ttree final-lemmas)
                              t
                              (mv t
                                  unify-subst
                                  (push-lemma (geneqv-refinementp
                                               (access rewrite-rule (car lemmas) :equiv)
                                               *geneqv-iff*
                                               wrld)
                                              (push-lemma rune nilp-ttree))
                                  (cdr lemmas)))))
                          (t (search-ground-units1
                              hyp unify-subst
                              (cdr lemmas)
                              type-alist ens force-flg wrld ttree)))))
           (t (search-ground-units1 hyp unify-subst
                                    (cdr lemmas)
                                    type-alist ens force-flg wrld ttree)))))
        (t (search-ground-units1 hyp unify-subst
                                 (cdr lemmas)
                                 type-alist ens force-flg wrld ttree))))

(defun search-ground-units
  (hyp unify-subst type-alist ens force-flg wrld ttree)

; This function is like lookup-hyp except we search through the ground unit
; rewrite lemmas.  We are a No-Change Loser with three values: the win flag,
; the new unify-subst, and a new ttree.

  (let ((lemmas (relevant-ground-lemmas hyp wrld)))
    (mv-let (winp unify-subst ttree rest-lemmas)
            (search-ground-units1
             hyp unify-subst lemmas type-alist ens force-flg wrld ttree)
            (declare (ignore rest-lemmas))
            (mv winp unify-subst ttree))))

(defun if-tautologyp (term)
  (declare (xargs :guard (pseudo-termp term)))

; This function returns T or NIL according to whether TERM is or is
; not an if-tautologyp.  A term is an if-tautology provided that under
; all (a) assignments of functions to the non-IF function symbols in
; the term and (b) assignments of objects to the variables in the
; term, the value of the term, (using the usual interpretation of IF
; and QUOTE and any Boolean commutative interpretations for EQUAL and
; IFF) is non-NIL. Every if-tautology is true, but one cannot conclude
; from the fact that a term is not an if-tautologyp that it is not
; true!  Note that we do not attach any ``semantics'' to the built-ins
; besides IF, QUOTEd objects, and the little we know about EQUAL and
; IFF.  For example, (IF (EQUAL A B) (EQUAL B A) 'T) is an
; if-tautology, but (IF (equiv A B) (equiv B A) 'T) for any symbol
; equiv other than EQUAL and IFF is not.

  (posp (if-interp (splice-instrs (if-compile term t nil nil))
                   nil nil nil nil

; The choice of 100000 below is rather arbitrary, determined by
; experimentation.  It is the limit for the number of if-interp steps.  It is
; probably fair to view this limit as a hack, but after all, Boolean
; decidability is NP-hard.

                   100000)))

(mutual-recursion

; Warning: For both functions in this nest, fns should be a subset of
; the keys of *bbody-alist*.  See the error related to
; *bbody-alist* in chk-acceptable-definition-install-body.

(defun expand-some-non-rec-fns (fns term wrld)

; We forcibly expand all calls in term of the fns in fns.  They better
; all be non-recursive or this may take a while.

; We assume that fns is a subset of the keys of *bbody-alist*.

  (cond ((variablep term) term)
        ((fquotep term) term)
        (t (let ((args (expand-some-non-rec-fns-lst fns (fargs term) wrld)))
             (cond ((member-equal (ffn-symb term) fns)
                    (subcor-var (formals (ffn-symb term) wrld)
                                args
                                (bbody (ffn-symb term))))
                   (t (cons-term (ffn-symb term) args)))))))

(defun expand-some-non-rec-fns-lst (fns lst wrld)
  (cond ((null lst) nil)
        (t (cons (expand-some-non-rec-fns fns (car lst) wrld)
                 (expand-some-non-rec-fns-lst fns (cdr lst) wrld)))))

)

(defun tautologyp (term wrld)

; Warning: Keep this list below of function names in sync with those in
; possible-trivial-clause-p.

; If this function returns t, then term is a theorem.  With the intended
; application in mind, namely the recognition of "trivial corollaries" while
; processing rule classes, we check for the "most common" tautology, (implies p
; p).  Otherwise, we expand certain non-recursive fns and see if the result is
; an if-tautology.  This function can be made as fancy as you want, as long as
; it recognizes theorems.

  (cond ((and (ffn-symb-p term 'implies)
              (equal (fargn term 1) (fargn term 2)))
         t)
        (t (if-tautologyp
            (expand-some-non-rec-fns

; The list of functions expanded is arbitrary, but they must all be
; non-recursively defined; indeed, because of the use of bbody in the
; definition of expand-some-non-rec-fns, these function must all belong to
; *definition-minimal-theory*.  Guards are permitted but of course it is the
; guarded body that we substitute.  The IF tautology checker doesn't know
; anything about any function symbol besides IF and NOT (and QUOTEd constants).
; The list below pretty obviously has to include IMPLIES and IFF.  It should
; not include NOT.

; The list is in fact *expandable-boot-strap-non-rec-fns* with NOT deleted and
; IFF added.  The main idea here is to include non-rec functions that users
; typically put into the elegant statements of theorems.  If functions are
; added to this list, consider changing the quoted constant in
; expand-abbreviations and, if the functions are not also added to
; *expandable-boot-strap-non-rec-fns*, the constant
; *definition-minimal-theory*, used in translate-in-theory-hint.  Consider also
; preprocess-clause and the error pertaining to *definition-minimal-theory* in
; chk-acceptable-definition-install-body.

             '(iff
               ;not
               implies eq atom eql = /= null

; If we ever make 1+ and 1- functions again, they should go back on this list.

               zerop synp return-last plusp minusp listp mv-list cons-with-hint
               wormhole-eval force case-split double-rewrite)
             term wrld)))))

(defun make-true-list-cons-nest (term-lst)
  (cond ((null term-lst) *nil*)
        (t (cons-term 'cons
                      (list (car term-lst)
                            (make-true-list-cons-nest (cdr term-lst)))))))

; Rockwell Addition: The reason we changed the recursivep property is
; that we frequently ask whether there is a recursive fn on the
; fnstack and now we don't have to go to the property list to answer.
; Read the comment below.

(defun being-openedp-rec (fn fnstack)

; We determine whether fn is ``on'' fnstack (including being a member of a
; mutually recursive clique).

; The fnstack used by the rewriter is a list.  Each element is one of four
; shapes:

; (1) a function symbol -- we are expanding a definition of that symbol and the
; symbol is non-recursively defined.

; (2) a list of function symbols -- we are expanding a singly or mutually
; recursive function.  (In fact, the fnstack element is the recursivep flag of
; the function we're expanding.)

; (3) a list of the form (:term . term) for some term, term -- we are rewriting
; the indicated term (through the recursive dive in the rewriter that rewrites
; the just-rewritten term).  See the extended comment in fnstack-term-member
; for an explanation and example.

; (4) the symbol :rewrite-lambda-object -- we are in the process of rewriting a
; lambda object.

; Lambda-expressions are never pushed onto the fnstack even though fn may be a
; lambda-expression.

  (cond ((null fnstack) nil)
        ((consp (car fnstack))
         (or (eq fn (caar fnstack)) ; and hence (not (eq (caar fnstack) :term))
             (being-openedp-rec fn (cdr fnstack))))
        (t (or (eq fn (car fnstack))
               (being-openedp-rec fn (cdr fnstack))))))

(defstub being-openedp-limited-for-nonrec () t)
(defattach being-openedp-limited-for-nonrec constant-t-function-arity-0)

(defmacro being-openedp (fn fnstack clique settled-down-p)

; We found a 1.8% slowdown when we modified the code, in a preliminary cut at
; Version_2.7, to improve the speed of being-openedp when large cliques are on
; the fnstack by looking up the representative of fn on the fnstack, rather
; than looking up fn itself.  Presumably that slowdown resulted from the new
; calls to getprop to get the 'recursivep property (back when we used it for
; this purpose, through Version_2.9.4).  Here we avoid computing that getprop
; (in the case that clique is a getprop expression) in a case we suspect is
; pretty common: fnstack is empty.  The fnstack argument will always be a
; symbolp expression, so we do not need to let-bind it below.

  (declare (xargs :guard (symbolp fnstack)))
  `(and ,fnstack
        (let ((clique ,clique))
          (and (or clique

; At one time this fnstack check could completely stop the opening up of a
; non-recursive function call.  After Version_8.3 we decided that we would like
; to avoid making that stop (based on an example that arose), but for backward
; compatibility we defeat this fnstack check only when "desperate": when
; simplification of the clause has just settled down (before attempting to
; eliminate destructors).  An attachable function allows the original, full
; being-openedp check to take place after all.

                   (not ,settled-down-p)
                   (not (being-openedp-limited-for-nonrec)))
               (being-openedp-rec (if clique
                                      (car clique)
                                    ,fn)
                                  ,fnstack)))))

(defun recursive-fn-on-fnstackp (fnstack)

; We return t iff there is an element of fnstack that is recursively
; defined.  We assume that any mutually recursive clique on the stack
; is truly indicative of mutual recursion.  See the description of the
; fnstack in being-openedp.

  (cond ((null fnstack) nil)
        ((and (consp (car fnstack))
              (not (eq (caar fnstack) :term)))
         t)
        (t (recursive-fn-on-fnstackp (cdr fnstack)))))

(defun fnstack-term-member (term fnstack)

; If we are not careful, the call (rewrite rewritten-body ...) in
; rewrite-fncall can cause an infinite loop.  Here we describe a mechanism for
; avoiding such loops.  This mechanism is enforced by the call to
; fnstack-term-member in rewrite-fncall, which must return nil before opening
; up a function call.

; The problem is the interaction between opening up function definitions and
; use of equalities on the type-alist.  Suppose that (foo x) is defined to be
; (bar (foo (cdr x))) in a certain case.  But imagine that on the type-alist we
; have (foo (cdr x)) = (foo x).  Then rewritten-body, here, is (bar (foo x)).
; Because it contains a rewritable call we rewrite it again.  If we do so with
; the old fnstack, we will open (foo x) to (bar (foo x)) again and infinitely
; regress.

; The following event list illustrates the problem we wish to avoid.
; (defun bar (x) (declare (ignore x)) 7)
; (in-theory (disable bar))
; (defun foo (x)
;  (if (consp x) (bar (foo (cdr x))) t))
; :brr t
; :monitor (:definition foo) t
; (thm (implies (and (consp x) (equal (foo x) (foo uuu))) (not (equal (foo (cdr x)) (foo x)))))
; :eval
; :eval
; :eval
; ...

; Doing a :path after the :evals shows an infinite regress rewriting (foo x).
; The problem is that lit 3 is on the type-alist and causes (foo (cdr x)) to
; rewrite to (foo x).  Thus, when (foo x) in lit 2 is rewritten it first goes
; to (bar (foo (cdr x))) and thence to (bar (foo x)).

; This same loop occurs in Nqthm, though it has never been fired in anger, as
; far as we know.

; In Version 2.5 and before we handled this rare loop in a very non-rugged way,
; using fnstack unchanged in the aforementioned recursive call (rewrite
; rewritten-body ...): If the term we're expanding reoccurs in the rewritten
; body, we won't rewrite the rewritten body.  In that approach, if we're
; expanding (foo x a) and it rewrites to (bar (foo (cdr x) a)) and thence to
; (bar (foo x a)), we'll break the loop.  BUT if it goes instead to (bar (foo x
; a')), we'll just naively go around the loop.

; Starting with Version_2.6, we extended fnstack with (:term . term) in that
; recursive call to rewrite.  Through Version_2.8, before making that recursive
; call we first checked the fnstack to see if an entry (:term . x) was already
; there for some subterm x of rewritten-body.  This was the only place that we
; paid attention to elements of fnstack of the form (:term . x).

; Starting with Version_2.9, we do a simpler check for membership of (:term
; . term) in the fnstack.  (The present function implements that membership
; check without the need to cons up (:term . term).)  The unique such check is
; done where it makes the most sense: just before we open up a function call in
; rewrite-fncall.

; Here is an example based on a script sent by Andrew Feist that causes an
; infinite loop in Version 2.5 but not in Version 2.6 (but using :dir :system
; as introduced in 2.8).

;  (include-book "arithmetic/top-with-meta" :dir :system)
;
;  (defun a (x)
;    (cond
;     ((not (integerp x)) nil)
;     ((< x 1) nil)
;     ((= x 1) 1)
;     ((= x 2) 2)
;     ((= x 3) 24)
;     (t (/ (- (* 6 (expt (a (1- x)) 2) (a (- x 3)))
;              (* 8 (a (1- x)) (expt (a (- x 2)) 2)))
;           (* (a (- x 2)) (a (- x 3)))))))
;
;  (defun e (x) ; product from i=1 to x-1 of 2^i - 1
;    (if (not (integerp x))
;        0
;      (if (< x 2)
;          1
;        (* (+ (expt 2 x) (- 1)) (e (1- x))))))
;
;  (defun d (x)
;    (cond
;     ((not (integerp x)) nil)
;     ((< x 1) nil)
;     (t (* (expt 2 (/ (* x (1- x)) 2)) (e (1- x))))))
;
;  ; Added to Andrew's script:
;  (in-theory (disable exponents-add))
;
;  (defthm lemma-a-is-d ; doesn't prove, but at least it avoids the loop
;    (= (a x) (d x)))

; We can execute the following trace forms if in GCL, in which case we should see
; the trace output shown below in Version  2.5 and before.

;  (trace (rewrite-fncall
;          :cond (eq (cadr (access rewrite-rule (car si::arglist) :rune)) 'expt)
;          :entry (list (cadr si::arglist) (nth 7 si::arglist))
;          :exit (car si::values)))

;  (trace (rewrite
;          :entry (list (car si::arglist) (nth 8 si::arglist))
;          :exit (car si::values)))
;
;                     114> (REWRITE-FNCALL (EXPT '2 (BINARY-+ '-2 X))
;                                     (E))>
;                     115> (REWRITE
;                          (IF (ZIP I)
;                              '1
;                              (IF (EQUAL (FIX R) '0)
;                                  '0
;                                  (IF (< '0 I)
;                                      (BINARY-* R (EXPT R (BINARY-+ I '-1)))
;                                      (BINARY-* (UNARY-/ R)
;                                                (EXPT R (BINARY-+ I '1))))))
;                          (EXPT E))>
; ...............................
;                     120> (REWRITE-FNCALL (EXPT '2 (BINARY-+ '-1 X))
;                                     (EXPT E))>
;                     <120 (REWRITE-FNCALL EXPT '2
;                                     (BINARY-+ '-1 X))>
; ...............................
;                     <115 (REWRITE BINARY-* '1/2
;                              (EXPT '2 (BINARY-+ '-1 X)))>
;                     115> (REWRITE (BINARY-* '1/2
;                                        (EXPT '2 (BINARY-+ '-1 X)))
;                              (E))>
; [never returns from this final 115, hence never returns from 114]

; But our solution at that point (described above for Version_2.6) did not
; prevent an infinite loop in Version_2.8 for the following example, sent by
; Fares Fraij.

;  (defun get-constant (n classfile)
;    (let ((temp (assoc n classfile)))
;      (cond ((null temp) nil)
;            ((stringp (cadr temp)) (cadr temp))
;            ((or (not (natp n))
;                 (not (natp (cadr temp)))
;                 (<= n (cadr temp)))
;             nil)
;            (t (get-constant (cadr temp) classfile)))))

;  (defun get-constant-path (n classfile)
;    (let ((temp (assoc n classfile)))
;      (cond ((null temp) nil)
;            (t   (if (or (stringp (cadr temp))
;                         (not (natp n))
;                         (not (natp (cadr temp)))
;                         (<= n (cadr temp)))
;                     (list n)
;                   (cons n (get-constant-path (cadr temp) classfile)))))))

;  (defthm member-position-path-get-constant-n-1
;    (implies (member position (get-constant-path n classfile))
;             (equal (get-constant n classfile)
;                    (get-constant position classfile))))

; The final defthm above caused an infinite loop.  The fnstack had plenty of
; copies of (:TERM GET-CONSTANT N CLASSFILE), yet the loop was caused by
; repeated opening up of (GET-CONSTANT N CLASSFILE)!  How could this happen?
; The rewritten-body was (GET-CONSTANT POSITION CLASSFILE), so our test for
; membership in fnstack returned nil, and we went ahead and rewrote the
; rewritten-body.  That rewrite was in a context where POSITION is known to
; equal N, so POSITION rewrote to N, and we found ourselves with a new call of
; (GET-CONSTANT N CLASSFILE).

; So now we do the fnstack check for (:term . term) even before opening up the
; function call.

  (cond ((null fnstack) nil)
        ((and (consp (car fnstack))
              (eq (caar fnstack) :term)
              (equal (cdar fnstack) term))
         t)
        (t (fnstack-term-member term (cdr fnstack)))))

; Essay on Too-many-ifs

; The discussion below applies to a long-standing "too-many-ifs" heuristic that
; is used only for nonrecursive function applications when no recursive
; function application is on the stack.  Up through Version_3.6.1, we always
; rewrote the body of nonrecursive function calls and then applied this
; heuristic.  After Version_3.6.1, we modified this heuristic to avoid
; rewriting the bodies of some such calls, by calling a version of the function
; first on unrewritten bodies and then, possibly again, after rewriting.  This
; gives rise to two functions, too-many-ifs-pre-rewrite and
; too-many-ifs-post-rewrite.

; Let args be the list of actuals to a nonrec fn.  We wish to determine whether
; the expansion of the fn call introduces too many IFs all at once into the
; rewritten body of fn.  Our motivation comes from an example like (M2 (ZTAK &
; & &) (ZTAK & & &) (ZTAK & & &)) where the careless opening up of everybody
; produces a formula with several hundred IFs in it because of M2's duplication
; of the IFs coming from the simplification of the ZTAKs.  An early thought was
; never to expand a nonrec fn -- at the top level of the clause -- if it had
; some IFs in its args and to wait till CLAUSIFY has cleaned things up.  That
; slowed a proveall down by a factor of 2 -- and by a factor of 13 in
; PRIME-LIST-TIMES-LIST -- because of the ridiculously slow expansion of such
; basic nonrec fns as AND, OR, NOT, and NLISTP.

; This heuristic originally took ARGS and the rewritten right-hand side of fn,
; VAL, and computed something like

; (> (ITERATE FOR ARG IN ARGS SUM (* (COUNT-IFS ARG) (OCCUR-CNT ARG VAL)))
;    (ITERATE FOR ARG IN ARGS SUM (COUNT-IFS ARG)))

; where the OCCUR-CNT counted the number of times ARG occurred in VAL.  The
; heuristic was slightly optimized by observing that if no IFs occur in any arg
; then there is no point in doing the OCCUR-CNTs and that once the left hand
; side has been pushed beyond the right there is no point in continuing.  (We
; say "something like" because the code, at least as of Version_3.6.1,
; double-counted an ARG when it was a subterm of some other arg in ARGS.)

; However, when Sol Swords profiled some book certification typically done at
; Centaur, his results suggested that nearly half of the rewriting and 15% of
; the total time (where 45% of the total time seemed to be in include-book-fn)
; was spent in too-many-ifs.  It turns out that we can save most of the
; too-many-ifs time by doing a preliminary check, before rewriting the
; right-hand-side, to see if it is "expected" (in some very inexact sense) that
; the right-hand-side would have too-many-ifs.  The function
; too-many-ifs-pre-rewrite does this check using the unrewritten body, which
; not only saves potential rewriting but also can be faster because the unrewritten
; body is often much smaller than the rewritten body.

; At one point we avoided too-many-ifs-post-rewrite entirely, which pushed our
; savings above 20%.  But we had failures in the regression suite:
; collect-times-1d in books/arithmetic-2/meta/common-meta.lisp and
; sum-pp4-reduce-to in books/rtl/rel7/support/lib1.delta1/mult-proofs.lisp.  In
; these cases, the proof failed because the new heuristic stopped fix from
; opening up, while the original heuristic allowed (fix x) to open up for the
; particular x at hand because (acl2-numberp x) simplified to t.  We solved
; that problem: at first we made an exception for fix, but now we simply
; ignored occurrences in test positions of calls of IF when counting argument
; occurrences in right-hand-sides of definition rules (see var-counts).

; Lemma make-shared-variables-dag-as-term-l-lemma in community book
; books/defexec/dag-unification/terms-as-dag.lisp is a good test case: it
; proves using the old heuristic but seems difficult to prove using the new
; heuristic (too-many-ifs-pre-rewrite) alone.  It is also notable in that if
; memory serves, the new heuristic specifically fails on lambdas.  We are
; pretty happy with our current implementation, which is a compromise: Use
; too-many-ifs-pre-rewrite to avoid opening up the right-hand side of a
; definition at all in some cases, but even if we do open it up, use
; too-many-ifs-post-rewrite to apply the old too-many-ifs heuristic.

(mutual-recursion

(defun var-counts1 (arg rhs acc)

; See the comment in var-counts.

  (declare (xargs :guard (and (pseudo-termp rhs)
                              (natp acc))
                  :verify-guards nil))
  (cond ((equal arg rhs)
         (1+ acc))
        ((variablep rhs)
         acc)
        ((fquotep rhs)
         acc)
        ((eq (ffn-symb rhs) 'if)
         (max (var-counts1 arg (fargn rhs 2) acc)
              (var-counts1 arg (fargn rhs 3) acc)))
        (t (var-counts1-lst arg (fargs rhs) acc))))

(defun var-counts1-lst (arg lst acc)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (natp acc))))
  (cond ((endp lst) acc)
        (t (var-counts1-lst arg
                            (cdr lst)
                            (var-counts1 arg (car lst) acc)))))
)

(defun var-counts (lhs-args rhs)

; Return a list of natural numbers that corresponds positionally to lhs-args,
; where the nth element of the returned list is an approximation to the number
; of occurrences of the nth element of lhs-args in rhs.  Normally lhs-args will
; be a list of variables -- hence the name -- though it can be the arguments to
; any call on the left-hand side of a definition rule.

; More precisely, the return value is used in the too-many-ifs-pre-rewrite
; heuristic, as a list of possible occurrences of each arg (formal) in the rhs
; of a given definition.  Larger elements of var-counts make it more likely
; that the given definition will not be opened up (or if it is, then that it
; will be closed back up again).

; Our algorithm ignores occurrences of elements of lhs-args in test positions
; of calls of IF, and for such calls, it takes maxima for the true and false
; branches; see var-counts1.  These decisions are merely heuristic, and might
; benefit from further experimentation, though we are pretty happy with current
; performance based on tests to date.  But our decisions deserve some remarks:

; Note that the var-counts are used before attempting to rewrite the rhs.  If
; we wished, var-counts could return a trivial result consisting of a list of
; zeroes from var-counts; as a result we will always rewrite the rhs.  But we
; want to short-circuit that rewrite when it seems reasonable to do so, such as
; when we have pretty good reason to believe that the too-many-ifs heuristic
; used _after_ rewriting would reject opening up the definition anyhow.

; For us to have good reason, we should be careful not to have the returned
; var-counts be too large, which could make it too easy to reject the
; opening-up.  For this reason, we ignore occurrences in test positions of
; calls of IF, since we can imagine those may disappear after the instantiated
; rhs is simplified.  But we don't want the var-counts to be too small, since
; then we might miss opportunities for efficiencies in early termination.  We
; might for example get all zeroes if we always take the minimum of var-counts
; in the two branches of any IF call, since it could often be the case that a
; formal parameter only occurs in one of the two branches.

; So, we take the maximum of two branches of any IF call.  In an early
; experiment we had good results taking the sum rather than the maximum: only a
; couple of proofs failed during ACL2 regression, and we got a 20% speed-up on
; a test provided by Sol Swords on certification done at Centaur.  But the sum
; is too large if we really imagine the IF tests simplifying away, so we take
; the maximum as a sort of compromise between the sum and the minimum (which
; could easily be too small, as explained above).

  (declare (xargs :guard (and (true-listp lhs-args)
                              (pseudo-termp rhs))))

  (cond ((endp lhs-args) nil)
        (t (cons (var-counts1 (car lhs-args) rhs 0)
                 (var-counts (cdr lhs-args) rhs)))))

(mutual-recursion

(defun count-ifs (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term) 0)
        ((fquotep term) 0)
        ((eq (ffn-symb term) 'hide) 0)
        ((eq (ffn-symb term) 'if)
         (+ 1
            (count-ifs (fargn term 1))
            (count-ifs (fargn term 2))
            (count-ifs (fargn term 3))))
        (t (count-ifs-lst (fargs term)))))

(defun count-ifs-lst (lst)
  (declare (xargs :guard (pseudo-term-listp lst)))
  (cond ((endp lst) 0)
        (t (+ (count-ifs (car lst))
              (count-ifs-lst (cdr lst))))))

)

; We originally defined nat-listp here and used it in the guards of
; too-many-ifs0 and too-many-ifs-pre-rewrite, but several community books had
; conflicts with this definition of nat-listp, as follows:

; workshops/2004/ruiz-et-al/support/terms-as-dag.lisp
; workshops/2003/sumners/support/n2n.lisp
; workshops/2009/kaufmann-kornerup-reitblatt/support/preliminaries.lisp
; concurrent-programs/bakery/measures.lisp
; unicode/nat-listp.lisp
; defexec/dag-unification/terms-as-dag.lisp

; So we have commented out this definition.  If we decide to use it after all,
; change integer-listp to nat-listp in the two guards mentioned above and also
; in community book books/system/too-many-ifs.lisp, as indicated there.

; (defun nat-listp (x)
;   (declare (xargs :guard t))
;   (cond ((atom x)
;          (equal x nil))
;         (t (and (natp (car x))
;                 (nat-listp (cdr x))))))

(defun too-many-ifs0 (args counts diff ctx)

; See also too-many-ifs-pre-rewrite.

; Diff is (- dot-product count-ifs), where count-ifs is the sum of the
; count-ifs of the args already processed and dot-product is the dot-product of
; the vector of those count-ifs and the counts already processed.

  (declare (type (signed-byte 30) diff)
           (xargs :guard (and (pseudo-term-listp args)
                              (integer-listp counts)
                              (equal (len args) (len counts)))))
  (cond ((endp args) (> diff 0))
        ((eql (car counts) 1)

; Then (count-ifs (car args)) will contribute nothing to diff.

         (too-many-ifs0 (cdr args) (cdr counts) diff ctx))
        (t
         (let ((count1 (the-fixnum! (count-ifs (car args)) ctx)))
           (declare (type (unsigned-byte 29) count1))
           (too-many-ifs0 (cdr args)
                          (cdr counts)
                          (the-fixnum! (+ (the-fixnum! (* count1
                                                          (1- (car counts)))
                                                       ctx)
                                          diff)
                                       ctx)
                          ctx)))))

(defproxy too-many-ifs-pre-rewrite (* *) => *)

(defun too-many-ifs-pre-rewrite-builtin (args counts)

; See the Essay on Too-many-ifs.

; Args is the left-hand-side of a definition rule, hence most commonly the
; formal parameters of some function.  Counts is a list that corresponds
; positionally to args, and represents the number of occurrences of each
; element of args in the right-hand-side of the implicit definition rule.
; (For details on how counts is computed, see var-counts.)

  (declare (xargs :guard (and (pseudo-term-listp args)
                              (integer-listp counts)
                              (equal (len args) (len counts)))))

  (too-many-ifs0 args counts 0 'too-many-ifs-pre-rewrite))

(defattach (too-many-ifs-pre-rewrite too-many-ifs-pre-rewrite-builtin)
  :skip-checks t)

; This dead code could be deleted, but we leave it as documentation for
; occur-cnt-bounded.

; (mutual-recursion
;
; (defun occur-cnt-rec (term1 term2 acc)
;
; ; Return a lower bound on the number of times term1 occurs in term2.
; ; We do not go inside of quotes.
;
;   (cond ((equal term1 term2) (1+ acc))
;         ((variablep term2) acc)
;         ((fquotep term2) acc)
;         (t (occur-cnt-lst term1 (fargs term2) acc))))
;
; (defun occur-cnt-lst (term1 lst acc)
;   (cond ((null lst) acc)
;         (t (occur-cnt-rec term1
;                           (car lst)
;                           (occur-cnt-lst term1 (cdr lst) acc)))))
; )
;
; (defun occur-cnt (term1 term2)
;   (occur-cnt-rec term1 term2 0))

(mutual-recursion

(defun occur-cnt-bounded (term1 term2 a m bound-m)

; Let bound = (+ m bound-m).  Return (+ a (* m (occur-cnt term1 term2))) unless
; it exceeds bound, in which case return -1.  We assume (<= a bound).

; Occur-cnt is no longer defined, but was defined (as is this function) so as
; not to go inside of quotes, returning a lower bound on the number of times
; term1 occurs in term2.

  (declare (type (signed-byte 30) a m bound-m)
           (xargs :measure (acl2-count term2)
                  :ruler-extenders (:lambdas)
                  :guard (and (pseudo-termp term2)
                              (signed-byte-p 30 (+ bound-m m))
                              (<= 0 a)
                              (<= 0 m)
                              (<= 0 bound-m)
                              (<= a (+ bound-m m)))
                  :verify-guards nil))
  (the-fixnum
   (cond ((equal term1 term2)
          (if (<= a bound-m)
              (the-fixnum (+ a m))
            -1))
         ((variablep term2) a)
         ((fquotep term2) a)
         (t (occur-cnt-bounded-lst term1 (fargs term2) a m bound-m)))))

(defun occur-cnt-bounded-lst (term1 lst a m bound-m)
  (declare (type (signed-byte 30) a m bound-m)
           (xargs :measure (acl2-count lst)
                  :ruler-extenders (:lambdas)
                  :guard (and (pseudo-term-listp lst)
                              (signed-byte-p 30 (+ bound-m m))
                              (<= 0 a)
                              (<= 0 m)
                              (<= 0 bound-m)
                              (<= a (+ bound-m m)))))
  (the-fixnum
   (cond ((endp lst) a)
         (t (let ((new (occur-cnt-bounded term1 (car lst) a m bound-m)))
              (declare (type (signed-byte 30) new))
              (if (eql new -1)
                  -1
                (occur-cnt-bounded-lst term1 (cdr lst) new m bound-m)))))))
)

(defun too-many-ifs1 (args val lhs rhs ctx)

; See also too-many-ifs-post-rewrite-builtin.

; We assume (<= lhs rhs).

  (declare (type (signed-byte 30) lhs rhs)
           (xargs :guard (and (pseudo-term-listp args)
                              (pseudo-termp val)
                              (<= 0 lhs)
                              (<= lhs rhs)
                              (<= (count-ifs-lst args) rhs))))
  (cond
   ((endp args) nil)
   (t (let ((x (the-fixnum! (count-ifs (car args)) ctx)))
        (declare (type (signed-byte 30) x))
        (cond ((eql x 0)
               (too-many-ifs1 (cdr args) val lhs rhs ctx))
              (t (let ((lhs
                        (occur-cnt-bounded (car args) val lhs x
                                           (the-fixnum (- rhs x)))))
                   (declare (type (signed-byte 30) lhs))
                   (if (eql lhs -1)
                       -1
                     (too-many-ifs1 (cdr args) val lhs rhs ctx)))))))))

(defproxy too-many-ifs-post-rewrite (* *) => *)

(defun too-many-ifs-post-rewrite-builtin (args val)

; This function implements the part of the too-many-ifs heuristic after the
; right-hand-side of a definition has been rewritten, to see if that expansion
; is to be kept or thrown away.  See the Essay on Too-many-ifs.

  (declare (xargs :guard (and (pseudo-term-listp args)
                              (pseudo-termp val))))

  (let* ((ctx 'too-many-ifs-post-rewrite-builtin)
         (rhs (the-fixnum! (count-ifs-lst args) ctx)))
    (cond ((int= rhs 0) nil)
          (t (too-many-ifs1 args val 0 rhs ctx)))))

(defattach (too-many-ifs-post-rewrite too-many-ifs-post-rewrite-builtin)
  :skip-checks t)

(defun all-args-occur-in-top-clausep (args top-clause)
  (cond ((null args) t)
        (t (and (dumb-occur-lst (car args) top-clause)
                (all-args-occur-in-top-clausep (cdr args) top-clause)))))

(defun cons-count-bounded-ac (x i max)

; We accumulate into i the number of conses in x, bounding our result by max,
; which is generally not less than i at the top level.

; With the xargs declarations shown below, we can verify termination and guards
; as follows.

;   (verify-termination (cons-count-bounded-ac
;                        (declare (xargs :verify-guards nil))))
;
;   (defthm lemma-1
;     (implies (integerp i)
;              (integerp (cons-count-bounded-ac x i max)))
;     :rule-classes (:rewrite :type-prescription))
;
;   (defthm lemma-2
;     (implies (integerp i)
;              (>= (cons-count-bounded-ac x i max) i))
;     :rule-classes :linear)
;
;   (defthm lemma-3
;     (implies (and (integerp i)
;                   (integerp max)
;                   (<= i max))
;              (<= (cons-count-bounded-ac x i max)
;                  max))
;     :rule-classes :linear)
;
;   (verify-guards cons-count-bounded-ac)

  (declare (type (signed-byte 30) i max)
           (xargs :guard (<= i max)
                  :measure (acl2-count x)
                  :ruler-extenders :lambdas))
  (the (signed-byte 30)
    (cond ((or (atom x) (>= i max))
           i)
          (t (let ((i (cons-count-bounded-ac (car x) (1+f i) max)))
               (declare (type (signed-byte 30) i))
               (cons-count-bounded-ac (cdr x) i max))))))

(defun cons-count-bounded (x)

; We return the number of conses in x, except we bound our result by
; (fn-count-evg-max-val).  We choose (fn-count-evg-max-val) as our bound simply
; because that bound is used in the similar computation of fn-count-evg.

  (the (signed-byte 30)
    (cons-count-bounded-ac x 0 (fn-count-evg-max-val))))

(mutual-recursion

(defun max-form-count (term)

; This function is used in the control of recursive fn expansion.  Many years
; ago, we used the fn count part of var-fn-count in this role.  Then we decided
; that for controlling expansion we should not count (IF x y z) to have size
; 1+|x|+|y|+|z| because the IF will be distributed and the y or the z will rest
; in the argument position of the recursive call.  So we started to compute the
; maximum fn count in the branches.  Then we added explicit values (this really
; was years ago!) and decided not to consider 1000 to be better than 999, since
; otherwise (< x 1000) would open.  So we measure quoted constants by their
; Lisp size.

; But with the advent of the HONS version of ACL2, our concern mounted about
; the ability of ACL2 to handle very large ("galactic") objects.  Consider the
; following example, which caused ACL2 Version_3.4 to hang.

;    (defun big (n)
;      (cond ((posp n) (let ((x (big (1- n))))
;                        (cons x x)))
;            (t nil)))
;
;    (defun foo (x) (if (consp x) (foo (cdr x)) x))
;
;    (set-gag-mode nil)
;    (set-inhibit-output-lst '(prove proof-tree summary))
;
;    (thm (consp (foo (big 50)))
;         :hints (("Goal"
;                  :in-theory
;                  (disable (foo) (:type-prescription foo)))))
;

; Our solution is to bound the computation of size of explicit values, unlike
; the unbounded computation done through ACL2 Version_3.4.  There, we used a
; function, cons-count, that ignored the sizes of numeric explicit values,
; counting only conses.

; But just how should we bound the size computation for explicit values?

; It seems odd that the existing approach only counted conses, since there
; seems to be no obvious reason to treat the number of conses in a list
; differently from the number of (implicit) successor calls in a natural
; number.  Our first change was to ignore completely the sizes of explicit
; values, returning 0 in the fquotep case below.  Unfortunately, we then
; observed a failure in the event (verify-guards meta-integerp ...) in
; community book books/arithmetic-3/bind-free/integerp-meta.lisp.  We have
; extracted the following from that failure: This succeeded when using
; (cons-count (cadr term)) in the case (fquotep term) below, but not when using
; 0 in that case instead.

;  (thm (IMPLIES
;        (AND (PSEUDO-TERM-LISTP (CDR TERM))
;             (MEMBER-EQ (CAADR TERM)
;                        '(BINARY-+ BINARY-*)))
;        (PSEUDO-TERM-LISTP (LEAVES (CADDAR (CDR TERM))
;                                   (CAADR TERM)))))

; Our first fix was simply to count size of explicit values just as we do in
; some other places, using fn-count-evg in the fquotep case.  Unfortunately we
; got a failure in (verify-guards subtract-bag ...) in the same file as above,
; apparently because (mv-nth 1 x) now opens up to (cadr x).

; So for backward compatibility we now define a bounded version of cons-count.

; Notice that our bounded size computation can cause the "wrong" term to be
; viewed as the smaller, so we need to be confident that this is not a problem,
; and indeed it is not when we call max-form-count in smallest-common-subterms.

  (the (signed-byte 30)
    (cond ((variablep term) 0)
          ((fquotep term) (cons-count-bounded (cadr term)))
          ((eq (ffn-symb term) 'if)
           (max (max-form-count (fargn term 2))
                (max-form-count (fargn term 3))))
          (t (max-form-count-lst (fargs term) 1)))))

(defun max-form-count-lst (lst acc)
  (declare (type (signed-byte 30) acc))
  (the (signed-byte 30)
    (cond ((>= acc (fn-count-evg-max-val))
           (fn-count-evg-max-val))
          ((null lst) acc)
          (t (max-form-count-lst (cdr lst)
                                 (+f acc (max-form-count (car lst))))))))

)

(defun controller-complexity1 (flg args controller-pocket)

; Flg is either t (meaning we measure the controllers) or nil
; (meaning we measure the non-controllers).  Args is the arg list
; to a call of a fn with the given controller pocket.

; In this implementation a controller pocket is a list of
; Booleans in 1:1 correspondence with the formals.  A t in an
; argument position indicates that the formal is a controller.

; We sum the max-form-counts of the arguments in controller (or
; non-controller, according to flg) positions.

  (cond ((null args) 0)
        ((eq (car controller-pocket) flg)
         (+ (max-form-count (car args))
            (controller-complexity1 flg
                                    (cdr args)
                                    (cdr controller-pocket))))
        (t (controller-complexity1 flg
                                   (cdr args)
                                   (cdr controller-pocket)))))

(defun controller-complexity (flg term controller-alist)

; Term is a call of some recursive fn in a mutually recursive clique.
; Controller-alist is an alist that assigns to each fn in the clique a
; controller-pocket.  We compute the controller complexity (or
; non-controller complexity, according to flg being t or nil) of term
; for the controller pocket assigned fn in the alist.

  (controller-complexity1 flg
                          (fargs term)
                          (cdr (assoc-eq (ffn-symb term)
                                         controller-alist))))

(defun controller-pocket-simplerp (call result controller-alist)

; Call has rewritten to something involving result.  Both call and
; result are applications of functions in the same mutually recursive
; clique.

; Controller-alist associates a fn in the clique to a controller
; pocket.  A controller pocket is a list in 1:1 correspondence with
; the formals of the fn with a t in those slots that are controllers
; and a nil in the others.  Thus, this alist assigns a complexity to
; both call and to result.

; We determine whether there controller-alist assigns a lower
; complexity to result than to call.

  (< (controller-complexity t result controller-alist)
     (controller-complexity t call controller-alist)))

(defun constant-controller-pocketp1 (args controller-pocket)
  (cond ((null args) t)
        ((car controller-pocket)
         (and (quotep (car args))
              (constant-controller-pocketp1 (cdr args)
                                            (cdr controller-pocket))))
        (t (constant-controller-pocketp1 (cdr args)
                                         (cdr controller-pocket)))))

(defun constant-controller-pocketp (term controller-alist)

; Term is a call of some fn in the clique for which controller-alist is
; a controller alist.  That alist assigns a controller-pocket to fn.
; We determine whether the controller arguments to fn in term are all
; quoted.

  (constant-controller-pocketp1 (fargs term)
                                (cdr (assoc-eq (ffn-symb term)
                                               controller-alist))))

(defun some-controller-pocket-constant-and-non-controller-simplerp
  (call result controller-alist)

; Call and result are both applications of functions in the same
; mutually recursive clique.  Controller-alist is an alist that assigns
; to each fn in the clique a controller pocket.  We determine whether
; that alist assigns controllers in such a way that the controllers of
; result are constant and the complexity of the non-controllers in
; result is less than that of the non-controllers in call.

  (and (constant-controller-pocketp result controller-alist)
       (< (controller-complexity nil result controller-alist)
          (controller-complexity nil call controller-alist))))

(mutual-recursion

(defun rewrite-fncallp (call result cliquep top-clause current-clause
                             controller-alist)

; Call has rewritten to (some term involving) result.  We want to know
; if we should replace call by result or leave the call unopened.  The
; ffn-symb of call is known to be a recursive function symbol, fn.  It
; is not a lambda-expression.  Cliquep is nil if fn is singly
; recursive and is the list of functions in fn's clique if it is
; mutually recursive.  Top-clause and current-clause are two clauses
; from simplify-clause0 (the input clause there and the result of
; removing trivial equations).  Controller-alist is the
; :controller-alist field of the def-body of fn.

; Controller-alist pairs every function in fn's mutually recursive
; clique with a controller pocket.  Thus, if fn is singly recursive,
; controller-alist looks like this:
; ((fn . controller-pocket)).
; But if fn is mutually recursive with clique fn1...fnm, then this
; alist assigns a controller pocket to each fni.

  (cond
   ((variablep result) t)
   ((fquotep result) t)
   ((flambda-applicationp result)

; This should not normally happen.  The only time we refuse to open a
; lambda-application is (a) we are at the top level of the clause and
; it has too many ifs, or (b) we were told not to open it by the user.
; But (a) can't have happened while we were constructing result
; because we were opening up a recursive fn.  Of course, the worry is
; that the body of this lambda-expression contains a recursive call
; that will somehow get loose and we will indefinitely recur.  But if
; the only way we get here is via case (b) above, we won't ever open
; this lambda and so we're safe.  We therefore act as though this
; lambda were just some ordinary function symbol.

    (rewrite-fncallp-listp call (fargs result)
                           cliquep
                           top-clause
                           current-clause
                           controller-alist))
   ((if cliquep
        (member-eq (ffn-symb result) cliquep)
      (eq (ffn-symb result) (ffn-symb call)))
    (and (or (all-args-occur-in-top-clausep (fargs result)
                                            top-clause)
             (dumb-occur-lst result current-clause)
             (controller-pocket-simplerp
              call
              result
              controller-alist)
             (some-controller-pocket-constant-and-non-controller-simplerp
              call
              result
              controller-alist))
         (rewrite-fncallp-listp call (fargs result)
                                cliquep
                                top-clause
                                current-clause
                                controller-alist)))
   (t (rewrite-fncallp-listp call (fargs result)
                             cliquep
                             top-clause
                             current-clause
                             controller-alist))))

(defun rewrite-fncallp-listp (call lst cliquep top-clause current-clause
                                   controller-alist)
  (cond ((null lst) t)
        (t (and (rewrite-fncallp call (car lst)
                                 cliquep
                                 top-clause
                                 current-clause
                                 controller-alist)
                (rewrite-fncallp-listp call (cdr lst)
                                       cliquep
                                       top-clause
                                       current-clause
                                       controller-alist)))))

)

(mutual-recursion

(defun contains-rewritable-callp (fn term cliquep
                                     terms-to-be-ignored-by-rewrite)

; This function scans the non-quote part of term and determines
; whether it contains a call, t, of any fn in the mutually recursive
; clique of fn, such that t is not on terms-to-be-ignored-by-rewrite.
; Fn is known to be a symbol, not a lambda-expression.  If cliquep is
; nil, fn is singly recursive.  Otherwise, cliquep is the list of
; functions in the clique (including fn).

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)

; If term is a lambda-application then we know that it contains no recursive
; calls of fns in the clique, as described in the comment on the subject
; in rewrite-fncallp above.

         (contains-rewritable-callp-lst fn (fargs term)
                                        cliquep
                                        terms-to-be-ignored-by-rewrite))
        ((and (if cliquep
                  (member-eq (ffn-symb term) cliquep)
                (eq (ffn-symb term) fn))
              (not (member-equal term terms-to-be-ignored-by-rewrite)))
         t)
        (t (contains-rewritable-callp-lst fn (fargs term)
                                          cliquep
                                          terms-to-be-ignored-by-rewrite))))

(defun contains-rewritable-callp-lst (fn lst cliquep
                                         terms-to-be-ignored-by-rewrite)
  (cond ((null lst) nil)
        (t (or (contains-rewritable-callp fn (car lst)
                                          cliquep
                                          terms-to-be-ignored-by-rewrite)
               (contains-rewritable-callp-lst
                fn (cdr lst)
                cliquep
                terms-to-be-ignored-by-rewrite)))))

)

(defrec linear-lemma

; Warning: Do not change the cheap flag, currently nil, without revisiting
; macro get-rule-field.

  ((nume . hyps) max-term concl
   backchain-limit-lst rune
   .

; The match-free field should be :all or :once if there are free variables in
; the hypotheses, else nil.

   match-free)

; See the warning above.

  nil)

; Finally the Rewriter

(defrec current-literal (not-flg . atm) t)

(defrec rewrite-constant

; WARNING: If you change the layout of the rewrite-constant in a way that
; affects the position of :current-clause -- e.g., add a field -- you MUST
; change the definition in axioms.lisp of the function |Access REWRITE-CONSTANT
; record field CURRENT-CLAUSE|.  If you don't, however, the build will fail
; loudly (via a redefinition error).

; WARNING: If you change the layout of the rewrite-constant in a way that
; affects the position on :nonlinearp, you must change the guard on the
; definitions of nonlinearp-default-hint in (at least) the following
; community books:

; books/arithmetic-5/lib/basic-ops/default-hint.lisp  -- one occurrence
; books/hints/basic-tests.lisp -- two occurrences

; WARNING: The name "rewrite-constant" is a misnomer because it is not really
; constant during rewriting.  For example, the active-theory is frequently
; toggled.

; The Rewriter's Constant Argument -- rcnst

; In nqthm the rewriter accessed many "special variables" -- variables
; bound outside the rewriter.  Some of these were true specials in the
; rewriter, in the sense that the rewriter sometimes re-bound them in its
; recursion.  An example of such a variable is fnstack, which is nil
; outside the rewriter and re-bound inside the rewriter only when we
; tentatively expand a function call.  But other nqthm special variables
; were just constants -- as far as the rewriter was concerned.  For example,
; current-lit, the literal on which rewrite-clause called rewrite, is
; set outside the call of rewrite and read but never written inside.

; We package up these "rewrite constants" as a single record so that
; we can pass all of them in one argument.

; We list below some of the "constants" in question and where they are set.  We
; then give the meaning of each field.

;    field                           where set        soundness
; pt                               rewrite-clause         *
; current-literal not-flg          rewrite-clause
; current-literal atm              rewrite-clause

; top-clause                       simplify-clause1
; current-clause                   simplify-clause1

; terms-to-be-ignored-by-rewrite   simplify-clause
; expand-lst                       simplify-clause

; fns-to-be-ignored-by-rewrite     prove

; rewriter-state                   add-linear-lemma

; The fields marked with *'s are involved in the soundness of the result
; of rewriting.  The rest are of heuristic use only.

; The current-literal not-flg and atm are always used together so we bundle
; them so we can extract them both at once:

  ((active-theory . (rewriter-state . rw-cache-state))
   current-enabled-structure
   (pt restrictions-alist . expand-lst)
   (force-info fns-to-be-ignored-by-rewrite . terms-to-be-ignored-by-rewrite)
   (top-clause . current-clause)
   ((splitter-output . current-literal) . oncep-override)
   (nonlinearp . cheap-linearp)
   (case-split-limitations . forbidden-fns)
   . backchain-limit-rw)
  t)

; Active-theory is either :standard or :arithmetic.  (It was added first to
; Version_2.7.)  It is used to determine whether we are in the middle of
; rewriting arithmetic expressions in support of non-linear arithmetic.  This
; field is toggled during rewriting.  Thus, we put it at the front of the data
; structure.

; Current-enabled-structure is an enabled-structure that contains the theory
; which specifies which rules are to be considered enabled.

; Pt -- a parent tree (see Essay on Parent Trees) denoting a set of literals in
; current-clause and containing the one we are working on in rewrite-clause and
; all the others that have rewritten to false.  Any poly in the
; simplify-clause-pot-lst that depends on one of these literals is considered
; "inactive."  To avoid tail biting we do not use inactive polys.

; Restrictions-alist is used for :restrict hints.  (Someday we should flesh out
; this explanation.)

; Expand-lst -- a list of expand-hint structures used heuristically.  We
; automatically expand any term on this list when encountered.  It is set from
; the user's hint settings and by simplify-clause to force the expansion of the
; induction conclusion in post-induction, pre-settled down rewriting.

; Case-split-limitations -- typically (sr-limit (w state)), but can be set with
; a :case-split-limitations hint to override that default in the simplifier.

; Force-info -- t if there are no calls of IF in the :top-clause, else 'weak.

; Fns-to-be-ignored-by-rewrite -- a list of function symbols used
; heuristically.  If a term begins with one of these, we do not rewrite it.
; This is set from the user's hint settings.

; Terms-to-be-ignored-by-rewrite -- a list of terms used heuristically.  We do
; not rewrite any term on this list.  Simplify-clause sets it during the
; initial post-induction rewriting to prevent us from looking prematurely at
; the induction hypotheses (see simplify-clause for details).

; Top-clause -- the clause on which simplify-clause was called.  This is used
; heuristically only, to decide whether to expand function calls.  The
; difference between top-clause and current-clause is that current-clause has
; been subjected to remove-trivial-equations.

; Current-clause -- Top-clause with remove-trivial-equations.  This is used
; heuristically only.

; Current-literal -- a pair containing the not-flg and atm of the literal on
; which rewrite-clause is currently working.  It was probably used at one time
; to avoid biting our tail (see below), but parent trees now perform that
; function.  We leave :current-literal in the rewrite-constant in case there
; are tools that use it.

; Nonlinearp -- A boolean indicating whether nonlinear arithmetic should be
; considered to be active.

; Cheap-linearp -- A boolean indicating whether linear arithmetic should avoid
; rewriting terms to turn into polys and avoid adding linear lemmas.

; We always obtain our rewrite-constant by loading relevant information into
; the following empty constant.  Warning: The constant below is dangerously
; useless less the current-enabled-structure is set to an enabled-structure.

(defconst *default-rw-cache-state*
  :atom)

(defconst *empty-rewrite-constant*
  (make rewrite-constant
        :active-theory :standard
        :rewriter-state nil
        :case-split-limitations nil
        :forbidden-fns nil
        :splitter-output t ; initial value of state global splitter-output
        :current-clause nil
        :current-enabled-structure nil
        :current-literal nil
        :expand-lst nil
        :fns-to-be-ignored-by-rewrite nil
        :force-info nil
        :nonlinearp nil
        :cheap-linearp nil
        :oncep-override :clear
        :pt nil
        :restrictions-alist nil
        :rw-cache-state *default-rw-cache-state*
        :terms-to-be-ignored-by-rewrite nil
        :top-clause nil
        :backchain-limit-rw nil))

; So much for the rcnst.

(defrec metafunction-context

; WARNING: If you change the layout of this record you must change the PROGN in
; axioms.lisp that defines |Access METAFUNCTION-CONTEXT record field
; TYPE-ALIST| and the other record functions, because that form comes about by
; macroexpanding this defrec.  But if you don't change that PROGN, however, the
; build will fail loudly (via a redefinition error).

; See the Essay on Metafunction Support, Part 1 for an explanation of the use
; of this record.

  (rdepth type-alist obj geneqv wrld fnstack ancestors backchain-limit
          simplify-clause-pot-lst rcnst gstack ttree unify-subst)
  t)

(defun ok-to-force (rcnst)

; Warning: In function push-warrants, we rely on the return value of
; ok-to-force being t or nil.

; We normally use the rewrite constant to determine whether forcing is enabled.
; At one time we experimented with a heuristic that allows the "force-flg" to
; be 'weak, meaning:  do not force if the resulting assumption has a variable
; that does not appear in its type-alist.  (Recall that its type-alist is used
; for the hypotheses of the corresponding goal in the forcing round.)  We still
; allow 'weak to be stored in the rewrite constant, and at the time of this
; writing, the heuristic just described is still implemented in
; force-assumption.  However, we found an example where this heuristic is too
; weak:  the presence of IF terms in the top-level clause is enough to cause
; bad assumptions to be forced, even though our heuristic permits does not
; filter out those bad assumptions.  So we have decided for now that the value
; 'weak from the :force-info field of the rewrite-constant, which is generated
; when there is an IF in the top-level clause, means:  do not force, period.
; (Note that forcing may still be used heuristically, for example by
; type-alist-clause; but, assumptions will not "get out" of such uses.)

  (let ((force-info (access rewrite-constant rcnst :force-info)))
    (cond
     ((eq force-info t)
      (and (enabled-numep *force-xnume*
                          (access rewrite-constant
                                  rcnst
                                  :current-enabled-structure))
           t))
     ((eq force-info 'weak)

; See comment above.

      nil)
     (t
      (er hard 'ok-to-force
          "OK-TO-FORCE called on apparently uninitialized rewrite constant, ~
           ~x0."
          rcnst)))))

; The next major concern is the fact that rewrite takes so many
; arguments.

; Rewrite takes so many arguments that we introduce a macro for
; calling it.  Many functions that call rewrite also take a lot of
; rewrite-type arguments and this macro can be used to call them too.
; Because all of these functions are mutually recursive with rewrite,
; we consider the use of this macro as an indication that we are
; entering the rewriter and have given it the name "rewrite-entry".

; For example, if you write:
;    (rewrite-entry (rewrite-if test left right alist))
; you get
;    (rewrite-if test left right alist type-alist ... rcnst ttree)

; And if you write:
;    (rewrite-entry (rewrite left alist 2)
;                   :ttree new-ttree)
; you get
;    (rewrite left alist 2 ... rcnst new-ttree)

; Note that in specifying which extra arguments you wish to set
; you must use the keyword form of the formal.  This implementation
; decision was made just to bring rewrite-entry into the same style
; as CLTL keyword args, which it resembles.

; The macro extends the given call by adding 12 extra arguments.
; The arguments used are the "extra formals" of rewrite, namely

;    ; &extra formals
;    rdepth type-alist obj geneqv wrld state fnstack ancestors
;    backchain-limit step-limit simplify-clause-pot-lst rcnst gstack ttree

; Important Note:  The string "&extra formals" is included where ever
; this list has been copied.

; However, for every extra formal for which the macro invocation
; specifies a value, that value is used instead.  Any function to be
; called via rewrite-entry should include the extra formals above
; explicitly in its defun, as the last 12 formals.

; Convention: Not every function uses all 12 of the extra formals.
; Ignored formals are so declared.  It is our convention when calling
; a function with an ignored formal to pass it nil in that slot.  That
; explains some (rewrite-entry (add-poly...) :obj nil...).  We could have
; just passed obj's current value, but that suffers from making the
; caller look like it uses obj when in fact obj might be ignored by it
; too.  This convention means that if one of these functions does
; begin to use a currently ignored formal, it will be necessary to
; remove the formal from the (declare (ignore ...)) and might cause us
; to think about the incoming value.

(defun plist-to-alist (lst)

; Convert '(key1 val1 key2 val2 ...) to '((key1 . val1) (key2 . val2) ...).
; In use here, the keys are all in the keyword package.

  (cond ((null lst) nil)
        (t (cons (cons (car lst) (cadr lst))
                 (plist-to-alist (cddr lst))))))

(defmacro adjust-rdepth (rdepth)

; Keep the following in sync with zero-depthp.

  #+acl2-rewrite-meter ; for stats on rewriter depth
  `(1+f ,rdepth)
  #-acl2-rewrite-meter ; normal case (no stats)
  `(1-f ,rdepth))

(defun add-rewrite-args (extra-formals keyword-extra-formals alist)

; extra-formals is '(type-alist ...)
; keyword-extra-formals is '(:type-alist ...)
; alist pairs keyword extra formals to terms

; We return a list in 1:1 correspondence with extra-formals.  The
; element corresponding to an extra-formal is the value specified by
; the alist if one is so specified, otherwise it is the extra-formal
; itself.

  (cond ((null extra-formals) nil)
        (t (cons (let ((pair (assoc-eq (car keyword-extra-formals)
                                       alist)))
                   (cond (pair (cdr pair))
                         (t (car extra-formals))))
                 (add-rewrite-args (cdr extra-formals)
                                   (cdr keyword-extra-formals)
                                   alist)))))

(defrec step-limit-record

; See the Essay on Step-limits.

; The state global 'step-limit-record is bound to one of these records at the
; start of an event by with-ctx-summarized (specifically, by the call of
; with-prover-step-limit in save-event-state-globals).  Then, :start is the
; initial value of state global 'last-step-limit for that event; :strictp
; indicates whether an error should occur if the step-limit is exceeded; and
; :sub-limit is the step-limit to use for sub-events, if any, where nil
; indicates that the sub-limit should be limited by the current step-limit.

  (start strictp . sub-limit)
  t)

(defun step-limit-start (state)

; Return the starting value of step-limit in the present context.  See defrec
; step-limit-record.

  (let ((rec (f-get-global 'step-limit-record state)))
    (cond (rec (access step-limit-record rec :start))
          (t (step-limit-from-table (w state))))))

(defun step-limit-strictp (state)

; Warning: Keep this in sync with code in with-prover-step-limit-fn near the
; comment there about step-limit-strictp.

; Return true if in the present context, we are to cause an error if the
; step-limit is exceeded.  See defrec step-limit-record.

  (let ((rec (f-get-global 'step-limit-record state)))
    (cond (rec (access step-limit-record rec :strictp))
          (t nil))))

(defun initial-step-limit (wrld state)

; Warning: Keep this in sync with code in with-prover-step-limit-fn near the
; comment there about initial-step-limit.

; See the Essay on Step-limits.

; This function returns the current step limit.  If 'step-limit-record has a
; non-nil value (see defrec step-limit-record), then we are already tracking
; step-limits in the state, so we return the value of 'last-step-limit.
; Otherwise the acl2-defaults-table is consulted for the step-limit.

  (declare (xargs :guard ; also needs rec, bound below, to be suitable
                  (and (plist-worldp wrld)
                       (alistp (table-alist 'acl2-defaults-table wrld))
                       (let ((val (cdr (assoc-eq :step-limit
                                                 (table-alist 'acl2-defaults-table
                                                              wrld)))))
                         (or (null val)
                             (and (natp val)
                                  (<= val *default-step-limit*))))
                       (state-p state)
                       (boundp-global 'step-limit-record state)
                       (boundp-global 'last-step-limit state))))
  (let ((rec (f-get-global 'step-limit-record state)))
    (cond (rec (or (access step-limit-record rec :sub-limit)
                   (f-get-global 'last-step-limit state)))
          (t (step-limit-from-table wrld)))))

(defun step-limit-error1 (ctx str start where state)
  (declare (ignorable state)) ; only used in raw Lisp
  #-acl2-loop-only
  (when *step-limit-error-p*
    (er soft ctx str start where)
    (setq *step-limit-error-p* 'error)
    (throw 'step-limit-tag ; irrelevant value
           t))
  (the (signed-byte 30)
    (prog2$ (er hard? ctx str start where)
            -1)))

(defmacro step-limit-error (superior-context-p)

; If superior-context-p is t then we return an error triple; if it is nil, we
; return -1, possibly causing a hard error or a throw.

  (let ((str "The prover step-limit, which is ~x0 in the ~@1, has been ~
              exceeded.  See :DOC set-prover-step-limit.")
        (ctx ''step-limit))
    (cond
     (superior-context-p
      `(er soft ,ctx
           ,str
           (step-limit-start state)
           "context immediately above the one just completed"))
     (t
      `(the-fixnum
        (step-limit-error1 ,ctx
                           ,str
                           (step-limit-start state)
                           "current context"
                           state))))))

(defmacro decrement-step-limit (step-limit)

; We make this event a macro for improved performance.

  (declare (xargs :guard

; By insisting that the formal is a symbol, we guarantee that its repeated
; reference below does not result in repeated evaluation of other than the
; current binding of a symbol.

                  (symbolp step-limit)))
  `(the (signed-byte 30)
        (cond
         ((< 0 (the-fixnum ,step-limit))
          (1-f ,step-limit))
         ((eql -1 (the-fixnum ,step-limit))
          -1)
         (t (assert$ (eql 0 (the-fixnum ,step-limit))
                     (cond ((step-limit-strictp state)
                            (step-limit-error nil))
                           (t -1)))))))

(defmacro rewrite-entry (&rest args)
  (declare (xargs :guard (and (true-listp args)
                              (consp (car args))
                              (keyword-value-listp (cdr args)))))
  (let* ((call0
          (append (car args)
                  (add-rewrite-args '( ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv pequiv-info
                                      wrld state
                                      fnstack ancestors
                                      backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)
                                    '( ; &extra formals -- keyword versions
                                      :rdepth :step-limit
                                      :type-alist :obj :geneqv :pequiv-info
                                      :wrld :state
                                      :fnstack :ancestors
                                      :backchain-limit
                                      :simplify-clause-pot-lst
                                      :rcnst :gstack :ttree)
                                    (plist-to-alist
                                     (if (eq (caar args) 'rewrite)
                                         (remove-keyword
                                          :step-limit ; dealt with below
                                          (cdr args))
                                       (cdr args))))))
         (call
          (cond
           ((not (eq (caar args) 'rewrite))
            call0)
           (t (let ((call1
                     `(let ((step-limit
                             (decrement-step-limit step-limit)))
                        (declare (type (signed-byte 30) step-limit))
                        ,call0))
                    (step-limit-tail (assoc-keyword :step-limit (cdr args))))
                (cond (step-limit-tail
                       `(let ((step-limit ,(cadr step-limit-tail)))
                          ,call1))
                      (t call1)))))))
    #+acl2-loop-only
    call
    #-acl2-loop-only
    (if (member-eq (caar args)

; We could omit relieve-hyp-synp in the list below, even though it too calls
; push-gframe, because relieve-hyp-synp is not called under rewrite-entry.  But
; we add it just in case that changes.

                   '(rewrite rewrite-with-lemma add-terms-and-lemmas
                             add-linear-lemma non-linear-arithmetic
                             relieve-hyp-synp))

; We restore *deep-gstack* to its value from before the call.  We really only
; need to do that for dmr monitoring, so that there aren't stale frames on
; *deep-gstack* when printing both the gstack and pstk (see dmr-string).  But
; the prog1 and setq seem cheap so we clean up after ourselves in all cases.

; WARNING: Gstack must be bound where rewrite-entry is called for the above
; values of (caar args).

        `(cond ((or (f-get-global 'gstackp state)
                    (f-get-global 'dmrp state))

; We could call our-multiple-value-prog1 instead of multiple-value-prog1 in the
; #+cltl2 case below, which would avoid the need for a separate #-cltl2 case.
; However, for non-ANSI GCL we want to take advantage of the fact that all
; functions in the rewrite nest return a first argument (the new step-limit)
; that is a fixnum, but the compiler doesn't use that information when a prog1
; call is used.  So we manage the non-ANSI case (including non-ANSI GCL)
; ourselves.

                #+cltl2
                (multiple-value-prog1
                 ,call
                 (setq *deep-gstack* gstack))
                #-cltl2
                ,(let ((var (gensym)))
                   `(let ((,var ,call))
                      (declare (type (signed-byte 30) ,var))
                      (setq *deep-gstack* gstack)
                      ,var)))
               (t ,call))
      call)))

; The following object, a fake rune, will be pushed as a 'lemma to
; indicate that the "linear arithmetic rule" was used.

(defconst *fake-rune-for-linear*
  '(:FAKE-RUNE-FOR-LINEAR nil))

; We now develop the code used in path maintenance and monitor.

; The goal stack is a list of frames, each of the form

(defrec gframe (sys-fn bkptr . args) t)

; where sys-fn is a system function name, e.g., REWRITE, bkptr is an
; arbitrary object supplied by the caller to the sys-fn that indicates
; why the call was made (and must be interpreted by the caller, not
; the called sys-fn), and args are some subset of the args to sys-fn.

; WARNING: We use bkptr as a "hash index" uniquely identifying a hypothesis
; among the hypotheses of a rewrite rule when we are memoizing relieve-hyp.
; Thus, bkptr is a positive integer inside the functions relieve-hyps1 and
; relieve-hyp and their peers.

; Note: Nqthm included a count in each frame which was the number of
; frames generated so far and could be used to determine the
; "persistence" of each frame.  I am skipping that for the present
; because it means linearizing the code to pass the incremented count
; across args, etc., unless it is done in an extra-logical style.  A
; better idea would be to connect the goal stack to the comment window
; and actually display it so that persistence became visual again.

#-acl2-loop-only
(defparameter *deep-gstack* nil)

(defmacro push-gframe (sys-fn bkptr &rest args)

; This macro allows us to write
; (let ((gstack (push-gframe 'rewrite bkptr term alist obj)))
;   ...)
; without actually doing any conses if we are not maintaining the goal stack.
; Notice that it conses the new frame onto the value of the variable gstack, so
; to use this macro that variable must be the gstack.

; Observe the use of list* below.  Thus, the :args component of the frame built
; is a DOTTED list of the args provided, i.e., the last arg is in the final
; cdr, not the final cadr.  Thus, (push-gframe 'rewrite 3 'a 'b 'c 'd) builds a
; frame with :args '(a b c . d).  Note in particular the effect when only one
; arg is provided: (push-gframe 'rewrite 3 'a) builds a frame with :args 'a.
; One might wish in this case that the field name were :arg.

  #+acl2-loop-only
  `(cond ((or (f-get-global 'gstackp state)
              (f-get-global 'dmrp state))
          (cons (make gframe
                      :sys-fn ,sys-fn
                      :bkptr ,bkptr
                      :args (list* ,@args))
                gstack))
         (t nil))
  #-acl2-loop-only
  `(progn (when (or (f-get-global 'gstackp state)
                    (f-get-global 'dmrp state))
            (setq *deep-gstack*
                  (cons (make gframe
                              :sys-fn ,sys-fn
                              :bkptr ,bkptr
                              :args (list* ,@args))
                        gstack))
            (when (f-get-global 'dmrp state)
              (dmr-display))
            *deep-gstack*)))

(defmacro initial-gstack (sys-fn bkptr &rest args)

; This macro is just (push-gframe sys-fn bkptr ,@args) except it is done on an
; empty gstack.  Thus, it builds an initial gstack with the top-most frame as
; specified.  The frame is built by push-gframe, so all frames are built by
; that macro.

; This is also a convenient place to reset *add-polys-counter*, which is used
; by dmr-string.

  `(let ((gstack nil))
     #-acl2-loop-only (setq *add-polys-counter* 0)
     (push-gframe ,sys-fn ,bkptr ,@args)))

(defun tilde-@-bkptr-phrase (calling-sys-fn called-sys-fn bkptr)

; Warning: Keep this in sync with tilde-@-bkptr-string.

; This function builds a ~@ phrase explaining how two adjacent frames
; are related, given the calling sys-fn, the called sys-fn and the
; bkptr supplied by the caller.  See cw-gframe for the use of this
; phrase.

  (case called-sys-fn
    (rewrite
     (cond ((integerp bkptr)
            (cond ((member-eq calling-sys-fn
                              '(rewrite-with-lemma
                                rewrite-quoted-constant-with-lemma
                                add-linear-lemma))
                   (msg " the atom of the ~n0 hypothesis" (list bkptr)))
                  ((eq calling-sys-fn 'simplify-clause)
                   (msg " the atom of the ~n0 literal" (list bkptr)))
                  (t (msg " the ~n0 argument" (list bkptr)))))
           ((consp bkptr)
            (msg " the rhs of the ~n0 hypothesis"
                 (list (cdr bkptr))))
           ((symbolp bkptr)
            (case bkptr
              (body " the body")
              (lambda-body " the lambda body")
              (lambda-object-body " the body of the lambda object")
              (rewritten-body " the rewritten body")
              (expansion " the expansion")
              (equal-consp-hack-car " the equality of the cars")
              (equal-consp-hack-cdr " the equality of the cdrs")
              (rhs " the rhs of the conclusion")
              (meta " the result of the metafunction")
              (nth-update " the result of the nth/update rewriter")
              (multiply-alists2 " the product of two polys")
              (forced-assumption " a forced assumption")
              (proof-builder " proof-builder top level")
              (otherwise (er hard 'tilde-@-bkptr-phrase
                             "When ~x0 calls ~x1 we get an unrecognized ~
                                      bkptr, ~x2."
                             calling-sys-fn called-sys-fn bkptr))))
           (t (er hard 'tilde-@-bkptr-phrase
                  "When ~x0 calls ~x1 we get an unrecognized bkptr, ~x2."
                  calling-sys-fn called-sys-fn bkptr))))
    ((rewrite-with-lemma setup-simplify-clause-pot-lst simplify-clause
                         add-terms-and-lemmas add-linear-lemma
                         non-linear-arithmetic synp)
     "")
    (t (er hard 'tilde-@-bkptr-phrase
           "When ~x0 calls ~x1 we get an unrecognized bkptr, ~x2."
           calling-sys-fn called-sys-fn bkptr))))

(defmacro get-rule-field (x field)

; X is a rewrite-rule or linear-lemma record.  If the field is inappropriate
; but the field is one as expected by the guard, then we return the special
; value :get-rule-field-none.

  (declare (xargs :guard (let ((fields '(:rune :hyps :lhs :rhs)))
                           (and (not (member-eq x fields))
                                (member-eq field fields)))))
  `(let ((x ,x))
     (cond ((eq (record-type x) 'rewrite-rule)
            (access rewrite-rule x ,field))
           ((eq (record-type x) 'linear-lemma)
            ,(cond ((member-eq field '(:lhs :rhs)) :get-rule-field-none)
                   (t `(access linear-lemma x ,field))))
           (t
            (er hard 'get-rule-field
                "The object ~x0 is neither a rewrite-rule record nor a ~
                 linear-lemma record."
                x)))))

(defun cw-gframe (i calling-sys-fn frame evisc-tuple)

; Warning: Keep this in sync with dmr-interp.

; This prints a gframe, frame, which is known to be frame number i and
; was called by calling-sys-fn.

  (case (access gframe frame :sys-fn)
        (simplify-clause

; We are tempted to ignore evisc-tuple in this case and print the whole clause.
; We have seen situations where we print ellipses after the 4th literal of the
; clause and then say that the next frame is simplifying the "fifth literal."
; On the other hand, we have seen huge clauses bring cw-gframe to its knees.
; So we compromise by using the evisc-tuple supplied.

         (cw "~x0. Simplifying the clause~%     ~Y12"
             i
             (access gframe frame :args)
             evisc-tuple))
        (setup-simplify-clause-pot-lst
         (cw "~x0. Setting up the linear pot list for the clause~%     ~Y12"
             i
             (access gframe frame :args)
             evisc-tuple))
        (rewrite
         (let ((term (car (access gframe frame :args)))
               (alist (cadr (access gframe frame :args)))
               (obj (cddr (access gframe frame :args))))
           (cw "~x0. Rewriting (to ~@6)~@1,~%     ~Y23,~#4~[~/   under the ~
                substitution~%~*5~]"
               i
               (tilde-@-bkptr-phrase calling-sys-fn
                                     'rewrite
                                     (access gframe frame :bkptr))
               term
               evisc-tuple
               (if alist 1 0)
               (tilde-*-alist-phrase alist evisc-tuple 5)
               (cond ((eq obj nil) "falsify")
                     ((eq obj t) "establish")
                     (t "simplify")))))
        ((rewrite-with-lemma
          rewrite-quoted-constant-with-lemma
          add-linear-lemma)
         (cw "~x0. Attempting to apply ~F1 to~%     ~Y23"
             i
             (get-rule-field (cdr (access gframe frame :args)) :rune)
             (car (access gframe frame :args))
             evisc-tuple))
        (add-terms-and-lemmas
         (cw "~x0. Attempting to apply linear arithmetic to ~@1~%     ~Y23"
             i
             (let ((obj (cdr (access gframe frame :args))))
               (cond ((eq obj nil) (msg "falsify the term list"))
                     ((eq obj t) "establish the term list")
                     (t ; '?, a special mark for setting up the pot-lst
                      "the clause")))
             (car (access gframe frame :args))
             evisc-tuple))
        (non-linear-arithmetic
         (cw "~x0. Attempting to apply non-linear arithmetic to the list of ~
              ~x1 var~#2~[~/s~]:~%     ~Y23"
             i
             (length (access gframe frame :args))
             (access gframe frame :args)
             evisc-tuple))
        (synp
         (let ((synp-fn (access gframe frame :args)))
           (cw "~x0. Entering ~x1 for hypothesis ~x2~%"
               i synp-fn (access gframe frame :bkptr))))
        (otherwise (er hard 'cw-gframe
                       "Unrecognized sys-fn, ~x0"
                       (access gframe frame :sys-fn)))))

(defun cw-gstack1 (i calling-sys-fn lst evisc-tuple)
  (cond ((null lst) nil)
        (t (prog2$ (cw-gframe i calling-sys-fn (car lst) evisc-tuple)
                   (cw-gstack1 (1+ i)
                               (access gframe (car lst) :sys-fn)
                               (cdr lst) evisc-tuple)))))

(defun cw-gstack-fn (evisc-tuple frames)

; And here is how we print the whole goal stack to the comment window.

; Note: I am unhappy about the use of the comment window here.  It pre-dates
; the invention of wormhole and its undoable changes to state.  I sometimes
; think I should make this function just print the stack to an arbitrary
; channel and in wormhole that can be *standard-co*.  But I have bigger fish to
; fry right now, namely the use of wormhole to implement an apparently (but not
; actually) recursive break-lemma.  So I'm leaving this little wart to think
; about later.

; Since this function is a hack anyhow, we implicitly refer to *deep-gstack*
; without passing it in.

  (let ((gstack #-acl2-loop-only *deep-gstack*
                #+acl2-loop-only nil)
        (ctx 'cw-gstack))
    (cond
     ((null gstack)
      (cw "There is no gstack to print.  If you have enabled stack monitoring ~
           with ``:BRR t'' this is likely due to the loop you wish to ~
           investigate occurring in so-called preprocessing, where monitoring ~
           is not done, rather than in the rewriter proper.  You may obtain ~
           better results by replaying the problematic event with a hint ~
           of:~%((\"Goal\" :DO-NOT '(preprocess)).~%See :DOC hints, in ~
           particular the discussion of :DO-NOT.~%"))
     ((and evisc-tuple
           (not (standard-evisc-tuplep evisc-tuple)))
      (er hard ctx
          "Illegal :evisc-tuple argument to ~x0: ~x1.  See :DOC cw-gstack."
          'cw-gstack evisc-tuple))
     ((not (or (null frames)
               (and (integerp frames) (< 0 frames))
               (and (true-listp frames)
                    (eql (length frames) 2)
                    (natp (car frames))
                    (natp (cadr frames))
                    (<= (car frames) (cadr frames)))))
      (er hard ctx
          "Illegal :frames argument to ~x0: ~x1.  See :DOC cw-gstack."
          'cw-gstack frames))
     (t
      (let ((start (cond ((or (null frames)
                              (integerp frames))
                          1)
                         ((<= (car frames) (length gstack))
                          (car frames))
                         (t (length gstack)))))
        (cw-gstack1 start nil
                    (cond ((null frames)
                           (reverse gstack))
                          (t
                           (let* ((rev-gstack (reverse gstack))
                                  (len (length gstack))
                                  (n (min (if (integerp frames)
                                              frames
                                            (cadr frames))
                                          len)))
                             (nthcdr (1- start) (take n rev-gstack)))))
                    evisc-tuple))))))

(defmacro cw-gstack (&key (evisc-tuple 'nil evisc-tuplep) (frames 'nil))
  (declare (xargs :guard t))
  `(cw-gstack-fn ,(if evisc-tuplep
                      evisc-tuple
                    '(term-evisc-tuple t state))
                 ,frames))

; Essay on "Break-Rewrite"
; Essay on BRR

; We wish to develop the illusion of a recursive function we will call
; "break-rewrite".  In particular, when a rule is to be applied by
; rewrite-with-lemma and that rule is monitored (i.e., its rune is on
; brr-monitored-runes) then we imagine the rule is actually applied by
; "break-rewrite", which is analogous to rewrite-with-lemma but instrumented to
; allow the user to watch the attempt to apply the rule.  Rewrite-fncall and
; add-linear-lemma are similarly affected.  Because we find "break-rewrite" a
; tedious name (in connection with user-available macros for accessing context
; sensitive information) we shorten it to simply brr when we need a name that
; is connected with the implementation of "break-rewrite."  There is no
; "break-rewrite" function -- its presence is an illusion -- and we reserve the
; string "break-rewrite" to refer to this mythical function.

; Rather than actually implement "break-rewrite" we sprinkle "break points"
; through the various rewrite functions.  These break points are the functions
; brkpt1 and brkpt2.  The reason we do this is so that we don't have to
; maintain two parallel versions of rewrite-with-lemma (and others) as
; discussed above.  It is not clear this is justification for what is a
; surprisingly complicated alternative, especially since a recursive call to
; the rewriter would make it possible to :EVAL more than once.  (For example,
; if the :EVAL says that the attempt failed because hyp 3 rewrote to xyz, we
; might want to :monitor some other rules and do the :EVAL again to see what
; went wrong.)  But since we haven't pursued any other approach, it is not
; clear that the complications are isolated in this one.

; The main complication is that if we really had a recursive "break-rewrite"
; then we could have local variables associated with each attempt to apply a
; given rule.  This would allow us, for example, to set a variable early in
; "break-rewrite" and then test it late, without having to worry that recursive
; calls of "break-rewrite" in between will see the setting.  An additional
; complication is that to interact with the user we must enter a wormhole and
; thus have no effect on the state.

; Our first step is to implement a slightly different interface to wormholes that
; will provide us with global variables that retain their values from one exit to
; the next entrance but that can be overwritten conveniently upon entrance.  See
; brr-wormhole below.  Assume that we have such a wormhole interface providing
; what we call "brr-globals."

; We use the notion of brr-globals to implement "brr-locals."  Of course, what
; we implement is a stack.  That stack is named brr-stack and it is a
; brr-global.  By virtue of being a brr-global it retains its value from one
; call of brr-wormhole to the next.

; Imagine then that we have this stack.  Its elements are frames.  Each frame
; specifies the local bindings of various variables.  Inside brkpt1 and brkpt2
; we access these "brr-locals" via the top-most frame on the stack.  Brkpt1
; pushes a new frame, appropriately binding the locals.  brkpt2 pops that frame
; when it exits "break-rewrite".

; For sanity, each frame will contain the gstack for the brkpt1 that built it.
; Any function accessing a brr-local will present its own gstack as proof that
; it is accessing the right frame.  One might naively assume that the presented
; gstack will always be equal to the gstack in the top-most frame and that
; failure of this identity check might as well signal a hard error.  How might
; this error occur?  The most obvious route is that we have neglected to pop a
; frame upon exit from the virtual "break-rewrite", i.e., we have forgotten to
; call brkpt2 on some exit of rewrite-with-lemma.  More devious is the
; possibility that brkpt2 was called but failed to pop because we have
; misinterpreted our various flags and locally monitored runes.  These routes
; argue for a hard error because they ought never to occur and the error
; clearly indicates a coding mistake.  But it is possible for the stack to get
; "out of sync" in an entirely user controlled way!

; Suppose we are in brkpt1.  It has pushed a frame with the current gstack.
; The user, typing to "break-rewrite" (the brr-wormhole in brkpt1) invokes the
; theorem prover and we enter another brkpt1.  It pushes its frame.  The user
; issues the command to proceed (i.e., to attempt to establish the hypotheses).
; The inner brkpt1 is terminated and control returns to rewrite.  Note that we
; are still in the inner "break-rewrite" because we are pursuing the hyps of
; the inner rule.  Consistent with this note is the fact that the stack
; contains two frames, the top-most one being that pushed by the inner brkpt1.
; Control is flowing toward the inner brkpt2 where, normally, the user would
; see the results of trying to establish the inner hyps.  But then the user
; aborts.  Control is thrown to the outer brkpt1, because all of this action
; has occurred in response to a recursive invocation of the theorem prover from
; within that wormhole.  But now the stack at that brkpt1 is out of sync: the
; gstack of the wormhole is different from the gstack in the top-most frame.
; So we see that this situation is unavoidable and must be handled gracefully.

; Therefore, to access the value of a brr-local we use a function which
; patiently looks up the stack until it finds the right frame.  It simply
; ignores "dead" frames along the way.  We could pop them off, but then we
; would have to side-effect state to update the stack.  The way a frame binds
; local variables is simply in an alist.  If a variable is not bound at the
; right frame we scan on up the stack looking for the next binding.  Thus,
; variables inherit their bindings from higher levels of "break-rewrite" as
; though the function opened with (let ((var1 var1) (var2 var2) ...) ...).
; When we "pop a frame" we actually pop all the frames up to and including the
; one for the gstack presented to pop.  Finally, we need the function that
; empties the stack.

; So much for the overview.  We begin by implementing brr-wormholes and
; brr-globals.

; While a normal wormhole provides one "global variable" that persists over
; entries and exits (namely, in the wormhole data field of the
; wormhole-status), the brr-wormhole provides several.  These are called
; "brr-globals."  The implementation of brr-globals is in two places: entry to
; and exit from the wormhole.  The entry modification is to alter the supplied
; form so that it first moves the variable values from the wormhole-input and
; previous wormhole-status vectors into true state global variables.  See
; brr-wormhole.  The exit modification is to provide exit-brr-wormhole which
; moves the final values of the globals to the wormhole-status vector to be
; preserved for the next entrance.

; NOTE: To add a new brr-global, look for all the functions containing the
; string "Note: To add a new brr-global" and change them appropriately.  No
; other changes are necessary (except, of course, passing in the desired values
; for the new global and using it).

(defun restore-brr-globals1 (name new-alist old-alist)

; Retrieve the value of name under new-alist, if a value is specified;
; otherwise use the value of name under old-alist.  See brr-wormhole.

  (let ((pair (assoc-eq name new-alist)))
    (cond (pair (cdr pair))
          (t (cdr (assoc-eq name old-alist))))))

(defun restore-brr-globals (state)

; We assign incoming values to the brr-globals.  When brr-wormhole
; enters a wormhole, this function is the first thing that is done.  See
; brr-wormhole.

; NOTE: To add a new brr-global, this function must be changed.

  (let ((new-alist (f-get-global 'wormhole-input state))
        (old-alist (wormhole-data (f-get-global 'wormhole-status state))))
    (pprogn
     (f-put-global 'brr-monitored-runes
                   (restore-brr-globals1 'brr-monitored-runes
                                         new-alist old-alist)
                   state)
     (f-put-global 'brr-evisc-tuple
                   (restore-brr-globals1 'brr-evisc-tuple
                                         new-alist old-alist)
                   state)
     (f-put-global 'brr-stack
                   (restore-brr-globals1 'brr-stack
                                         new-alist old-alist)
                   state)
     (f-put-global 'brr-gstack
                   (restore-brr-globals1 'brr-gstack
                                         new-alist old-alist)
                   state)
     (f-put-global 'brr-alist
                   (restore-brr-globals1 'brr-alist
                                         new-alist old-alist)
                   state))))

(defun save-brr-globals (state)

; We collect into an alist all of the brr-globals and their current values and
; store that alist into the wormhole data field of (@ wormhole-status).  When
; exiting from a brr-wormhole, this is the last thing that ought to be done.
; See exit-brr-wormhole.

; NOTE: To add a new brr-global, this function must be changed.

  (f-put-global 'wormhole-status
                (make-wormhole-status
                 (f-get-global 'wormhole-status state)
                 :ENTER
                 (list
                  (cons 'brr-monitored-runes
                        (f-get-global 'brr-monitored-runes state))
                  (cons 'brr-evisc-tuple
                        (f-get-global 'brr-evisc-tuple state))
                  (cons 'brr-stack
                        (f-get-global 'brr-stack state))
                  (cons 'brr-gstack
                        (f-get-global 'brr-gstack state))
                  (cons 'brr-alist
                        (f-get-global 'brr-alist state))))
                state))

(defun get-brr-global (var state)

; This function should be used whenever we wish to access a brr-global.  That
; is, we should write (get-brr-global 'brr-stack state) instead of either
; (f-get-global 'brr-stack state) or (@ brr-stack), even those these
; alternative forms are equivalent when we are in a brr-wormhole.  But if we
; are not in a brr-wormhole, these alternative forms might cause arbitrary lisp
; errors because the brr-globals are not (generally) bound outside of wormholes
; (though there is nothing to prevent us from using the same symbols as
; "normal" state globals -- their values would just be unavailable to us from
; within brr-wormholes because they get over-written upon entry to the
; wormhole.)  Thus, this function checks that the variable really is bound and
; causes a hard error if it is not.  That is generally an indication that a
; function intended to be used only inside wormholes is being called outside.

; NOTE: To add a new brr-global, this function must be changed.

  (cond ((eq (f-get-global 'wormhole-name state) 'brr)
         (case var
               (brr-monitored-runes
                (f-get-global 'brr-monitored-runes state))
               (brr-evisc-tuple
                (f-get-global 'brr-evisc-tuple state))
               (brr-stack
                (f-get-global 'brr-stack state))
               (brr-gstack
                (f-get-global 'brr-gstack state))
               (brr-alist
                (f-get-global 'brr-alist state))
               (otherwise
                (illegal 'get-brr-global
                         "Unrecognized brr-global, ~x0."
                         (list (cons #\0 var))))))
        (t (illegal 'get-brr-global
                    "It is illegal to call get-brr-global unless you are ~
                     under break-rewrite and you are not.  The argument to ~
                     get-brr-global was ~x0."
                    (list (cons #\0 var))))))

(defun exit-brr-wormhole (state)

; This function should be called on every exit from a brr-wormhole.  It saves
; the brr-globals into the wormhole-status to be preserved for future entries
; and then it returns (value :q) which will cause us to exit the wormhole.

  (pprogn (save-brr-globals state)
          (value :q)))

(defmacro brr-wormhole (entry-lambda input-alist test-form aliases)

; A brr-wormhole is a particular kind of wormhole.  A quick summary of the
; differences:
; (0) while our normal convention is that the entry code for all wormholes
;     should be :ENTER, brr-wormholes really do use the :SKIP option and
;     toggle between :SKIP and :ENTER frequently; the status of the
;     brr-wormhole is thus (:key data), where data is the alist mapping
;     brr-globals to their values as described below
; (1) brr-wormhole implements brr-global variables which are set
;     from input-alist (or else retain their values from the
;     last exit of the 'brr wormhole).
; (2) test-form returns (value t) or (value nil) indicating whether
;     a break is to occur.
; (3) the LD specials are manipulated so that no output appears before
;     test-form is eval'd and an error in the test-form throws you out of
;     the wormhole.  If the test-form returns (value nil), the wormhole
;     entry/exit are entirely silent.

  (let ((aliases `(append ,aliases
                          '((:exit
                             0 (lambda nil
                                 (prog2$ (cw "The keyword command :EXIT is ~
                                              disabled inside BRR.  Exit BRR ~
                                              with :ok or use :p! to pop or ~
                                              :a! to abort; or exit ACL2 ~
                                              entirely with ~x0.~%"
                                             '(exit))
                                         (value :invisible))))
                            (:quit
                             0 (lambda nil
                                 (prog2$ (cw "The keyword command :QUIT is ~
                                              disabled inside BRR.  Quit BRR ~
                                              with :ok or use :p! to pop or ~
                                              :a! to abort; or quit ACL2 ~
                                              entirely with ~x0.~%"
                                             '(quit))
                                         (value :invisible))))))))
    `(wormhole 'brr
               ,entry-lambda
               ,input-alist
               `(pprogn (restore-brr-globals state)
                        (er-progn
                         (set-ld-keyword-aliases! ,,aliases)
                         (set-ld-prompt 'brr-prompt state)

; The above reference to the function symbol brr-prompt is a little startling
; because we haven't defined it yet.  But we will define it before we use this
; macro.


                         (mv-let (erp val state)
                                 ,,test-form
                                 (cond
                                  (erp (exit-brr-wormhole state))
                                  (val
                                   (er-progn (set-ld-error-action :continue state)
; The aliases had better ensure that every exit  is via exit-brr-wormhole.
                                             (value :invisible)))
                                  (t (exit-brr-wormhole state))))))
               :ld-prompt  nil
               :ld-missing-input-ok nil
               :ld-pre-eval-filter :all
               :ld-pre-eval-print  nil
               :ld-post-eval-print :command-conventions
               :ld-evisc-tuple nil
               :ld-error-triples  t
               :ld-error-action :error
               :ld-query-control-alist nil
               :ld-verbose nil)))

(defun initialize-brr-stack (state)

; This is a no-op that returns nil.  But it has the secret side effect of
; setting the brr-global brr-stack to nil.  We don't want to reset all the
; brr-globals: brr-monitored-runes and brr-evisc-tuple should persist.  The
; others are irrelevant because they will be assigned before they are read.

  (and (f-get-global 'gstackp state)
       (brr-wormhole '(lambda (whs)
                        (set-wormhole-entry-code whs :ENTER))
                     '((brr-stack . nil))
                     '(value nil)
                     nil)))

; This completes the implementation of brr-wormholes (except that we must be sure to
; exit via exit-brr-wormhole always).

; We now move on to the implementation of brr-locals.

(defun lookup-brr-stack (var-name stack)

; See the Essay on "Break-Rewrite".  Stack is a list of frames.  Each frame is
; of the form (gstack' . alist).  We assoc-eq up the alists of successive
; frames until we find one binding var-name.  We return the value with which
; var-name is paired, or else nil if no binding is found.

  (cond ((endp stack) nil)
        (t (let ((temp (assoc-eq var-name (cdar stack))))
             (cond (temp (cdr temp))
                   (t (lookup-brr-stack var-name (cdr stack))))))))

(defun clean-brr-stack1 (gstack stack)
  (declare (xargs :guard (alistp stack)))
  (cond ((endp stack)
         nil)
        ((equal gstack (caar stack)) stack)
        (t (clean-brr-stack1 gstack (cdr stack)))))

(defconst *cryptic-brr-message*
  "If you are seeing this message after you have caused a console interrupt ~
   (or otherwise have made a break into Lisp) or during a new prover call ~
   made from within BRR, then it is likely that this is a bit of routine BRR ~
   housekeeping.  (In the latter case, of a new prover call made from within ~
   BRR, you can probably avoid this message by calling :brr nil before making ~
   that new prover call.)  Otherwise, the ACL2 implementors would appreciate ~
   a script showing how to reproduce this message.")

(defun clean-brr-stack (gstack stack)

; See the Essay on "Break-Rewrite".  Stack is a list of frames.  Each frame is
; of the form (gstack' . alist), where the frames are ordered so that each
; successive gstack' is at a higher level than the previous one.  (But note
; that they do not ascend in increments of one.  That is, suppose the
; top frame of stack is marked with gstack' and the next-to-top frame is
; marked with gstack''.  Then gstack' is an extension of gstack'', i.e.,
; some cdr of gstack' is gstack''.  We sweep down stack looking for
; the frame marked by gstack.  We return the stack that has this frame on
; top, or else we return nil.

; We used (Version_2.7 and earlier) to cause a hard error if we did
; not find a suitable frame because we thought it indicated a coding
; error.  Now we just return the empty stack because this situation
; can arise through interrupt processing.  Suppose we are in rewrite
; and push a new frame with brkpt1.  We're supposed to get to brkpt2
; eventually and pop it.  An interrupt could prevent that, leaving the
; frame unpopped.  Suppose that is the last time a brkpt occurs in
; that simplification.  Then the old stack survives.  Suppose the
; waterfall carries out an elim and then brings us back to
; simplification.  Now the gstack is completely different but the
; preserved brr-stack in *wormhole-status-alist* is still the old one.
; Clearly, we should ignore it -- had no interrupt occurred it would
; have been popped down to nil.

  (declare (xargs :guard (alistp stack)))
  (let ((cleaned-stack (clean-brr-stack1 gstack stack)))
    (prog2$
     (if (not (equal cleaned-stack stack))
         (cw "~%~%Cryptic BRR Message 1:  Sweeping dead frames off ~
              brr-stack.  ~@0~%~%"
             *cryptic-brr-message*)

; If anybody ever reports the problem described above, it indicates
; that frames are being left on the brr-stack as though the
; pop-brr-stack-frame supposedly performed by brkpt2 is not being
; executed.  This could leave the brr-stack arbitrarily wrong, as a
; non-nil stack could survive into the simplification of a subsequent,
; independent subgoal sharing no history at all with brr-gstack.

       nil)
     cleaned-stack)))

(defun get-brr-local (var state)

; This function may be used inside code executed under "break-rewrite".  It is
; NOT for use in general purpose calls of wormhole because it is involved with
; the local variable illusion associated with "break-rewrite".  A typical use
; is (get-brr-local 'unify-subst state) which fetches the local binding of
; 'unify-subst in the frame of brr-stack that is labeled with the current
; brr-gstack.

  (let ((clean-stack (clean-brr-stack (get-brr-global 'brr-gstack state)
                                      (get-brr-global 'brr-stack state))))
    (lookup-brr-stack var clean-stack)))

(defun put-brr-local1 (gstack var val stack)

; See the Essay on "Break-Rewrite" and the comment in brr-@ above.  We assign
; val to var in the frame labeled by gstack.  This function returns the
; resulting stack but does not side-effect state (obviously).  Dead frames at
; the top of the stack are removed by this operation.

  (let ((clean-stack (clean-brr-stack gstack stack)))
    (cons (cons gstack (put-assoc-eq var val (cdar clean-stack)))
          (cdr clean-stack))))

(defun put-brr-local (var val state)

; This function may be used inside code executed within "break-rewrite".  It is
; NOT for use in general purpose calls of wormhole because it is involved with
; the local variable illusion associated with "break-rewrite".  A typical use
; is (put-brr-local 'unify-subst val state) which stores val as the local
; binding of 'unify-subst in the frame of brr-stack that is labeled with the
; current brr-gstack.

  (f-put-global 'brr-stack
                (put-brr-local1 (get-brr-global 'brr-gstack state)
                                var val
                                (get-brr-global 'brr-stack state))
                state))

(defun put-brr-local-lst (alist state)
  (cond ((null alist) state)
        (t (pprogn (put-brr-local (caar alist)  (cdar alist) state)
                   (put-brr-local-lst (cdr alist) state)))))

(defun some-cdr-equalp (little big)

; We return t if some cdr of big, including big itself, is equal to little.

  (cond ((equal little big) t)
        ((null big) nil)
        (t (some-cdr-equalp little (cdr big)))))

(defun push-brr-stack-frame (state)

; This function may be used inside code executed within "break-rewrite".  It
; pushes the new frame, (gstack . alist) on the brr-stack, where gstack is the
; current value of (get-brr-global 'brr-gstack state) and alist is
; (get-brr-global 'brr-alist state).

  (let ((gstack (get-brr-global 'brr-gstack state))
        (brr-stack (get-brr-global 'brr-stack state)))
    (cond
     ((or (null brr-stack)
          (and (not (equal (caar brr-stack) gstack))
               (some-cdr-equalp (caar brr-stack) gstack)))
      (f-put-global 'brr-stack
                    (cons (cons gstack (get-brr-global 'brr-alist state))
                          brr-stack)
                    state))
     (t
      (prog2$
       (cw "~%~%Cryptic BRR Message 2:  Discarding dead brr-stack.  ~@0~%~%"
           *cryptic-brr-message*)
       (f-put-global 'brr-stack
                    (cons (cons gstack (get-brr-global 'brr-alist state))
                          nil)
                    state))))))

(defun pop-brr-stack-frame (state)

; This function may be used inside code executed within "break-rewrite".  It
; pops the top-most frame off the brr-stack.  Actually, it pops all the frames
; up through the one labeled with the current brr-gstack.

  (f-put-global 'brr-stack
                (cdr (clean-brr-stack (get-brr-global 'brr-gstack state)
                                      (get-brr-global 'brr-stack state)))
                state))

(defun decode-type-alist (type-alist)

; Once upon a type we untranslated (caar type-alist) below.  But
; tilde-*-substitution-phrase, which is the only function which sees the output
; of this function in our sources, does an untranslate.

  (cond ((null type-alist) nil)
        (t (cons (cons (caar type-alist)
                       (decode-type-set (cadar type-alist)))
                 (decode-type-alist (cdr type-alist))))))

(defun translate-break-condition (xterm ctx state)
  (er-let* ((term (translate xterm '(nil) nil t ctx (w state) state)))

; known-stobjs = t (user interface)

           (let* ((used-vars (all-vars term))
                  (bad-vars (set-difference-eq used-vars '(state))))
             (cond
              (bad-vars
               (er soft ctx
                   "The only variable allowed in a break condition ~
                    is STATE.  Your form, ~x0, contains the ~
                    variable~#1~[~/s~] ~&2."
                   xterm (if (cdr bad-vars) 1 0) (reverse bad-vars)))
              (t (value term))))))

(defun eval-break-condition (rune term ctx state)
  (cond
   ((equal term *t*) (value t))
   (t (mv-let (erp okp latches)
              (ev term
                  (list (cons 'state (coerce-state-to-object state)))
                  state nil nil t)
              (declare (ignore latches))
              (cond
               (erp (pprogn
                     (error-fms nil ctx (car okp) (cdr okp) state)
                     (er soft ctx
                         "The break condition installed on ~x0 could not be ~
                          evaluated."
                         rune)))
               (t (value okp)))))))

(defconst *default-free-vars-display-limit* 30)

(defmacro set-free-vars-display-limit (n)
  `(let ((n ,n))
     (prog2$ (or (natp n)
                 (er hard 'set-free-vars-display-limit
                     "The argument to set-free-vars-display-limit should ~
                     evaluate to a natural number, but it was given an ~
                     argument that evaluated to ~x0."
                     n))
             (f-put-global 'free-vars-display-limit n state))))

(defun free-vars-display-limit (state)
  (if (f-boundp-global 'free-vars-display-limit state)
      (let ((val (f-get-global 'free-vars-display-limit state)))
        (if (or (natp val) (null val))
            val
          *default-free-vars-display-limit*))
    *default-free-vars-display-limit*))

(mutual-recursion

(defun limit-failure-reason (failures-remaining failure-reason elided-p)
  (declare (xargs :guard (natp failures-remaining)))
  (case-match failure-reason
    ((hyp 'free-vars . alist)
     (cond ((zp failures-remaining)
            (mv 0 (list hyp 'free-vars 'elided) t))
           ((eq (car alist) 'hyp-vars)
            (mv (1- failures-remaining) failure-reason elided-p))
           (t (mv-let (new-failures-remaining new-alist elided-p)
                (limit-failure-reason-alist (1- failures-remaining) alist elided-p)
                (cond ((eql failures-remaining
                            new-failures-remaining) ;optimization
                       (mv failures-remaining failure-reason elided-p))
                      (t (mv new-failures-remaining
                             (list* hyp 'free-vars new-alist)
                             elided-p)))))))
    (& (mv (if (zp failures-remaining)
               failures-remaining
             (1- failures-remaining))
           failure-reason
           elided-p))))

(defun limit-failure-reason-alist (failures-remaining alist elided-p)
  (cond ((null alist)
         (mv failures-remaining alist elided-p))
        (t (mv-let (failures-remaining-1 failure-reason elided-p)
             (limit-failure-reason failures-remaining (cdar alist) elided-p)
             (mv-let (failures-remaining-2 rest-alist elided-p)
               (limit-failure-reason-alist failures-remaining-1 (cdr alist)
                                           elided-p)
               (mv failures-remaining-2
                   (cond ((and (not (zp failures-remaining))
                               (eql failures-remaining
                                    failures-remaining-2))
                          alist) ;optimization
                         (t (cons (cond
                                   ((and (not (zp failures-remaining))
                                         (eql failures-remaining
                                              failures-remaining-1))
                                    (car alist)) ;optimization
                                   (t (cons (caar alist) failure-reason)))
                                  rest-alist)))
                   elided-p))))))
)

(mutual-recursion

(defun fix-free-failure-reason (failure-reason)

; See tilde-@-failure-reason-phrase.

  (case-match failure-reason
    ((& 'free-vars 'hyp-vars . &)
     failure-reason)
    ((bkptr 'free-vars . failure-reason-lst)
     (list* bkptr
            'free-vars
            (fix-free-failure-reason-alist failure-reason-lst nil)))
    (& failure-reason)))

(defun fix-free-failure-reason-alist (x acc)

; We deliberately reverse x as we fix it; see tilde-@-failure-reason-phrase.

  (cond ((endp x) acc)
        (t ; x is (cons (cons unify-subst failure-reason) &)
         (fix-free-failure-reason-alist
          (cdr x)
          (cons (cons (caar x)
                      (fix-free-failure-reason (cdar x)))
                acc)))))
)

(defun ancestor-backchain-rune (ancestor)
  (and (access ancestor ancestor :bkptr)
       (let ((tokens (access ancestor ancestor :tokens)))
         (assert$ (and tokens (null (cdr tokens)))
                  (car tokens)))))

; The function backchain-limit-enforcers calls find-rules-of-rune.  Several
; record structures support the definition of find-rules-of-rune, because they
; support access-x-rule-rune.  We define those structures here, even though
; they might naturally be defined elsewhere (and remain as comments in their
; locations as of Version_8.0).

(defrec forward-chaining-rule
  ((rune . nume) trigger hyps concls . match-free) nil)

(defrec elim-rule
  (((nume . crucial-position) . (destructor-term . destructor-terms))
   (hyps . equiv)
   (lhs . rhs)
   . rune) nil)

(defrec generalize-rule (nume formula . rune) nil)

(defrec induction-rule (nume (pattern . condition) scheme . rune) nil)

(defrec built-in-clause ((nume . all-fnnames) clause . rune) t)

; Decoding Logical Names: decode-logical-name supports the definition of
; find-rules-of-rune, which in turn supports the definition of
; backchain-limit-enforcers; so we turn here to defining decode-logical-name.

(defun scan-to-defpkg (name wrld)

; We wish to give meaning to stringp logical names such as "MY-PKG".  We do it
; in an inefficient way: we scan the whole world looking for an event tuple of
; type DEFPKG and namex name.  We know that name is a known package and that it
; is not one in *initial-known-package-alist*.

  (cond ((null wrld) nil)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value)
              (eq (access-event-tuple-type (cddar wrld)) 'DEFPKG)
              (equal name (access-event-tuple-namex (cddar wrld))))
         wrld)
        (t (scan-to-defpkg name (cdr wrld)))))

(defun scan-to-include-book (full-book-name wrld)

; We wish to give meaning to stringp logical names such as "arith".  We
; do it in an inefficient way: we scan the whole world looking for an event
; tuple of type INCLUDE-BOOK and namex full-book-name.

  (cond ((null wrld) nil)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value)
              (eq (access-event-tuple-type (cddar wrld)) 'include-book)
              (equal full-book-name (access-event-tuple-namex (cddar wrld))))
         wrld)
        (t (scan-to-include-book full-book-name (cdr wrld)))))

(defun multiple-assoc-terminal-substringp1 (x i alist)
  (cond ((null alist) nil)
        ((terminal-substringp x (caar alist) i (1- (length (caar alist))))
         (cons (car alist) (multiple-assoc-terminal-substringp1 x i (cdr alist))))
        (t (multiple-assoc-terminal-substringp1 x i (cdr alist)))))

(defun multiple-assoc-terminal-substringp (x alist)

; X and the keys of the alist are presumed to be strings.  This function
; compares x to the successive keys in the alist, succeeding on any key that
; contains x as a terminal substring.  Unlike assoc, we return the list of all
; pairs in the alist with matching keys.

  (multiple-assoc-terminal-substringp1 x (1- (length x)) alist))

(defun possibly-add-lisp-extension (str)

; String is a string.  If str ends in .lisp, return it.  Otherwise, tack .lisp
; onto the end and return that.

  (let ((len (length str)))
    (cond
     ((and (> len 5)
           (eql (char str (- len 5)) #\.)
           (eql (char str (- len 4)) #\l)
           (eql (char str (- len 3)) #\i)
           (eql (char str (- len 2)) #\s)
           (eql (char str (- len 1)) #\p))
      str)
     (t (string-append str ".lisp")))))

(defun stuff-standard-oi (cmds state)

; This function appends cmds (which must be a true list) onto standard-oi.  We
; act as though the entire system maintains the invariant that when standard-oi
; is a symbol ld-pre-eval-print is nil and when it is a list ld-pre-eval-print
; is t.  We maintain it here.  This has the convenient effect that -- if the
; condition is true now -- then the commands in cmds will be printed before
; they are executed and that when we get back down to *standard-oi* printing
; will be shut off.  There is no guarantee that this condition is invariant.
; The user might set ld-pre-eval-print at will.  The worse that will happen is
; undesirable pre-eval print behavior.

  (declare (xargs :guard (true-listp cmds)))
  (cond
   ((null cmds) state)
   (t (pprogn
       (f-put-global 'ld-pre-eval-print t state)
       (f-put-global 'standard-oi
                     (append cmds
                             (cond ((symbolp (f-get-global 'standard-oi state))
                                    (cons '(set-ld-pre-eval-print nil state)
                                          (f-get-global 'standard-oi state)))
                                   (t (f-get-global 'standard-oi state))))
                     state)))))

(defun defun-mode-prompt-string (state)
  (if (raw-mode-p state)
      "P"
    (case (default-defun-mode (w state))
      (:logic
       (if (gc-off state)
           (if (ld-skip-proofsp state)
               "s"
             "")
         (if (ld-skip-proofsp state)
             "!s"
           "!")))
      (otherwise ; :program
       (if (gc-off state)
           (if (ld-skip-proofsp state)
               "ps"
             "p")
         (if (ld-skip-proofsp state)
             "p!s"
           "p!"))))))

(defun brr-prompt (channel state)
  (the2s
   (signed-byte 30)
   (fmt1 "~F0 ~s1~sr ~@2>"
         (list (cons #\0 (get-brr-local 'depth state))
               (cons #\1 (f-get-global 'current-package state))
               (cons #\2 (defun-mode-prompt-string state))
               (cons #\r
                     #+:non-standard-analysis
                     (if (f-get-global 'script-mode state)
                         ""
                       "(r)")
                     #-:non-standard-analysis ""))
         0 channel state nil)))

; We now develop code to display type-alists nicely.

(defun ts< (x y)

; This is just a heuristic order for the type-alist command (proof-builder and
; break-rewrite).  First comes t, then non-nil, then nil, and finally we sort
; by type inclusion.

  (cond
   ((ts= x y)
    nil)
   ((ts= x *ts-t*)
    t)
   ((ts= y *ts-t*)
    nil)
   ((ts= x *ts-non-nil*)
    t)
   ((ts= y *ts-non-nil*)
    nil)
   ((ts= x *ts-nil*)
    t)
   ((ts= y *ts-nil*)
    nil)
   ((ts-subsetp x y)
    t)
   (t
    nil)))

(defun add-to-type-alist-segments (ts term segs)
  (cond
   ((or (endp segs)
        (ts< ts (caar segs)))
    (cons (cons ts (list term))
          segs))
   ((ts= ts (caar segs))
    (cons (cons ts (cons term (cdar segs)))
          (cdr segs)))
   (t
    (cons (car segs)
          (add-to-type-alist-segments ts term (cdr segs))))))

(defun merge-term-order (l1 l2)
  (declare (xargs :guard (and (pseudo-term-listp l1)
                              (pseudo-term-listp l2))))
  (cond ((endp l1) l2)
        ((endp l2) l1)
        ((term-order (car l1) (car l2))
         (cons (car l1) (merge-term-order (cdr l1) l2)))
        (t (cons (car l2) (merge-term-order l1 (cdr l2))))))

(defun merge-sort-term-order (l)
  (declare (xargs :guard (pseudo-term-listp l)))
  (cond ((endp (cdr l)) l)
        (t (merge-term-order (merge-sort-term-order (evens l))
                             (merge-sort-term-order (odds l))))))

(defun sort-type-alist-segments (segs)
  (if (endp segs)
      nil
    (cons (cons (caar segs)

; Unfortunately, term-order does not do a particularly great job from the point
; of view of displaying terms.  However, we use it anyhow here, if for no other
; reason so that the display order is predictable.

                (merge-sort-term-order (cdar segs)))
          (sort-type-alist-segments (cdr segs)))))

(defun type-alist-segments (type-alist acc)
  (if (endp type-alist)
      (sort-type-alist-segments acc)
    (type-alist-segments (cdr type-alist)
                         (add-to-type-alist-segments
                          (cadar type-alist)
                          (caar type-alist)
                          acc))))

(defun print-terms (terms iff-flg wrld evisc-tuple)

; Print untranslations of the given terms with respect to iff-flg, following
; each with a newline.

; We use cw instead of the fmt functions because we want to be able to use this
; function in print-type-alist-segments (used in brkpt1), which does not return
; state.

  (if (endp terms)
      terms
    (prog2$
     (cw "~Y01"
         (untranslate (car terms) iff-flg wrld)
         evisc-tuple)
     (print-terms (cdr terms) iff-flg wrld evisc-tuple))))

(defun print-type-alist-segments (segs wrld evisc-tuple)

; We use cw instead of the fmt functions because we want to be able to use this
; function in brkpt1, which does not return state.

  (if (endp segs)
      segs
    (prog2$ (cw "-----~%Terms with type ~x0:~%"
                (decode-type-set (caar segs)))
            (prog2$ (print-terms (cdar segs)
                                 (member (caar segs)
                                         (list *ts-t*
                                               *ts-non-nil*
                                               *ts-nil*
                                               *ts-boolean*))
                                 wrld
                                 evisc-tuple)
                    (print-type-alist-segments (cdr segs) wrld evisc-tuple)))))

(defun print-type-alist (type-alist wrld evisc-tuple)
  (print-type-alist-segments (type-alist-segments type-alist nil)
                             wrld
                             evisc-tuple))

; End of code for printing type-alists.

; Start support for find-rules-of-rune, in support of
; backchain-limit-enforcers.

(defun decode-logical-name (name wrld)

; Given a logical name, i.e., a symbol with an 'absolute-event-number property
; or a string naming a defpkg or include-book, we return the tail of wrld
; starting with the introductory event.  We return nil if name is illegal.

  (cond
   ((symbolp name)
    (cond ((eq name :here)
           (scan-to-event wrld))
          (t
           (let ((n (getpropc name 'absolute-event-number nil wrld)))
             (cond ((null n) nil)
                   (t (lookup-world-index 'event n wrld)))))))
   ((stringp name)

; Name may be a package name or a book name.

    (cond
     ((find-non-hidden-package-entry name
                                     (global-val 'known-package-alist wrld))
      (cond ((find-package-entry name *initial-known-package-alist*)

; These names are not DEFPKGd and so won't be found in a scan.  They
; are introduced by absolute event number 0.

             (lookup-world-index 'event 0 wrld))
            (t (scan-to-defpkg name wrld))))
     (t (let ((hits (multiple-assoc-terminal-substringp
                     (possibly-add-lisp-extension name)
                     (global-val 'include-book-alist wrld))))

; Hits is a subset of the include-book-alist.  The form of each
; element is (full-book-name user-book-name familiar-name
; cert-annotations . book-hash).

          (cond
           ((and hits (null (cdr hits)))
            (scan-to-include-book (car (car hits)) wrld))
           (t nil))))))
   (t nil)))

(defun access-x-rule-rune (x rule)

; Given a rule object, rule, of record type x, we return the :rune of rule.
; This is thus typically ``(access x rule :rune).''

; Note: We include with every case the rule-class tokens that create this rule
; so that we can search for any such tokens and find this function when adding
; a new, similar, rule-class.

; There is no record object generated only by        ;;; :refinement
;                                                    ;;; :tau-system
  (case x
        (recognizer-tuple                            ;;; :compound-recognizer
         (access recognizer-tuple rule :rune))
        (type-prescription                           ;;; :type-prescription
         (access type-prescription rule :rune))
        (congruence-rule                             ;;; :congruence
                                                     ;;; :equivalence
         (access congruence-rule rule :rune))
        (pequiv                                      ;;; :congruence
         (access congruence-rule
                 (access pequiv rule :congruence-rule)
                 :rune))
        (rewrite-rule                                ;;; :rewrite
                                                     ;;; :meta
                                                     ;;; :definition
         (access rewrite-rule rule :rune))
        (well-founded-relation-rule                  ;;; :well-founded-relation
; No such record type, but we pretend!
         (cddr rule))
        (linear-lemma                                ;;; :linear
         (access linear-lemma rule :rune))
        (forward-chaining-rule                       ;;; :forward-chaining
         (access forward-chaining-rule rule :rune))
        (built-in-clause                             ;;; :built-in-clause
         (access built-in-clause rule :rune))
        (elim-rule                                   ;;; :elim
         (access elim-rule rule :rune))
        (generalize-rule                             ;;; :generalize
         (access generalize-rule rule :rune))
        (induction-rule                              ;;; :induction
         (access induction-rule rule :rune))
        (type-set-inverter-rule                      ;;; :type-set-inverter
         (access type-set-inverter-rule rule :rune))
        (otherwise (er hard 'access-x-rule-rune
                       "Unrecognized rule class, ~x0."
                       x))))

(defun collect-x-rules-of-rune (x rune lst ans)

; Lst is a list of rules of type x.  We collect all those elements of lst
; with :rune rune.

  (cond ((null lst) ans)
        ((equal rune (access-x-rule-rune x (car lst)))
         (collect-x-rules-of-rune x rune (cdr lst)
                                  (add-to-set-equal (car lst) ans)))
        (t (collect-x-rules-of-rune x rune (cdr lst) ans))))

(defun collect-congruence-rules-of-rune-in-geneqv-lst (geneqv-lst rune ans)

; A geneqv is a list of congruence rules.  Geneqv-lst, above, is a list of
; geneqvs.  We scan every congruence rule in geneqv-lst and collect those with
; the :rune rune.

  (cond
   ((null geneqv-lst) ans)
   (t (collect-congruence-rules-of-rune-in-geneqv-lst
       (cdr geneqv-lst) rune
       (collect-x-rules-of-rune 'congruence-rule rune (car geneqv-lst) ans)))))

(defun collect-congruence-rules-of-rune (congruences rune ans)

; The 'congruences property of an n-ary function symbol is a list of tuples,
; each of which is of the form (equiv geneqv1 ... geneqvn), where each geneqvi
; is a list of congruence rules.  Congruences is the 'congruences property of
; some function.  We scan it and collect every congruence rule in it that has
; :rune rune.

  (cond
   ((null congruences) ans)
   (t (collect-congruence-rules-of-rune
       (cdr congruences) rune
       (collect-congruence-rules-of-rune-in-geneqv-lst (cdr (car congruences))
                                                       rune ans)))))

(defun collect-pequivs-of-rune (alist rune ans)

; Alist has the form of the :deep or :shallow field of the 'pequivs property of
; a function symbol.  Thus, each element of alist is of the form (equiv pequiv1
; ... pequivn), where each pequivi is a pequiv record.  We scan this alist and
; collect every pequiv record in it whose :rune is rune.

  (cond
   ((null alist) ans)
   (t (collect-pequivs-of-rune
       (cdr alist)
       rune
       (collect-x-rules-of-rune 'pequiv rune (cdr (car alist)) ans)))))

(defun find-rules-of-rune2 (rune sym key val ans)

; (sym key . val) is a member of wrld.  We collect all the rules in val with
; :rune rune.  This function is patterned after info-for-x-rules.

; Wart: If key is 'eliminate-destructors-rule, then val is a single rule, not a
; list of rules.  We handle this case specially below.

; Warning: Keep this function in sync with info-for-x-rules.  In that spirit,
; note that tau rules never store runes and hence are completely ignored
; here, as in info-for-x-rules.

  (let ((token (car rune)))

; As an efficiency, we do not look for rune in places where it cannot occur.
; For example, if token is :elim then there is no point in searching through
; the 'lemmas properties.  In general, each case below insists that token is of
; the appropriate class.  Sometimes there are more than one.  For example, the
; 'lemmas property may contain :rewrite, :definition, and :meta runes, all of
; which are stored as REWRITE-RULEs.

    (cond
     ((eq key 'global-value)
      (case sym
            (well-founded-relation-alist
             (if (eq token :well-founded-relation)
                 (collect-x-rules-of-rune 'well-founded-relation-rule rune
                                          val ans)
                 ans))
            (built-in-clauses
             (if (eq token :built-in-clause)
                 (collect-x-rules-of-rune 'built-in-clause rune val ans)
                 ans))
            (type-set-inverter-rules
             (if (eq token :type-set-inverter)
                 (collect-x-rules-of-rune 'type-set-inverter-rule rune
                                          val ans)
                 ans))
            (generalize-rules
             (if (eq token :generalize)
                 (collect-x-rules-of-rune 'generalize-rule rune val ans)
                 ans))
            (otherwise ans)))
     (t
      (case key
            (lemmas
             (if (member-eq token '(:rewrite :meta :definition))
                 (collect-x-rules-of-rune 'rewrite-rule rune val ans)
                 ans))
            (linear-lemmas
             (if (eq token :linear)
                 (collect-x-rules-of-rune 'linear-lemma rune val ans)
                 ans))
            (eliminate-destructors-rule
             (if (eq token :elim)
                 (collect-x-rules-of-rune 'elim-rule rune (list val) ans)
                 ans))
            (congruences
             (if (member-eq token '(:congruence :equivalence))
                 (collect-congruence-rules-of-rune val rune ans)
                 ans))
            (pequivs
             (if (eq token :congruence)
                 (collect-pequivs-of-rune
                  (access pequivs-property val :deep)
                  rune
                  (collect-pequivs-of-rune
                   (access pequivs-property val :shallow)
                   rune
                   ans))
               ans))
            (coarsenings

; :Refinement rules add to the 'coarsenings property.  If equiv1 is a
; refinement of equiv2, then equiv2 is a coarsening of equiv1 and the lemma
; establishing that fact adds equiv2 to the 'coarsenings property of equiv1.
; There is no rule object corresponding to this fact.  Hence, even if rune is
; the :refinement rune responsible for adding some equiv2 to this list, we
; won't find a rule object here by the name rune.

; Similar comments apply to :equivalence rules.  They add to the 'coarsenings
; property but no rule object exists.  It should be noted that some congruence
; rules are added by lemmas of class :equivalence and those rules are named by
; :equivalence runes and are found among the 'congruences properties.

             ans)
            (forward-chaining-rules
             (if (eq token :forward-chaining)
                 (collect-x-rules-of-rune 'forward-chaining-rule rune val ans)
                 ans))
            (type-prescriptions
             (if (eq token :type-prescription)
                 (collect-x-rules-of-rune 'type-prescription rune val ans)
                 ans))
            (induction-rules
             (if (eq token :induction)
                 (collect-x-rules-of-rune 'induction-rule rune val ans)
                 ans))
            (recognizer-alist
             (if (eq token :compound-recognizer)
                 (collect-x-rules-of-rune 'recognizer-tuple rune val ans)
               ans))
            (otherwise ans))))))

(defun find-rules-of-rune1 (rune props ans)

; Props is a list of triples and can be considered a segment of some wrld.  (It
; is not only because duplicates have been removed.)  We visit every property
; and collect all the rules with :rune rune.

  (cond ((null props) ans)
        ((eq (cddar props) *acl2-property-unbound*)
         (find-rules-of-rune1 rune (cdr props) ans))
        (t (find-rules-of-rune1 rune (cdr props)
                                (find-rules-of-rune2 rune
                                                     (caar props)
                                                     (cadar props)
                                                     (cddar props)
                                                     ans)))))

(defun world-to-next-event (wrld)
  (cond ((null wrld) nil)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value))
         nil)
        (t (cons (car wrld)
                 (world-to-next-event (cdr wrld))))))

(defun actual-props (props seen acc)

; Props is a list whose elements have the form (sym key . val), where val could
; be *acl2-property-unbound*.  Seen is the list containing some (sym key . &)
; for each pair (sym key) that has already been seen.

  (cond
   ((null props)
    (prog2$ (fast-alist-free seen)
            (reverse acc)))
   ((member-eq (cadar props) (cdr (hons-get (caar props) seen)))
    (actual-props (cdr props) seen acc))
   ((eq (cddr (car props)) *acl2-property-unbound*)
    (actual-props (cdr props)
                  (hons-acons (caar props)
                              (cons (cadar props)
                                    (cdr (hons-get (caar props) seen)))
                              seen)
                  acc))
   (t
    (actual-props (cdr props)
                  (hons-acons (caar props)
                              (cons (cadar props)
                                    (cdr (hons-get (caar props) seen)))
                              seen)
                  (cons (car props) acc)))))

(defun find-rules-of-rune (rune wrld)

; Find all the rules in wrld with :rune rune.  We do this by first obtaining
; that segment of wrld consisting of the properties stored by the event
; named by the base symbol of rune.  Then we collect every rule mentioned
; in the segment, provided the rule has :rune rune.

  (declare (xargs :guard (and (plist-worldp wrld)
                              (runep rune wrld))))
  (let ((wrld-tail (decode-logical-name (base-symbol rune) wrld)))
    (find-rules-of-rune1 rune
                         (actual-props
                          (world-to-next-event (cdr wrld-tail))
                          'find-rules-of-rune1
                          nil)
                         nil)))

(defun backchain-limit-enforcers (position ancestors wrld)

; Backchaining has failed due to a backchain-limit, for a rule of class
; :rewrite or :linear.  Find indices of all ancestors whose backchain-limit
; could be the culprit, as reported by the :ANCESTORS break-rewrite command.
; Position is the position in the top-level ancestors, which is 0 at the top
; level; it is a bound on how many times we are allowed to backchain in order
; to avoid the current failure.

  (cond ((endp ancestors) nil)
        (t (let* ((rune (ancestor-backchain-rune (car ancestors)))
                  (rule (and rune
                             (car (find-rules-of-rune rune wrld)))))
             (cond (rule
                    (let* ((linearp (eq (car rune) :linear))
                           (backchain-limit-lst
                            (if linearp
                                (access linear-lemma rule :backchain-limit-lst)
                              (access rewrite-rule rule :backchain-limit-lst)))
                           (bkptr (access ancestor (car ancestors) :bkptr))
                           (hyp-backchain-limit
                            (and backchain-limit-lst
                                 (if (and (not linearp)
                                          (eq (access rewrite-rule rule
                                                      :subclass)
                                              'meta))
                                     backchain-limit-lst ; a numeric limit
                                   (nth (1- bkptr)
                                        backchain-limit-lst)))))
                      (cond ((and hyp-backchain-limit
                                  (>= (1+ position) hyp-backchain-limit))
                             (cons (cons position hyp-backchain-limit)
                                   (backchain-limit-enforcers (1+ position)
                                                              (cdr ancestors)
                                                              wrld)))
                            (t
                             (backchain-limit-enforcers (1+ position)
                                                        (cdr ancestors)
                                                        wrld))))))))))

(defun tilde-*-ancestors-stack-msg1 (i ancestors wrld evisc-tuple)
  (cond ((endp ancestors) nil)
        ((ancestor-binding-hyp-p (car ancestors))
         (cons (msg "~c0. Binding Hyp: ~Q12~|~
                     ~ ~ ~ ~ ~ Unify-subst:  ~Q32~%"
                    (cons i 2)
                    (untranslate (dumb-negate-lit
                                  (ancestor-binding-hyp/hyp (car ancestors)))
                                 t wrld)
                    evisc-tuple
                    (ancestor-binding-hyp/unify-subst (car ancestors)))
               (tilde-*-ancestors-stack-msg1 (+ 1 i) (cdr ancestors)
                                             wrld evisc-tuple)))
        (t (cons (let ((tokens (access ancestor (car ancestors) :tokens)))
                   (msg "~c0. Hyp: ~Q12~|~
                         ~ ~ ~ ~ ~ Rune~#3~[:  ~x4~/s:  ~x3~]~%"
                        (cons i 2)
                        (untranslate (dumb-negate-lit
                                      (access ancestor (car ancestors) :lit))
                                     t wrld)
                        evisc-tuple
                        tokens
                        (car tokens)))
                 (tilde-*-ancestors-stack-msg1 (+ 1 i) (cdr ancestors)
                                               wrld evisc-tuple)))))

(defun tilde-*-ancestors-stack-msg (ancestors wrld evisc-tuple)
  (list "" "~@*" "~@*" "~@*"
         (tilde-*-ancestors-stack-msg1 0 ancestors wrld evisc-tuple)))

(defun brr-evisc-tuple (state)
  (cond
   ((eq (f-get-global 'wormhole-name state) 'brr)
    (let ((val (get-brr-global 'brr-evisc-tuple state)))
      (if (eq val :DEFAULT)
          (term-evisc-tuple t state)
        val)))
   (t (er hard 'brr-evisc-tuple
          "It is illegal to call ~x0 unless you are under ~
           break-rewrite and you are not.  Consider instead evaluating ~x1."
          'brr-evisc-tuple
          '(show-brr-evisc-tuple)))))

(defun set-brr-evisc-tuple (val state)
  (pprogn
   (f-put-global 'brr-evisc-tuple-initialized t state)
   (cond
    ((eq (f-get-global 'wormhole-name state) 'brr)
     (f-put-global 'brr-evisc-tuple val state))
    (t (prog2$
        (brr-wormhole
         '(lambda (whs)
            (set-wormhole-entry-code whs :ENTER))
         nil
         `(pprogn (f-put-global 'brr-evisc-tuple ',val state)
                  (value nil))
         nil)
        state)))))

(defun maybe-initialize-brr-evisc-tuple (state)
  (cond ((f-get-global 'brr-evisc-tuple-initialized state)
; The test above is always true inside :brr.
         state)
        (t (set-brr-evisc-tuple :DEFAULT state))))

(defun show-brr-evisc-tuple-fn (state)
  (pprogn
   (maybe-initialize-brr-evisc-tuple state)
   (cond
    ((eq (f-get-global 'wormhole-name state) 'brr)
     (prog2$ (cw "~Y01~|" (brr-evisc-tuple state) nil)
             (value :invisible)))
    (t
     (prog2$
      (brr-wormhole
       '(lambda (whs)
          (set-wormhole-entry-code whs :ENTER))
       nil
       `(prog2$ (cw "~Y01~|" (brr-evisc-tuple state) nil)
                (value nil))
       nil)
      (value :invisible))))))

(defmacro show-brr-evisc-tuple ()
  '(show-brr-evisc-tuple-fn state))

(defun show-ancestors-stack-msg (state evisc-tuple)
  (msg "Ancestors stack (most recent entry on top):~%~*0~%Use ~x1 to see ~
        actual ancestors stack.~%"
       (tilde-*-ancestors-stack-msg
        (get-brr-local 'ancestors state)
        (w state)
        evisc-tuple)
       '(get-brr-local 'ancestors state)))

(defun tilde-@-failure-reason-phrase1-backchain-limit (hyp-number
                                                       ancestors
                                                       state
                                                       evisc-tuple)
  (msg
   "a backchain limit was reached while processing :HYP ~x0.  ~@1"
   hyp-number
   (let ((pairs (backchain-limit-enforcers 0 ancestors (w state))))
     (cond
      ((null pairs)
       (let ((str "  Note that the brr command, :ANCESTORS, will show you the ~
                   ancestors stack."))
         (cond ((backchain-limit (w state) :rewrite)
                (msg "This appears to be due to the global backchain-limit of ~
                      ~x0.~@1"
                     (backchain-limit (w state) :rewrite)
                     str))
               (t

; If the global backchain-limit for :rewrite is nil, and no ancestor has a
; relevant backchain-limit (i.e., pairs is nil), then the hypothesis at hand
; must have a backchain-limit of 0.  Through Version_8.3 we did not handle this
; case properly; it seems we assumed that if the hypothesis has a
; backchain-limit of 0 then pairs must be nil, but that is not necessarily the
; case as illustrated by the following example (inspired by a bug report from
; Mihir Mehta).

;   (defun p1 (x) (integerp x))
;   (defun p2 (x) (integerp x))
;   (defun p3 (x) (integerp x))
;   (defthm p1->p2
;     (implies (p1 x) (p2 x))
;     :rule-classes ((:rewrite :backchain-limit-lst (0))))
;   (defthm p2->p3
;     (implies (p2 x) (p3 x)))
;   (in-theory (disable p1 p2 p3))
;   (brr t)
;   (monitor '(:rewrite p1->p2) t)
;   (thm (p3 a))

                (msg "Note that the limit is 0 for that :HYP.")))))
      (t
       (msg "The ancestors stack is below.  The ~#0~[entry~/entries~] at ~
             index ~&0 ~#0~[shows~/each show~] a rune whose ~#0~[~/respective ~
             ~]backchain limit of ~v1 has been reached, for backchaining ~
             through its indicated hypothesis.~|~%~@2"
            (strip-cars pairs)
            (strip-cdrs pairs)
            (show-ancestors-stack-msg state evisc-tuple)))))))

(defun get-evg (q ctx)

; Q is a quotep, or at least we expect it to be.  We cause a hard error if not,
; else we return the "explicit value guts".

  (if (quotep q)
      (cadr q)
    (er hard ctx
        "We expected a quotep in this context, variables, but ~x0 is not a ~
         quotep!"
        q)))

(mutual-recursion

(defun tilde-@-failure-reason-free-phrase (hyp-number alist level unify-subst
                                                      evisc-tuple state)

; Alist is a list of pairs (unify-subst . failure-reason).  Level is initially
; 0 and increases as we dive into failure-reason.

  (cond
   ((null alist) "")
   (t
    (let ((new-unify-subst (caar alist))
          (new-failure-reason (cdar alist)))
      (msg "~t0[~x1]~*2~|~@3~@4~@5"
           (if (< hyp-number 10) (* 4 level) (1- (* 4 level)))
           hyp-number
           (tilde-*-alist-phrase (alist-difference-eq new-unify-subst unify-subst)
                                 evisc-tuple
                                 (+ 4 (* 4 level)))
           (if (let ((fr (if (and (consp new-failure-reason)
                                  (eq (car new-failure-reason) 'cached))
                             (cdr new-failure-reason)
                           new-failure-reason)))
                 (and (consp fr)
                      (integerp (car fr))
                      (or (not (and (consp (cdr fr))
                                    (eq (cadr fr) 'free-vars)))
                          (and (consp (cdr fr))
                               (consp (cddr fr))
                               (member-eq (caddr fr)
                                          '(hyp-vars elided))))))
               "Failed because "
             "")
           (tilde-@-failure-reason-phrase1 new-failure-reason (1+ level)
                                           new-unify-subst evisc-tuple nil
                                           state)
           (tilde-@-failure-reason-free-phrase hyp-number
                                               (cdr alist) level unify-subst
                                               evisc-tuple state))))))

(defun tilde-@-failure-reason-phrase1 (failure-reason level unify-subst
                                                      evisc-tuple
                                                      free-vars-display-limit
                                                      state)
  (cond ((eq failure-reason 'time-out)
         "we ran out of time.")
        ((eq failure-reason 'loop-stopper)
         "it permutes a big term forward.")
        ((eq failure-reason 'too-many-ifs-pre-rewrite)
         "the unrewritten :RHS contains too many IFs for the given args.")
        ((eq failure-reason 'too-many-ifs-post-rewrite)
         "the rewritten :RHS contains too many IFs for the given args.")
        ((eq failure-reason 'rewrite-fncallp)
         "the :REWRITTEN-RHS is judged heuristically unattractive.")
        ((member-eq failure-reason '(linearize-unrewritten-produced-disjunction
                                     linearize-rewritten-produced-disjunction))
         (msg "the ~@0 term generated a disjunction of two conjunctions of ~
               polynomials."
              (if (eq failure-reason 'linearize-rewritten-produced-disjunction)
                  'rewritten
                'unrewritten)))
        ((eq failure-reason 'linear-possible-loop)
         "the rewritten term was judged to have the potential to cause a loop ~
          related to linear arithmetic.")
        ((and (consp failure-reason)
              (integerp (car failure-reason)))
         (let ((n (car failure-reason)))
           (case
             (cdr failure-reason)
             (time-out (msg "we ran out of time while processing :HYP ~x0."
                            n))
             (ancestors (msg ":HYP ~x0 is judged more complicated than its ~
                              ancestors (type :ANCESTORS to see the ancestors ~
                              and :PATH to see how we got to this point)."
                             n))
             (known-nil (msg ":HYP ~x0 is known nil by type-set."
                             n))
             (otherwise
              (cond
               ((eq (cadr failure-reason) 'free-vars)
                (mv-let
                 (failures-remaining failure-reason elided-p)
                 (if free-vars-display-limit
                     (limit-failure-reason free-vars-display-limit
                                           failure-reason
                                           nil)
                   (mv nil failure-reason nil))
                 (declare (ignore failures-remaining))
                 (cond
                  ((eq (caddr failure-reason) 'hyp-vars)
                   (msg ":HYP ~x0 contains free variable~#1~[~/s~] ~&1, for ~
                         which no suitable ~#1~[binding was~/bindings were~] ~
                         found."
                        n
                        (set-difference-equal (cdddr failure-reason)
                                              (strip-cars unify-subst))))
                  ((eq (caddr failure-reason) 'elided)
                   (msg ":HYP ~x0 contains free variables (further reasons ~
                         elided, as noted above)."
                        n))
                  (t
                   (msg
                    "~@0~@1"
                    (if (eql level 1)
                        (msg ":HYP ~x0 ~@1.  The following display summarizes ~
                              the attempts to relieve hypotheses by binding ~
                              free variables; see :DOC free-variables.~|~@2~%"
                             n
                             (if (let* ((hyp
                                         (nth (1- n)
                                              (access rewrite-rule
                                                      (get-brr-local 'lemma state)
                                                      :hyps)))
                                        (evg
                                         (and (ffn-symb-p hyp 'synp)
                                              (quotep (fargn hyp 2))
                                              (unquote (fargn hyp 2)))))
                                   (and evg
                                        (consp evg)
                                        (eq (car evg) 'bind-free)))
                                 (msg "uses ~x0 to produce unsuccessful free ~
                                       variable bindings"
                                      'bind-free)
                               "contains free variables")
                             (if elided-p
                                 (msg
                                  "     Also, if you want to avoid ~
                                     ``reasons elided'' notes below, then ~
                                     evaluate (assign free-vars-display-limit ~
                                     k) for larger k (currently ~x0, default ~
                                     ~x1); then :failure-reason will show the ~
                                     first k or so failure sub-reasons before ~
                                     eliding.  Note that you may want to do ~
                                     this evaluation outside break-rewrite, ~
                                     so that it persists.~|"
                                  free-vars-display-limit
                                  *default-free-vars-display-limit*)
                               ""))
                      "")
                    (tilde-@-failure-reason-free-phrase
                     n
                     (cddr failure-reason)
                     level unify-subst evisc-tuple state))))))
               ((eq (cadr failure-reason) 'backchain-limit)
                (tilde-@-failure-reason-phrase1-backchain-limit
                 n
                 (cddr failure-reason)
                 state
                 evisc-tuple))
               ((eq (cadr failure-reason) 'rewrote-to)
                (msg ":HYP ~x0 rewrote to ~X12."
                     n
                     (cddr failure-reason)
                     evisc-tuple))
               ((member-eq (cadr failure-reason) '(syntaxp
                                                   syntaxp-extended
                                                   bind-free
                                                   bind-free-extended))
                (let ((synp-fn (case (cadr failure-reason)
                                 (syntaxp-extended 'syntaxp)
                                 (bind-free-extended 'bind-free)
                                 (otherwise (cadr failure-reason)))))
                  (cond ((caddr failure-reason)
                         (msg "the evaluation of the ~x0 test in :HYP ~x1 ~
                               produced the error ``~@2''"
                              synp-fn
                              n
                              (cadddr failure-reason)))
                        (t (msg "the ~x0 test in :HYP ~x1 evaluated to NIL."
                                synp-fn
                                n)))))
               (t (er hard 'tilde-@-failure-reason-phrase1
                      "Unrecognized failure reason, ~x0."
                      failure-reason)))))))
        ((and (consp failure-reason)
              (eq (car failure-reason) 'normalizer-failed-to-evaluate))
         (msg "the normalizer, ~x0, simplified to a non-constant, ~x1."
              (cadr failure-reason)
              (caddr failure-reason)))
        ((and (consp failure-reason)
              (eq (car failure-reason) 'normalizer-returned-same-constant))
         (msg "the normalizer, ~x0, simplified to the same constant, ~x1."
              (cadr failure-reason)
              (caddr failure-reason)))
        ((and (consp failure-reason)
              (eq (car failure-reason) 'cached))
         (msg "~@0~|*NOTE*: This failure was cached earlier.  Use the hint ~
               :RW-CACHE-STATE ~x1 to disable failure caching."
              (tilde-@-failure-reason-phrase1
               (cdr failure-reason)
               level unify-subst evisc-tuple free-vars-display-limit state)
              nil))
        (t (er hard 'tilde-@-failure-reason-phrase1
               "Unrecognized failure reason, ~x0."
               failure-reason))))
)

(defun tilde-@-failure-reason-phrase (failure-reason level unify-subst
                                                     evisc-tuple
                                                     free-vars-display-limit
                                                     state)

; In relieve-hyps1 we store a 'free-vars failure reason in which we formerly
; reversed a "failure-reason-lst", which is really an alist mapping extended
; unify-substs to failure reasons.  Now, we save consing by delaying such
; reversal until the relatively rare times that we are ready to display the
; failure reason.

  (tilde-@-failure-reason-phrase1 (fix-free-failure-reason failure-reason)
                                  level unify-subst evisc-tuple
                                  free-vars-display-limit state))

(defun brr-result (state)
  (let ((result (get-brr-local 'brr-result state)))
    (cond ((eq (record-type (get-brr-local 'lemma state)) 'linear-lemma)
           (show-poly-lst result))
          (t result))))

(defconst *brkpt1-aliases*

; Keep this in sync (as appropriate) with *brkpt2-aliases*.

  (flet ((not-yet-evaled-fn ()
                            `(lambda nil
                               (prog2$
                                (cw "~F0 has not yet been :EVALed.~%"
                                    (get-rule-field (get-brr-local 'lemma state)
                                                    :rune))
                                (value :invisible))))
         (ancestors-fn (plusp)
                       `(lambda nil
                          (prog2$
                           (cw "~@0" (show-ancestors-stack-msg
                                      state
                                      ,(if plusp
                                           nil
                                         '(brr-evisc-tuple state))))
                           (value :invisible))))
         (btm-fn (plusp)
                 `(lambda nil
                    (prog2$
                     (let ((gstack (get-brr-global 'brr-gstack state)))
                       (cw-gframe (length gstack) nil (car gstack)
                                  ,(if plusp
                                       nil
                                     '(brr-evisc-tuple state))))
                     (value :invisible))))
         (frame-fn (plusp)
                   `(lambda (n)
                      (let ((rgstack
                             (reverse (get-brr-global 'brr-gstack state))))
                        (cond
                         ((and (integerp n)
                               (>= n 1)
                               (<= n (length rgstack)))
                          (prog2$
                           (cw-gframe n
                                      (if (= n 1)
                                          nil
                                        (access gframe (nth (- n 2) rgstack)
                                                :sys-fn))
                                      (nth (- n 1) rgstack)
                                      ,(if plusp
                                           nil
                                         '(brr-evisc-tuple state)))
                           (value :invisible)))
                         (t (er soft :frame
                                ":FRAME must be given an integer argument ~
                                 between 1 and ~x0."
                                (length rgstack)))))))
         (initial-ttree-fn (plusp)
                           `(lambda nil
                              (let ((lemma (get-brr-local 'lemma state)))
                                (cond
                                 ((eq (record-type lemma) 'linear-lemma)
                                  (er soft :INITIAL-TTREE
                                      ":INITIAL-TTREE is not legal for a ~
                                       :LINEAR rule."))
                                 (t (prog2$
                                     (cw "~X01~|"
                                         (get-brr-local 'initial-ttree state)
                                         ,(if plusp
                                              nil
                                            '(brr-evisc-tuple state)))
                                     (value :invisible)))))))
         (path-fn (plusp)
                  `(lambda nil
                     (prog2$ (cw-gstack :evisc-tuple
                                        ,(if plusp
                                             nil
                                           '(brr-evisc-tuple state)))
                             (value :invisible))))
         (target-fn (plusp)
                    `(lambda nil
                       (prog2$ (cw "~X01~|"
                                   (get-brr-local 'target state)
                                   ,(if plusp
                                        nil
                                      '(brr-evisc-tuple state)))
                               (value :invisible))))
         (top-fn (plusp)
                 `(lambda nil
                    (prog2$
                     (cw-gframe 1
                                nil
                                (car (reverse (get-brr-global 'brr-gstack
                                                              state)))
                                ,(if plusp
                                     nil
                                   '(brr-evisc-tuple state)))
                     (value :invisible))))
         (type-alist-fn (plusp)
                        `(lambda nil
                           (prog2$
                            (cw "~%Decoded type-alist:~%")
                            (prog2$
                             (print-type-alist-segments
                              (type-alist-segments
                               (get-brr-local 'type-alist state)
                               nil)
                              (w state)
                              ,(if plusp
                                   nil
                                 '(brr-evisc-tuple state)))
                             (prog2$
                              (cw "~%==========~%Use ~x0 to see actual ~
                                   type-alist.~%"
                                  '(get-brr-local 'type-alist state))
                              (value :invisible))))))
         (unify-subst-fn (plusp)
                         `(lambda nil
                            (prog2$
                             (cw "~*0"
                                 (tilde-*-alist-phrase
                                  (get-brr-local 'unify-subst state)
                                  ,(if plusp
                                       nil
                                     '(brr-evisc-tuple state))
                                  5))
                             (value :invisible)))))
    `(
; If you add commands, change the documentation for brr-commands.
      (:ancestors
       0 ,(ancestors-fn nil))
      (:ancestors+
       0 ,(ancestors-fn t))
      (:btm
       0 ,(btm-fn nil))
      (:btm+
       0 ,(btm-fn t))
      (:eval
       0 (lambda nil
           (proceed-from-brkpt1 'break t :eval state)))
      (:eval!
       0 (lambda nil
           (proceed-from-brkpt1 'break nil :eval! state)))
      (:eval$
       1 (lambda (runes)
           (proceed-from-brkpt1 'break runes :eval$ state)))
      (:failure-reason
       0 ,(not-yet-evaled-fn))
      (:failure-reason+
       0 ,(not-yet-evaled-fn))
      (:final-ttree
       0 ,(not-yet-evaled-fn))
      (:final-ttree+
       0 ,(not-yet-evaled-fn))
      (:frame
       1 ,(frame-fn nil))
      (:frame+
       1 ,(frame-fn t))
      (:go
       0 (lambda nil
           (proceed-from-brkpt1 'print t :go state)))
      (:go!
       0 (lambda nil
           (proceed-from-brkpt1 'print nil :go! state)))
      (:go$
       1 (lambda (runes)
           (proceed-from-brkpt1 'print runes :go$ state)))
      (:help
       0 (lambda nil
           (doc 'brr-commands)))
      (:hyp
       1 (lambda (n)
           (cond
            ((and (integerp n)
                  (>= n 1)
                  (<= n (length (get-rule-field (get-brr-local 'lemma state)
                                                :hyps))))
             (prog2$ (cw "~X01~|"
                         (nth (1- n)
                              (get-rule-field (get-brr-local 'lemma state)
                                              :hyps))
                         nil)
                     (value :invisible)))
            (t (er soft :HYP
                   ":HYP must be given an integer argument between 1 and ~x0."
                   (length (get-rule-field (get-brr-local 'lemma state)
                                           :hyps)))))))
      (:hyps
       0 (lambda nil
           (prog2$
            (cw "~x0~|"
                (get-rule-field (get-brr-local 'lemma state)
                                :hyps))
            (value :invisible))))
      (:initial-ttree
       0 ,(initial-ttree-fn nil))
      (:initial-ttree+
       0 ,(initial-ttree-fn t))
      (:lhs
       0 (lambda nil
           (let ((val (get-rule-field (get-brr-local 'lemma state)
                                      :lhs)))
             (cond
              ((eq val :get-rule-field-none) ; linear lemma
               (er soft :LHS
                   ":LHS is only legal for a :REWRITE rule."))
              (t
               (prog2$
                (cw "~x0~|" val)
                (value :invisible)))))))
      (:ok
       0 (lambda nil

; Note:  Proceed-from-brkpt1 is not defined in this file!  It is here used
; in a constant, fortunately, because it cannot yet be defined.  The problem
; is that it involves chk-acceptable-monitors, which in turn must look at
; the rules named by given runes, which is a procedure we can define only
; after introducing certain history management utilities.

           (proceed-from-brkpt1 'silent t :ok state)))
      (:ok!
       0 (lambda nil
           (proceed-from-brkpt1 'silent nil :ok! state)))
      (:ok$
       1 (lambda (runes)
           (proceed-from-brkpt1 'silent runes :ok$ state)))
      (:path
       0 ,(path-fn nil))
      (:path+
       0 ,(path-fn t))
      (:poly-list
       0 ,(not-yet-evaled-fn))
      (:poly-list+
       0 ,(not-yet-evaled-fn))
      (:q
       0 (lambda nil
           (prog2$ (cw "Proceed with some flavor of :ok, :go, or :eval, or use ~
                      :p! to pop or :a! to abort.~%")
                   (value :invisible))))
      (:rewritten-rhs
       0 ,(not-yet-evaled-fn))
      (:rewritten-rhs+
       0 ,(not-yet-evaled-fn))
      (:rhs
       0 (lambda nil
           (let ((val (get-rule-field (get-brr-local 'lemma state)
                                      :rhs)))
             (cond
              ((eq val :get-rule-field-none) ; linear lemma
               (er soft :RHS
                   ":RHS is only legal for a :REWRITE rule."))
              (t
               (prog2$
                (cw "~x0~|" val)
                (value :invisible)))))))
      (:standard-help 0 help)
      (:target
       0 ,(target-fn nil))
      (:target+
       0 ,(target-fn t))
      (:top
       0 ,(top-fn nil))
      (:top+
       0 ,(top-fn t))
      (:type-alist
       0 ,(type-alist-fn nil))
      (:type-alist+
       0 ,(type-alist-fn t))
      (:unify-subst
       0 ,(unify-subst-fn nil))
      (:unify-subst+
       0 ,(unify-subst-fn t))
      (:wonp
       0 ,(not-yet-evaled-fn)))))

(defconst *brkpt2-aliases*

; Keep this in sync (as appropriate) with *brkpt1-aliases*.

  (flet ((already-evaled-fn ()
                            '(lambda nil
                               (prog2$ (cw "You already have run some flavor ~
                                            of :eval.~%")
                                       (value :invisible))))
         (ancestors-fn (plusp)
                       `(lambda nil
                          (prog2$
                           (cw "~@0" (show-ancestors-stack-msg
                                      state
                                      ,(if plusp
                                           nil
                                         '(brr-evisc-tuple state))))
                           (value :invisible))))
         (btm-fn (plusp)
                 `(lambda nil
                    (prog2$
                     (let ((gstack (get-brr-global 'brr-gstack state)))
                       (cw-gframe (length gstack) nil (car gstack)
                                  ,(if plusp
                                       nil
                                     '(brr-evisc-tuple state))))
                     (value :invisible))))
         (failure-reason-fn (plusp)
                            `(lambda nil
                               (prog2$
                                (if (get-brr-local 'wonp state)
                                    (cw "? ~F0 succeeded.~%"
                                        (get-rule-field (get-brr-local 'lemma
                                                                       state)
                                                        :rune))
                                  (cw "~@0~|"
                                      (tilde-@-failure-reason-phrase
                                       (get-brr-local 'failure-reason state)
                                       1
                                       (get-brr-local 'unify-subst state)
                                       ,(if plusp
                                            nil
                                          '(brr-evisc-tuple state))
                                       (free-vars-display-limit state)
                                       state)))
                                (value :invisible))))
         (final-ttree-fn (plusp)
                         `(lambda nil
                            (let ((lemma (get-brr-local 'lemma state)))
                              (cond
                               ((eq (record-type lemma) 'linear-lemma)
                                (er soft :FINAL-TTREE
                                    ":FINAL-TTREE is not legal for a :LINEAR ~
                                     rule."))
                               (t (prog2$
                                   (cw "~X01~|"
                                       (get-brr-local 'final-ttree state)
                                       ,(if plusp
                                            nil
                                          '(brr-evisc-tuple state)))
                                   (value :invisible)))))))
         (frame-fn (plusp)
                   `(lambda (n)
                      (let ((rgstack
                             (reverse (get-brr-global 'brr-gstack state))))
                        (cond
                         ((and (integerp n)
                               (>= n 1)
                               (<= n (length rgstack)))
                          (prog2$
                           (cw-gframe n
                                      (if (= n 1)
                                          nil
                                        (access gframe (nth (- n 2) rgstack)
                                                :sys-fn))
                                      (nth (- n 1) rgstack)
                                      ,(if plusp
                                           nil
                                         '(brr-evisc-tuple state)))
                           (value :invisible)))
                         (t (er soft :frame
                                ":FRAME must be given an integer argument ~
                                 between 1 and ~x0."
                                (length rgstack)))))))
         (initial-ttree-fn (plusp)
                           `(lambda nil
                              (let ((lemma (get-brr-local 'lemma state)))
                                (cond
                                 ((eq (record-type lemma) 'linear-lemma)
                                  (er soft :INITIAL-TTREE
                                      ":INITIAL-TTREE is not legal for a ~
                                       :LINEAR rule."))
                                 (t (prog2$
                                     (cw "~X01~|"
                                         (get-brr-local 'initial-ttree state)
                                         ,(if plusp
                                              nil
                                            '(brr-evisc-tuple state)))
                                     (value :invisible)))))))
         (path-fn (plusp)
                  `(lambda nil
                     (prog2$ (cw-gstack :evisc-tuple
                                        ,(if plusp
                                             nil
                                           '(brr-evisc-tuple state)))
                             (value :invisible))))
         (poly-list-fn (plusp)
                       `(lambda nil
                          (let ((lemma (get-brr-local 'lemma state)))
                            (cond
                             ((eq (record-type lemma) 'linear-lemma)
                              (prog2$
                               (cond
                                ((get-brr-local 'wonp state)
                                 (cw "~X01~|"
                                     (brr-result state)
                                     ,(if plusp
                                          nil
                                        '(brr-evisc-tuple state))))
                                (t (cw "? ~F0 failed.~%"
                                       (get-rule-field lemma :rune))))
                               (value :invisible)))
                             (t
                              (er soft :POLY-LIST
                                  ":POLY-LIST is only legal for a :LINEAR ~
                                   rule."))))))
         (rewritten-rhs-fn (plusp)
                           `(lambda nil
                              (let ((lemma (get-brr-local 'lemma state)))
                                (cond
                                 ((eq (record-type lemma) 'rewrite-rule)
                                  (prog2$
                                   (cond
                                    ((or (get-brr-local 'wonp state)
                                         (member-eq (get-brr-local
                                                     'failure-reason state)
                                                    '(too-many-ifs
                                                      rewrite-fncallp)))
                                     (cw "~X01~|"
                                         (get-brr-local 'brr-result state)
                                         ,(if plusp
                                              nil
                                            '(brr-evisc-tuple state))))
                                    (t (cw "? ~F0 failed.~%"
                                           (get-rule-field lemma :rune))))
                                   (value :invisible)))
                                 (t
                                  (er soft :REWRITTEN-RHS
                                      ":REWRITTEN-RHS is only legal for a ~
                                       :REWRITE rule."))))))
         (target-fn (plusp)
                    `(lambda nil
                       (prog2$ (cw "~X01~|"
                                   (get-brr-local 'target state)
                                   ,(if plusp
                                        nil
                                      '(brr-evisc-tuple state)))
                               (value :invisible))))
         (top-fn (plusp)
                 `(lambda nil
                    (prog2$
                     (cw-gframe 1
                                nil
                                (car (reverse (get-brr-global 'brr-gstack
                                                              state)))
                                ,(if plusp
                                     nil
                                   '(brr-evisc-tuple state)))
                     (value :invisible))))
         (type-alist-fn (plusp)
                        `(lambda nil
                           (prog2$
                            (cw "~%Decoded type-alist:~%")
                            (prog2$
                             (print-type-alist-segments
                              (type-alist-segments
                               (get-brr-local 'type-alist state)
                               nil)
                              (w state)
                              ,(if plusp
                                   nil
                                 '(brr-evisc-tuple state)))
                             (prog2$
                              (cw "~%==========~%Use ~x0 to see actual ~
                                   type-alist.~%"
                                  '(get-brr-local 'type-alist state))
                              (value :invisible))))))
         (unify-subst-fn (plusp)
                         `(lambda nil
                            (prog2$
                             (cw "~*0"
                                 (tilde-*-alist-phrase
                                  (get-brr-local 'unify-subst state)
                                  ,(if plusp
                                       nil
                                     '(brr-evisc-tuple state))
                                  5))
                             (value :invisible)))))
    `(
; If you add commands, change the documentation for brr-commands.
      (:ancestors
       0 ,(ancestors-fn nil))
      (:ancestors+
       0 ,(ancestors-fn t))
      (:btm
       0 ,(btm-fn nil))
      (:btm+
       0 ,(btm-fn t))
      (:eval
       0 ,(already-evaled-fn))
      (:eval!
       0 ,(already-evaled-fn))
      (:eval$
       1 (lambda (runes)
           (prog2$ runes ; avoid issues of ignored variable
                   ,(already-evaled-fn))))
      (:failure-reason
       0 ,(failure-reason-fn nil))
      (:failure-reason+
       0 ,(failure-reason-fn t))
      (:final-ttree
       0 ,(final-ttree-fn nil))
      (:final-ttree+
       0 ,(final-ttree-fn t))
      (:frame
       1 ,(frame-fn nil))
      (:frame+
       1 ,(frame-fn t))
      (:go
       0 (lambda nil

; Like :ok, :man.

           (exit-brr state)))
      (:go!
       0 (lambda nil
           (exit-brr state)))
      (:go$
       1 (lambda (runes)
           (prog2$ runes ; avoid issues of ignored variable
                   (exit-brr state))))
      (:help
       0 (lambda nil
           (doc 'brr-commands)))
      (:hyp
       1 (lambda (n)
           (cond
            ((and (integerp n)
                  (>= n 1)
                  (<= n (length (get-rule-field (get-brr-local 'lemma state)
                                                :hyps))))
             (prog2$ (cw "~X01~|"
                         (nth (1- n)
                              (get-rule-field (get-brr-local 'lemma state)
                                              :hyps))
                         nil)
                     (value :invisible)))
            (t (er soft :HYP
                   ":HYP must be given an integer argument between 1 and ~x0."
                   (length (get-rule-field (get-brr-local 'lemma state)
                                           :hyps)))))))
      (:hyps
       0 (lambda nil
           (prog2$
            (cw "~x0~|"
                (get-rule-field (get-brr-local 'lemma state)
                                :hyps))
            (value :invisible))))
      (:initial-ttree
       0 ,(initial-ttree-fn nil))
      (:initial-ttree+
       0 ,(initial-ttree-fn t))
      (:lhs
       0 (lambda nil
           (let ((val (get-rule-field (get-brr-local 'lemma state)
                                      :lhs)))
             (cond
              ((eq val :get-rule-field-none) ; linear lemma
               (er soft :LHS
                   ":LHS is only legal for a :REWRITE rule."))
              (t
               (prog2$
                (cw "~x0~|" val)
                (value :invisible)))))))
      (:ok
       0 (lambda nil

; Note:  Exit-brr is not yet defined because it calls proceed-from-brkpt1.
; See the note above about that function.

           (exit-brr state)))
      (:ok!
       0 (lambda nil
           (exit-brr state)))
      (:ok$
       1 (lambda (runes)
           (prog2$ runes ; avoid issues of ignored variable
                   (exit-brr state))))
      (:path
       0 ,(path-fn nil))
      (:path+
       0 ,(path-fn t))
      (:poly-list
       0 ,(poly-list-fn nil))
      (:poly-list+
       0 ,(poly-list-fn t))
      (:q
       0 (lambda nil
           (prog2$ (cw "Proceed with some flavor of :ok, :go, or :eval, or use ~
                      :p! to pop or :a! to abort.~%")
                   (value :invisible))))
      (:rewritten-rhs
       0 ,(rewritten-rhs-fn nil))
      (:rewritten-rhs+
       0 ,(rewritten-rhs-fn t))
      (:rhs
       0 (lambda nil
           (let ((val (get-rule-field (get-brr-local 'lemma state)
                                      :rhs)))
             (cond
              ((eq val :get-rule-field-none) ; linear lemma
               (er soft :RHS
                   ":RHS is only legal for a :REWRITE rule."))
              (t
               (prog2$
                (cw "~x0~|" val)
                (value :invisible)))))))
      (:standard-help 0 help)
      (:target
       0 ,(target-fn nil))
      (:target+
       0 ,(target-fn t))
      (:top
       0 ,(top-fn nil))
      (:top+
       0 ,(top-fn t))
      (:type-alist
       0 ,(type-alist-fn nil))
      (:type-alist+
       0 ,(type-alist-fn t))
      (:unify-subst
       0 ,(unify-subst-fn nil))
      (:unify-subst+
       0 ,(unify-subst-fn t))
      (:wonp
       0 (lambda nil
           (prog2$
            (if (get-brr-local 'wonp state)
                (cw "? ~F0 succeeded.~%"
                    (get-rule-field (get-brr-local 'lemma state) :rune))
              (cw "? ~F0 failed.~%"
                  (get-rule-field (get-brr-local 'lemma state) :rune)))
            (value :invisible)))))))

(defun brkpt1 (lemma target unify-subst type-alist ancestors initial-ttree
                     gstack rcnst state)

; #+ACL2-PAR note: since we lock the use of wormholes, brr might be usable
; within the parallelized waterfall.  However, since locks can serialize
; computation, we leave brr disabled for now.  Kaufmann has the following
; reaction to using brr and waterfall parallelism at the same time:

;;; "My immediate reaction is that if someone wants to use brr, they should
;;; turn off parallelism.  I'd probably even make it illegal to have both
;;; waterfall-parallelism enabled and :brr t at the same time."

; Parallelism blemish: cause an error when a user tries to enable parallelism
; and brr is enabled.  Also cause an error when enabling brr and
; waterfall-parallelism is enabled.  We do not label this a "wart", because we
; have documented this lack of feature in
; unsupported-waterfall-parallelism-features.

  (cond
   #+acl2-par ; test is always false anyhow when #-acl2-par
   ((f-get-global 'waterfall-parallelism state)
    nil)
   ((not (f-get-global 'gstackp state))
    nil)
   (t
    (brr-wormhole
     '(lambda (whs)
        (set-wormhole-entry-code
         whs
         (if (assoc-equal (get-rule-field lemma :rune)
                          (cdr (assoc-eq 'brr-monitored-runes
                                         (wormhole-data whs))))
             :ENTER
           :SKIP)))
     `((brr-gstack . ,gstack)
       (brr-alist . ((lemma . ,lemma)
                     (target . ,target)
                     (unify-subst . ,unify-subst)
                     (type-alist . ,type-alist)
                     (ancestors . ,ancestors)
                     (rcnst . ,rcnst)
                     (initial-ttree . ,initial-ttree))))
     '(pprogn
       (push-brr-stack-frame state)
       (put-brr-local 'depth (1+ (or (get-brr-local 'depth state) 0)) state)
       (let ((pair (assoc-equal (get-rule-field (get-brr-local 'lemma state)
                                                :rune)
                                (get-brr-global 'brr-monitored-runes state))))
; We know pair is non-nil because of the entrance test on wormhole above
         (er-let*
          ((okp (eval-break-condition (car pair) (cadr pair) 'wormhole state)))
          (cond
           (okp
            (pprogn
             (cond ((true-listp okp)
                    (stuff-standard-oi okp state))
                   (t state))
             (prog2$ (cw "~%(~F0 Breaking ~F1 on ~X23:~|"
                         (get-brr-local 'depth state)
                         (get-rule-field (get-brr-local 'lemma state)
                                         :rune)
                         (get-brr-local 'target state)
                         (brr-evisc-tuple state))
                     (value t))))
           (t (pprogn
               (pop-brr-stack-frame state)
               (value nil)))))))
     *brkpt1-aliases*))))

(defun brkpt2 (wonp failure-reason unify-subst gstack brr-result final-ttree
                    rcnst state)

; #+ACL2-PAR note: see brkpt1.

  (cond
   #+acl2-par ; test is always false anyhow when #-acl2-par
   ((f-get-global 'waterfall-parallelism state)
    nil)
   ((not (f-get-global 'gstackp state))
    nil)
   (t
    (brr-wormhole
     '(lambda (whs)
        (set-wormhole-entry-code
         whs
         (if (assoc-equal gstack
                          (cdr (assoc-eq 'brr-stack (wormhole-data whs))))
             :ENTER
           :SKIP)))
     `((brr-gstack . ,gstack)
       (brr-alist . ((wonp . ,wonp)
                     (failure-reason . ,failure-reason)
                     (unify-subst . ,unify-subst) ; maybe changed
                     (brr-result . ,brr-result)
                     (rcnst . ,rcnst)
                     (final-ttree . ,final-ttree))))
     '(cond
       ((eq (get-brr-local 'action state) 'silent)
        (prog2$ (cw "~F0)~%" (get-brr-local 'depth state))
                (pprogn
                 (f-put-global 'brr-monitored-runes
                               (get-brr-local 'saved-brr-monitored-runes state)
                               state)
                 (f-put-global 'brr-evisc-tuple
                               (get-brr-local 'saved-brr-evisc-tuple state)
                               state)
                 (pop-brr-stack-frame state)
                 (value nil))))
       ((eq (get-brr-local 'action state) 'print)
        (pprogn
         (put-brr-local-lst (f-get-global 'brr-alist state) state)
         (prog2$ (if (get-brr-local 'wonp state)
                     (cw "~%~F0 ~F1 produced ~X23.~|~F0)~%"
                         (get-brr-local 'depth state)
                         (get-rule-field (get-brr-local 'lemma state) :rune)
                         (brr-result state)
                         (brr-evisc-tuple state))
                   (cw "~%~F0x ~F1 failed because ~@2~|~F0)~%"
                       (get-brr-local 'depth state)
                       (get-rule-field (get-brr-local 'lemma state) :rune)
                       (tilde-@-failure-reason-phrase
                        (get-brr-local 'failure-reason state)
                        1
                        (get-brr-local 'unify-subst state)
                        (brr-evisc-tuple state)
                        (free-vars-display-limit state)
                        state)))
                 (pprogn
                  (f-put-global 'brr-monitored-runes
                                (get-brr-local 'saved-brr-monitored-runes state)
                                state)
                  (f-put-global 'brr-evisc-tuple
                                (get-brr-local 'saved-brr-evisc-tuple state)
                                state)
                  (pop-brr-stack-frame state)
                  (value nil)))))
       (t (pprogn
           (put-brr-local-lst (f-get-global 'brr-alist state) state)
           (er-progn
            (set-standard-oi
             (get-brr-local 'saved-standard-oi state)
             state)
            (cond ((consp (f-get-global 'standard-oi state))
                   (set-ld-pre-eval-print t state))
                  (t (value nil)))
            (pprogn (f-put-global 'brr-monitored-runes
                                  (get-brr-local 'saved-brr-monitored-runes
                                                 state)
                                  state)
                    (f-put-global 'brr-evisc-tuple
                                  (get-brr-local 'saved-brr-evisc-tuple
                                                 state)
                                  state)
                    (prog2$
                     (if (get-brr-local 'wonp state)
                         (cw "~%~F0! ~F1 produced ~X23.~|~%"
                             (get-brr-local 'depth state)
                             (get-rule-field (get-brr-local 'lemma state) :rune)
                             (brr-result state)
                             (brr-evisc-tuple state))
                       (cw "~%~F0x ~F1 failed because ~@2~|~%"
                           (get-brr-local 'depth state)
                           (get-rule-field (get-brr-local 'lemma state) :rune)
                           (tilde-@-failure-reason-phrase
                            (get-brr-local 'failure-reason state)
                            1
                            (get-brr-local 'unify-subst state)
                            (brr-evisc-tuple state)
                            (free-vars-display-limit state)
                            state)))
                     (value t)))))))
     *brkpt2-aliases*))))

; We now develop some of the code for an implementation of an idea put
; forward by Diederik Verkest, namely, that patterns should be allowed
; in :expand hints.

(defrec expand-hint
  ((equiv
    .
    alist) ; :none, a unify-subst or (:constants . unify-subst)
           ; where unify-subst is a partial substitution that must be
           ; extended by the match of pattern against the term being
           ; considered for expansion.  :None means an exact match
           ; is required. :Constants means the successful match must
           ; bind variables to themselves or to quoted evgs.
   .
   (pattern
    .
    ((rune ; nil for a lambda application
      .
      hyp) ; nil if there are no hypotheses of rule, else their conjunction
     .
     (lhs  ; left-hand side of rule, for matching against actual term
      .
      rhs)
     )))
  t)

(defun binds-to-constants-p (unify-subst)
  (cond ((endp unify-subst) t)
        (t (let ((pair (car unify-subst)))
             (and (or (eq (car pair) (cdr pair))
                      (quotep (cdr pair)))
                  (binds-to-constants-p (cdr unify-subst)))))))

(defun expand-permission-result1 (term expand-lst geneqv wrld)

; This is a generalized version of member-equal that asks whether expand-lst
; gives term permission to be expanded, as described in :DOC hints.  Here, term
; is a function application.  We return (mv new-term hyp unify-subst rune k),
; where if new-term is not nil, and assuming hyp if hyp is non-nil, then
; new-term is provably equal to the application of unify-subst to term and, if
; non-nil, rune justifies this equality.  If new-term is not nil then k is the
; length of the tail of expand-lst whose car justifies the expansion of
; new-term, but only if we want to remove that member of expand-lst for
; heuristic purposes; otherwise k is nil.  See expand-permission-result.

  (if expand-lst
      (let ((x (car expand-lst)))
        (cond ((eq x :lambdas)
               (cond ((flambda-applicationp term)
                      (mv (lambda-body (ffn-symb term))
                          nil
                          (pairlis$ (lambda-formals (ffn-symb term))
                                    (fargs term))
                          nil
                          nil))
                     (t (expand-permission-result1 term (cdr expand-lst) geneqv
                                                   wrld))))
              ((not (geneqv-refinementp (access expand-hint x :equiv)
                                        geneqv
                                        wrld))
               (expand-permission-result1 term (cdr expand-lst) geneqv wrld))
              (t (let* ((alist (access expand-hint x :alist))
                        (alist-none-p (eq alist :none))
                        (alist-constants-p (and (not alist-none-p)
                                                (eq (car alist) :constants)))
                        (alist (if alist-constants-p
                                   (cdr alist)
                                 alist)))
                   (mv-let
                    (flg unify-subst0)
                    (cond
                     (alist-none-p
                      (mv (equal (access expand-hint x :pattern) term) nil))
                     (t (one-way-unify1 (access expand-hint x :pattern)
                                        term
                                        alist)))
                    (let ((flg (and flg
                                    (if alist-constants-p

; We require that unify-subst0 bind each variable to itself or to a constant.
; See the long comment in filter-disabled-expand-terms for further discussion.

                                        (binds-to-constants-p unify-subst0)
                                      t))))
                      (cond
                       (flg
                        (mv-let
                         (flg unify-subst)
                         (one-way-unify (access expand-hint x :lhs) term)
                         (cond (flg
                                (mv (access expand-hint x :rhs)
                                    (access expand-hint x :hyp)
                                    unify-subst
                                    (access expand-hint x :rune)
                                    (and (or alist-none-p

; For the example in a comment in expand-permission-result, looping occurs if
; we do not remove the expand hint in the alist-constants-p case.  See the long
; comment in filter-disabled-expand-terms for further discussion.

                                             alist-constants-p)
                                         (length expand-lst))))
                               (t (expand-permission-result1
                                   term (cdr expand-lst) geneqv wrld)))))
                       (t (expand-permission-result1 term (cdr expand-lst)
                                                     geneqv wrld)))))))))
    (mv nil nil nil nil nil)))

(defun remove1-by-position (target-index lst acc)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp acc)
                              (natp target-index)
                              (< target-index (len lst)))))
  (cond
   ((zp target-index)
    (revappend acc (cdr lst)))
   (t (remove1-by-position (1- target-index) (cdr lst) (cons (car lst) acc)))))

(defun expand-permission-result (term rcnst geneqv wrld)

; This is a generalized version of member-equal that asks whether rcnst gives
; term permission to be expanded, as described in :DOC hints.  Here, term is a
; function application.  We return (mv new-term hyp unify-subst rune
; new-rcnst), where if new-term is not nil:

; - term is provably equal to the application of unify-subst to new-term, where
;   if hyp is non-nil then this is under the assumption of the application of
;   unify-subst to hyp,

; - if rune is non-nil, rune justifies the above claim; and

; - new-rcnst is either rcnst or an update of it that removes the reason for
;   expansion of term from the :expand-lst (see long comment below).

  (let ((expand-lst (access rewrite-constant rcnst :expand-lst)))
    (mv-let
     (new-term hyp unify-subst rune posn-from-end)
     (expand-permission-result1 term expand-lst geneqv wrld)
     (cond
      (posn-from-end

; In this case new-term is non-nil; so term will be expanded, and we want to
; remove the reason for this expansion in order to avoid looping.  The thm
; below did indeed cause a rewriting loop through Version_4.3.  (It is OK for
; it to fail, but not with looping.)

;   (defun first-nondecrease (lst)
;     (cond ((endp lst) nil)
;       ((endp (cdr lst)) (list (car lst)))
;       ((> (car lst) (cadr lst)) (list (car lst)))
;       (t (cons (car lst) (first-nondecrease (cdr lst))))))
;
;   (defun removeN (lst n)
;     (cond ((endp lst) nil)
;       ((zp n) lst)
;       (t (removeN (cdr lst) (1- n)))))
;
;   (defthm len-removen  ; Needed to admint next fn.  If you disable this
;     (implies (natp n)  ; lemma, the overflow no longer occurs.
;              (equal (len (removen lst n))
;                     (if (>= n (len lst))
;                         0
;                         (- (len lst) n)))))
;
;   (defun longest-nondecrease (lst)
;     (declare (xargs :measure (len lst)))
;     (if (or (endp lst) (not (true-listp lst))) nil
;         (let* ((first (first-nondecrease lst))
;            (n (len first)))
;       (let ((remain (longest-nondecrease (removeN lst n))))
;         (if (>= n (len remain)) first remain)))))
;
;   ; This is an arithmetic lemma that may seem benign.
;   (defthm equality-difference-hack
;     (implies (and (acl2-numberp x)
;                   (acl2-numberp y))
;              (equal (equal (+ x (- y)) x)
;                     (equal y 0))))
;
;   ; Loops:
;   (thm (implies (true-listp lst)
;                 (equal (equal (len (longest-nondecrease lst)) (len lst))
;                        (equal (longest-nondecrease lst) lst))))

       (assert$
        new-term
        (mv new-term hyp unify-subst rune
            (let ((expand-lst (access rewrite-constant rcnst :expand-lst)))
              (change rewrite-constant rcnst
                      :expand-lst
                      (remove1-by-position (- (length expand-lst)
                                              posn-from-end)
                                           expand-lst
                                           nil))))))
      (t (mv new-term hyp unify-subst rune rcnst))))))

(defun expand-permission-p (term rcnst geneqv wrld)

; Returns nil if we do not have permission from :expand hints to expand, else
; returns rcnst possibly updated by removing term from the :expand-lst field
; (see comments about that in expand-permission-result).  It may be more
; appropriate to use expand-permission-result instead.

  (mv-let (new-term hyp unify-subst rune new-rcnst)
          (expand-permission-result term rcnst geneqv wrld)
          (declare (ignore hyp unify-subst rune))
          (and new-term new-rcnst)))

(defun one-way-unify-restrictions1 (pat term restrictions)
  (cond
   ((null restrictions)
    (mv nil nil))
   (t (mv-let (unify-ans unify-subst)
              (one-way-unify1 pat term (car restrictions))
              (cond
               (unify-ans (mv unify-ans unify-subst))
               (t (one-way-unify-restrictions1 pat term (cdr restrictions))))))))

(defun one-way-unify-restrictions (pat term restrictions)
  (cond
   ((null restrictions)
    (one-way-unify pat term))
   (t (one-way-unify-restrictions1 pat term restrictions))))

(defun ev-fncall! (fn args state aok)

; This function is logically equivalent to ev-fncall.  However, it is
; much faster because it can only be used for certain fn and args: fn
; is a Common Lisp compliant function, not trafficking in stobjs,
; defined as a function in raw Lisp.  The args satisfy the guard of fn.

; Note that return-last is not defined as a function in raw Lisp, so fn should
; not be return-last.  That is also important so that we do not take the
; stobjs-out of return-last, which causes an error.

  (declare (xargs :guard
                  (let ((wrld (w state)))
                    (and (symbolp fn)
                         (not (eq fn 'return-last))
                         (function-symbolp fn wrld)
                         (all-nils (stobjs-in fn wrld))
                         (equal (stobjs-out fn wrld) '(nil))
                         (eq (symbol-class fn wrld)
                             :common-lisp-compliant)
                         (mv-let
                           (erp val latches)
                           (ev (guard fn nil wrld)
                               (pairlis$ (formals fn wrld)
                                         args)
                               state
                               nil
                               t
                               aok)
                           (assert$
                            (null latches)
                            (and (null erp)
                                 val)))))))
  #+(and (not acl2-loop-only) lucid)
  (declare (ignore state))
  #-acl2-loop-only
  (return-from ev-fncall!
               (mv nil (apply fn args) nil))
  (ev-fncall fn args
             nil ; irrelevant arg-exprs (as latches is nil)
             state
             nil ; latches

; Since ev-fncall-meta calls ev-fncall!, the comment about sys-call under
; ev-fncall-meta explains why the following argument of nil is important.

             nil aok))

(defun ev-fncall-meta (fn args state)
  (declare (xargs :guard
                  (and (symbolp fn)
                       (function-symbolp fn (w state)))))

; Fn is a metafunction and args is its list of arguments.  Extended
; metafunctions have three arguments, term, mfc, and state.  Thanks to the
; power of coerce-state-to-object, we actually find the live state in args.
; The args of a vanilla metafunction is just the list containing the term.  Our
; first interest below is to bind the Lisp special *metafunction-context* to
; the context if we are calling an extended metafunction.  This will allow the
; metafunction's subroutines to authenticate their arguments.  We assume that
; the context was correctly constructed by our caller, e.g., rewrite.  Our
; second concern is to avoid guard checking if possible.

  (let (#-acl2-loop-only
        (*metafunction-context* (if (cdr args) (cadr args) nil))
        )
    (cond ((eq (symbol-class fn (w state))
               :common-lisp-compliant)

; Since the guard of the meta function fn is implied by pseudo-termp of its
; arg, and since fn is only applied to terms by our meta facility, and finally
; because we check that fn does not traffic in stobjs (see
; chk-acceptable-meta-rule), we know that it is safe to call the raw Lisp
; version of fn.

; See chk-evaluator-use-in-rule for a discussion of how we restrict the use of
; evaluators in rules of class :meta or :clause-processor, so that we can use
; aok = t in the calls of ev-fncall! and ev-fncall just below.

           (ev-fncall! fn args state t))
          (t (ev-fncall fn args
                        nil ; irrelevant arg-exprs (as latches is nil)
                        state
                        nil ; latches

; The next argument, hard-error-returns-nilp, is nil.  Think hard before
; changing it!  For example, it guarantees that if a metafunction invokes
; sys-call, then the call (er hard ...) under sys-call will cause an error that
; the user can see (and react to).

                        nil t)))))

(defun ev-synp (synp-term unify-subst mfc state)

; Synp-term is the quotation of the term to be evaluated.  Unify-subst is the
; unifying substitution presently in force, and mfc is the meta-level context
; (formerly referred to as "metafunction-context").  This function has been
; modeled (weakly) on ev-fncall-meta.

; This call to synp is the result of the macro-expansion of a syntaxp or
; bind-free hypothesis.  Or at least it might as well be; we check in
; bad-synp-hyp-msg (called in chk-acceptable-rewrite-rule2) that synp-term has
; a form that we know how to handle.

  (let* (#-acl2-loop-only
         (*metafunction-context* mfc)
         (unify-subst1 (if mfc
                           (cons (cons 'mfc mfc)
                                 unify-subst)
                         unify-subst))
         (unify-subst2 (if mfc
                           (cons (cons 'state (coerce-state-to-object state))
                                 unify-subst1)
                         unify-subst)))

; It is tempting to bind the state global safe-mode to t here, using
; state-global-let*.  However, we cannot do that without returning state, which
; we want to avoid since the caller, relieve-hyp, does not return state.  Since
; synp is only used heuristically, it really isn't necessary to use safe mode,
; although it would have been nice for avoiding hard errors (e.g., from car of
; a non-nil atom).

    (ev (get-evg synp-term 'ev-synp) unify-subst2 state nil t t)))

(defun bad-synp-alist1 (alist unify-subst vars-to-be-bound wrld)

; We return nil if the alist is legal, else a string or message suitable for
; printing with ~@.

  (declare (xargs :guard (alistp alist)))
  (if (null alist)
      nil
    (or (let ((key (caar alist))
              (value (cdar alist)))
          (cond ((not (legal-variablep key))
                 (msg "the key ~x0 is not a legal variable" key))
                ((assoc-eq key unify-subst)
                 (msg "the key ~x0 is already bound in the unifying ~
                       substitution, ~x1"
                      key
                      unify-subst))
                ((not (termp value wrld))
                 (msg "the value ~x0 bound to key ~x1 is not a legal term ~
                       (translated into ACL2 internal form) in the current ~
                       ACL2 world"
                      value key))
                ((and (not (eq vars-to-be-bound t))
                      (not (member-eq key vars-to-be-bound)))
                 (msg "the key ~x0 is not a member of the specified list of ~
                       variables to be bound, ~x1"
                      key vars-to-be-bound))
                (t nil)))
        (bad-synp-alist1 (cdr alist) unify-subst vars-to-be-bound wrld))))

(defun bad-synp-alist1-lst (alist-lst unify-subst vars-to-be-bound wrld)
  (cond
   ((endp alist-lst) nil)
   (t (or (bad-synp-alist1 (car alist-lst) unify-subst vars-to-be-bound wrld)
          (bad-synp-alist1-lst (cdr alist-lst) unify-subst vars-to-be-bound
                               wrld)))))

(defun bind-free-info (x unify-subst vars-to-be-bound wrld)

; X is a value returned by a bind-free synp hypothesis, known not to be t or
; nil; unify-subst is an alist containing the unifying substitution gathered so
; far; and vars-to-be-bound is either t or a quoted list of variables.  We
; check that alist is indeed an alist, that it does not bind any variables
; already bound in unify-subst, and that it only binds variables to ACL2 terms.
; If vars-to-be-bound is anything other than t, we also require that alist only
; binds vars present in vars-to-be-bound.

; We return nil if x is a legal alist, t if x is a legal list of alists, and
; otherwise a string or message suitable for printing with ~@.

  (cond
   ((and (true-listp x)
         (alistp (car x)))
    (or (bad-synp-alist1-lst x
                             unify-subst
                             (get-evg vars-to-be-bound 'bad-synp-alist)
                             wrld)
        t))
   ((alistp x)
    (bad-synp-alist1 x
                     unify-subst
                     (get-evg vars-to-be-bound 'bad-synp-alist)
                     wrld))
   (t "it is not an alist")))

(defun evgs-or-t (lst alist)

; Consider the result, lst', of substituting alist into the list of
; terms, lst.  Is every term in lst' a quoted constant?  (For example,
; lst might be (x '23) and alist might be '((x . '7) (y . a)), in
; which case, the answer is "yes, they're all quoted constants.")  If
; so, we return the true-list containing the evgs of the elements of
; lst'; else we return t.

  (cond ((endp lst) nil)
        ((variablep (car lst))
         (let ((temp (assoc-eq (car lst) alist)))
           (if (and temp (quotep (cdr temp)))
               (let ((rest (evgs-or-t (cdr lst) alist)))
                 (cond ((eq rest t) t)
                       (t (cons (cadr (cdr temp)) rest))))
             t)))
        ((fquotep (car lst))
         (let ((rest (evgs-or-t (cdr lst) alist)))
           (cond ((eq rest t) t)
                 (t (cons (cadr (car lst)) rest)))))
        (t t)))

; Essay on Correctness of Meta Reasoning

; Below, we sketch a proof of a theorem asserting the correctness of ACL2's
; meta reasoning, starting with meta rules and then handling clause processor
; rules.  We state correctness for extended metafunctions, but correctness for
; ordinary metafunctions follows trivially by adding mfc and state as ignored
; arguments.  We assume a call of hyp-fn in the meta rule, but of course this
; too is fully general; just define hyp-fn to return 't if it is not already
; present.  We also assume that the metatheorem includes hypotheses of
; (pseudo-termp term) and (alistp a), but of course the metatheorem then
; applies if it omits these hypotheses -- just weaken it by adding them back
; in!  And of course, the mention of meta-extract-hyps is harmless if there are
; no meta-extract hypotheses; in that case, meta-extract-hyps is the empty
; conjunction.

; Let *mfc* be a metafunction context, and let {*mfc*} denote the formula
; asserting the validity of *mfc*, as based on its type-alist.  For example, if
; *mfc* has only one entry in its type-alist, and that entry binds (foo x) to
; (ts-complement *ts-integer*), then {*mfc*} is (not (integerp (foo x))).  For
; notational convenience, we write "ev" below for an evaluator function symbol
; (which thus is definitely not the predefined ACL2 ev function)!

; Recall the ancestor relation: the transitive-reflexive closure of the
; relation "g is an immediate ancestor of f" generated by pairs <f,g> where g
; occurs in the axiom that introduces f.  Note that attachments are not
; considered for this relation.

; Theorem.  Suppose that the following is a theorem, where the only axioms for
; ev are evaluator axioms; where term, a, mfc, and state are variables with
; those exact names (clearly this theorem then generalizes to more arbitrary
; variables); and where META-EXTRACT-HYPS is explained below.

;   (implies (and (pseudo-termp term)
;                 (alistp a)
;                 META-EXTRACT-HYPS ; see below
;                 (ev (hyp-fn term mfc state) a))
;            (equal (ev term a)
;                   (ev (meta-fn term mfc state) a)))

; Suppose in addition that LHS, HYP, and RHS are terms, and that in an
; environment where term is bound to 'LHS, mfc is bound to *mfc* (the current
; metafunction context), and state is bound to the live ACL2 state, the
; following conditions hold, where evaluation may use attachments.

;   (hyp-fn term mfc state) evaluates to 'HYP;
;   (meta-fn term mfc state) evaluates to 'RHS; and
;   META-EXTRACT-HYPS is a conjunction of meta-extract hypotheses,
;     as recognized by remove-meta-extract-contextual-hyps and
;     remove-meta-extract-global-hyps

; Let EXTRA-FNS be a set of 0, 1, or 2 symbols consisting of
; meta-extract-contextual-fact, meta-extract-global-fact+, or both, according
; to which have top-level calls among META-EXTRACT-HYPS.

; Finally, assume the following: ev is not ancestral in any defaxiom or in
; EXTRA-FNS; no ancestor of ev or EXTRA-FNS with an attachment is ancestral in
; meta-fn or hyp-fn; and no ancestor of any defaxiom has an attachment.  (See
; chk-evaluator-use-in-rule for enforcement.  See the example towards the end
; of :DOC evaluator-restrictions for necessity of ruling out functions that are
; "both ancestral in the evaluator and also ancestral in the meta or
; clause-processor functions."  Also see the Appendix below for a remark about
; allowing an attachment to ev even if it is ancestral in meta-fn or hyp-fn.)

; Then the following is a theorem of (mfc-world *mfc*), or equivalently (since
; the worlds have the same logical theory), (w *the-live-state*):

;   (implies (and {*mfc*}
;                 HYP)
;            (equal LHS RHS)).

; The proof of the theorem above uses the following lemma.

; Evaluator Elimination Lemma.  Assume that u is a term, ev is an evaluator for
; the function symbols in u, and a0 is a term of the form (list (cons 'v1 t1)
; ... (cons 'vn tn)) where (v1 ... vn) includes all variables occurring free in
; u and each ti is a term.  Let s be the substitution mapping vi to ti (1 <= i
; <= n).  Then the following is a theorem:

;   (ev 'u a0) = u/s

; Proof:  An easy induction on the structure of term u.  Q.E.D.

; As a warmup, we first prove the theorem in the special case that
; META-EXTRACT-HYPS is the empty conjunction and there are no attachments
; involved.  Let (v1 .. vn) be the variables occurring free in lhs, rhs, or
; hyp.  Let A0 be the term

;   (list (cons 'v1 v1) ... (cons 'vn vn)).

; We instantiate the assumed theorem

;   (implies (and (pseudo-termp term)
;                 (alistp a)
;                 (ev (hyp-fn term mfc state) a))
;            (equal (ev term a) (ev (meta-fn term mfc state) a)))

; replacing term by 'LHS, a by A0, mfc by *mfc*, and state by the live state,
; to obtain the following.

;   (implies (and (pseudo-termp 'LHS)
;                 (alistp A0)
;                 (ev (hyp-fn 'LHS *mfc* *the-live-state*) A0))
;            (equal (ev 'LHS A0)
;                   (ev (meta-fn 'LHS *mfc* *the-live-state*) A0)))

; which is provably equal, by computation, to the following (assuming no
; attachments are used in the computation; we consider attachments later):

;   (implies (ev 'HYP A0)
;            (equal (ev 'LHS A0) (ev 'RHS A0)))

; By functional instantiation, we may replace ev in the hypotheses of this
; theorem by an "extended" evaluator for a set of function symbols including
; all those that occur in hyp, lhs, or rhs.  (A long comment in
; defaxiom-supporters justifies this use of functional instantiation.)  Then by
; the Evaluator Elimination Lemma the formula above simplifies to

;   (implies HYP
;            (equal LHS RHS))

; as desired.

; We next consider the general case, where there may be meta-extract hypotheses
; and attachments may be used.  To start, note that the following is a theorem,
; as it results from the assumed theorem by strengthening hypotheses.  (Here we
; write obj1, obj2, st, and aa for variables not occurring elsewhere in the
; formula.)

;   (implies
;    (and (pseudo-termp term)
;         (alistp a)
;         (forall (obj1)
;                 (ev (meta-extract-contextual-fact obj1 mfc state) a))
;         (forall (obj2 st2 aa)
;                 (ev (meta-extract-global-fact+ obj2 st2 state) aa))
;         (ev (hyp-fn term mfc state) a))
;    (equal (ev term a) (ev (meta-fn term mfc state) a)))

; We instantiate as before, to obtain:

; (1)  (implies
;       (and (pseudo-termp 'LHS)
;            (alistp A0)
;            (forall (obj1)
;             (ev (meta-extract-contextual-fact obj1 *mfc* *the-live-state*)
;                 A0))
;            (forall (obj2 st2 aa)
;             (ev (meta-extract-global-fact+ obj2 st2 *the-live-state*) aa))
;            (ev (hyp-fn 'LHS *mfc* *the-live-state*) A0))
;       (equal (ev 'LHS A0)
;              (ev (meta-fn 'LHS *mfc* *the-live-state*) A0)))

; As before, this reduces by computation to the following formula.

; (2)  (implies
;       (and (forall (obj1)
;             (ev (meta-extract-contextual-fact obj1 *mfc* *the-live-state*)
;                 A0))
;            (forall (obj2 st2 aa)
;             (ev (meta-extract-global-fact+ obj2 st2 *the-live-state*) aa))
;            (ev 'hyp A0))
;       (equal (ev 'LHS A0) (ev 'RHS A0)))

; However, attachments may have been used in evaluating these calls of hyp-fn
; and meta-fn.  So at this point, we know only that (2) is a theorem of the
; evaluation theory.  Our intuition, however, is that the attachments can
; somehow be renamed in an extension of the world so that they don't interfere
; with ev or EXTRA-FNS, which can allow us to conclude by a conservativity
; argument that (2) is a theorem of the current world.  We use that intuition
; to prove the following claim.  We thank Sol Swords for a key observation
; leading to the specific notion of "green" just below, which enabled us to
; complete this proof.

; Claim: (2) is a theorem of the current world.

; Proof of Claim.  We replicate the current world by renaming each function
; symbol for which some ancestor has an attachment.  For convenience, we view
; each function symbol f in the original world, W0, as "red"; and if f is
; renamed to a function symbol f', then f' is "green", the "green version of"
; f.

; Let W1 be the world isomorphic to W0 that results from applying this renaming
; to the existing world, W0.  For a function symbol f in W0, we refer to its
; "W1 version" as the corresponding green function symbol in W1 if such exists
; (that is, if f has an ancestor in W0 with an attachment), else as f itself.
; The notion of "green" in W1 is clearly "closed upward": if g' is green and
; its corresponding red function in W0 is an ancestor of function f in W0, then
; f is renamed to a green version in W1.  Note that every defaxiom event
; consists entirely of red functions since, by hypothesis, no ancestor of any
; defaxiom has an attachment.

; Let W0- be the result of removing defattach events from W0.  Now imagine
; including books for both worlds W0- and W1 to obtain a world W.  Thus, W
; incorporates both W0 without defattach events and W1 with defattach events,
; where every function with an attachment is green.  These worlds are
; compatible because if the axiom in W1 introducing a function symbol f has any
; call of a green function symbol, then f is green by the "closed upward"
; property mentioned above; thus every axiom in W1 introducing a red function
; symbol is redundant with (indeed, identical to) its axiom in W0.

; Let (1') be the result of replacing hyp-fn and meta-fn in W0 with their W1
; versions, hyp-fn' and meta-fn'.  Let fs be the functional substitution that
; contains, for every green ancestor f' of hyp-fn' or meta-fn', the pair <f,f'>
; where f is the red version of f'.  Note that ev is not in the domain of fs,
; since otherwise it would have an ancestor f with an attachment that is also
; an ancestor of hyp-fn or meta-fn, a contradiction.  Thus (1') is the result
; of applying fs to (1), perhaps after replacing green pseudo-termp and/or
; alistp by the provably equal corresponding red function; so we need only show
; that fs is a valid functional substitution for (1) in W.  Recall this comment
; in relevant-constraints, specifying which formulas need to remain theorems
; when fs is applied to them.

; The relevant theorems are the set of all terms, term, such that
;   (a) term mentions some function symbol in the domain of alist,
;   AND
;   (b) either
;      (i) term arises from a definition of or constraint on a function symbol
;          ancestral either in thm or in some defaxiom,
;       OR
;      (ii) term is the body of a defaxiom.

; In this case, the terms satisfying (b) are the axioms that introduce
; ancestors of defaxioms or of hyp-fn, meta-fn, ev, EXTRA-FNS, alistp, or
; pseudo-termp.  We need only consider those that also satisfy (a).  By
; hypothesis no defaxiom has any ancestor with an attachment, so since every
; function symbol is in the domain of fs, we may ignore defaxioms.  We also
; ignore alistp and pseudo-termp since they and their ancestors are fully
; defined, so any replacement of red by green yields a provably equal function.
; Any axiom introducing an ancestor f of hyp-fn or meta-fn clearly is either
; left alone by fs or else is mapped to the axiom introducing the green version
; of f.  The proof is concluded by showing that the axiom introducing an
; arbitrary ancestor f of ev or EXTRA-FNS mentions no symbol in the domain of
; fs.  Suppose to the contrary that g is such a symbol; then since g has a
; green version, there is an ancestor h of g such that h has an attachment.
; But then h is a common ancestor of ev or EXTRA-FNS and also of either hyp-fn
; or meta-fn, contradicting the hypothesis that no such common ancestor has an
; attachment.

; By the Evaluation History Theorem in the Essay on Defattach, there is a world
; W' whose theory is the evaluation theory of W.  (That theorem assumes that
; only encapsulated functions get attachments, but that's immaterial since we
; can always logically replace a defun by an encapsulate that exports the
; corresponding definition rule.)  Clearly any call of hyp-fn or meta-fn that
; completes in W0 with attachments gives the same result as the corresponding
; call of its W1 version in W1 with attachments, hence in W with attachments.
; Therefore, just as (2) followed from (1) in our earlier "warmup" argument,
; (2) also follows from (1') in W'.  Let W2 be the world obtained by
; restricting W' to the set of ancestors of at least one of the (red) functions
; ev, EXTRA-FNS, alistp, and pseudo-termp, and all defaxioms.  As usual the
; theory of W' conservatively extends the theory of W2: both are worlds and W2
; contains all defaxioms.  So (2) is a theorem of W2.  But W2 is contained in
; W0, since W2 consists entirely of red functions by the "closed upward"
; property for green functions.  Therefore (2) is a theorem of W0.

; That completes the proof of the Claim.  Thus (2) is a theorem of the current
; world, and we justifiably ignore attachments for the remainder of this
; discussion.

; Now we functionally instantiate (2).  We do so as in the earlier "warmup"
; argument (which was made without considering attachments), this time after
; introducing an evaluator ev' that includes all currently known function
; symbols, thus obtaining a world w' extending the current logical world, w.

;   (implies
;    (and (forall (obj1)
;          (ev' (meta-extract-contextual-fact obj1 *mfc* *the-live-state*)
;               A0))
;         (forall (obj2 st2 aa)
;          (ev' (meta-extract-global-fact+ obj2 st2 *the-live-state*) aa))
;         (ev' 'HYP A0))
;    (equal (ev' 'LHS A0) (ev' 'RHS A0)))

; As before, the Evaluator Elimination Lemma yields that the following is a
; theorem of w'.

;   (implies
;    (and (forall (obj1)
;          (ev' (meta-extract-contextual-fact obj1 *mfc* *the-live-state*)
;               A0))
;         (forall (obj2 st2 aa)
;          (ev' (meta-extract-global-fact+ obj2 st2 *the-live-state*) aa))
;         HYP)
;    (equal LHS RHS))

; Thus, it remains only to modify the rest of the earlier "warmup" argument by
; dealing with the two universally quantified hypotheses.

; Our first step is to show that the second universally quantified hypothesis,
; where we may as well ignore the forall quantifier, is a theorem of w'.  Let
; term0 be the value returned by (meta-extract-global-fact+ obj2 st2
; *the-live-state*).  Since (ev' *t* aa) is provably equal to *t*, let us
; assume without loss of generality that term0 is not *t*, .  The first case we
; consider is that obj2 is not of the form (:FNCALL fn arglist).  Then we
; claim, without proof (but by appeal to plausibility!), that term0 is provably
; a member of the finite list ('THM1 'THM2 ...), where (THM1 THM2 ...)
; enumerates the theorems of w that can be returned by rewrite-rule-term and
; meta-extract-formula when called by meta-extract-global-fact+.  We thus need
; to show that for each member 'THM of this list, (ev' 'THM aa) is a theorem of
; w'.  By the (argument of the) Evaluator Elimination Lemma, (ev' 'THM aa) is
; provably equal to the instance of THM obtained by replacing each variable x
; by the term (cdr (assoc 'x aa)).  Since THM is a theorem of w and hence w',
; so is this instance.  It remains to consider the other case, i.e., to show
; that for obj2 = (:FNCALL fn arglist), (ev' term0 aa) is a theorem of w'.
; Since we are assuming that term0 is not *t*, we know that (w st2) = (w
; *the-live-state*), which is w, and we also know (by inspection of the
; definition of fncall-term) that term0 = (fncall-term fn arglist st2) for a
; logic-mode function symbol fn of w whose input arity is the length of
; arglist.  But (fncall-term fn arglist st2) is the term (equal (fn . arglist)
; 'val) where (magic-ev-fncall fn arglist st2 ...) = (mv nil val).  We arrange
; that magic-ev-fncall has unknown-constraints, but we conceive of it as being
; axiomatized using clocked, logic mode definitions that follow the definitions
; supporting ev-fncall -- in particular, a clocked, logic-mode version of
; ev-fncall-rec-logical -- such that (mv t nil) is returned when the clock
; expires.  (All of those functions are conceptually in the ground-zero theory,
; but they need not be defined in the ACL2 system implementation.)  Then the
; top-level recursive function is called with a clock that is greater than all
; clocks that would ever be needed for termination under this story for actual
; calls made.  Thus, for every input term, the value returned by ev-fncall is
; provably equal to the value returned by magic-ev-fncall.

; Thus, we now know that the following is a theorem of w':

; (*)
;   (implies
;    (and (forall (obj1)
;          (ev' (meta-extract-contextual-fact obj1 *mfc* *the-live-state*)
;               A0))
;         HYP)
;    (equal LHS RHS))

; Recall that we are trying to show that the following is a theorem of w.

;   (implies
;    (and {*mfc*}
;         HYP)
;    (equal LHS RHS))

; Since the introduction of ev' makes w' a conservative extension of w, it
; suffices to show that the formula just above is a theorem of w'.  Since (*)
; has been shown to be a theorem of w', then it suffices to show that the
; following is a theorem of w'.

; (+)
;   (implies
;    {*mfc*}
;    (forall (obj1)
;     (ev' (meta-extract-contextual-fact obj1 *mfc* *the-live-state*) A0)))

; But we now argue that this is indeed a theorem.  Informally, we think of it
; as a way to formalize the spec for meta-extract-contextual-fact: that it only
; produces terms that evaluate to true.  To see why (+) is a theorem, we focus
; on the case that obj has the form (:rw term obj nil).  Then the above call of
; meta-extract-contextual-fact is equal to a term of the form (equal lhs0
; rhs0), where rhs0 is the result of applying mfc-rw-fn to lhs0, *mfc*, and a
; state whose world is w, the world of *mfc*.  The key is that in such a case,
; mfc-rw-fn rewrites a term to one that is equal to it with respect to the
; hypotheses of *mfc* including its world, w.  A little more precisely, we
; arrange that mfc-rw-fn -- and mfc-ts-fn, and so on -- all have
; unknown-constraints, but we conceive of those constraints as coming from
; clocked, logic mode versions of corresponding prover routines.  For example,
; we conceive of the definition of mfc-rw-fn as following the definition of
; rewrite, but with a clock and using analogous logic-mode supporting functions
; (just as discussed above for magic-ev-fncall), so that the original term is
; returned if the clock expires.  That clock has an initial value that is
; greater than all clocks that could be needed for termination in support of
; all calls ever actually made, in the sense of this story.  This approach
; guarantees that any value computed by rewrite can be legitimately used as a
; value returned by mfc-rw-fn; that is, the returned value is provably equal to
; the call of mfc-rw-fn on its inputs.  But by the (conceived) definition of
; mfc-rw-fn as a logic mode function, the proof obligations pertaining to
; mfc-rw-fn for (+) are provable.  By extending this argument to other mfc-
; functions, we see that (+) is a theorem.

; It remains to modify the arguments above in the case of clause-processors.
; The terms in META-EXTRACT-HYPS are then all calls of
; meta-extract-global-fact+, not meta-extract-contextual-fact.  The argument
; then proceeds in analogy to how it went before, thus for example replacing
; (ev' 'HYP A0) by (forall aa (ev' 'CLAUSES-RESULT aa)), where CLAUSES-RESULT
; is the formal conjunction of the (disjunctions of the) clauses returned by
; the clause-processor.  This hypothesis is a theorem (by the Evaluator
; Elimination Lemma), however, because by hypothesis, these clauses are all
; theorems.

; We remark briefly on the relation between guards and ancestors in our
; criterion for using attachments in meta-level reasoning.  Above, we argue
; that we can restrict to attachments to functions ancestral in metafunctions
; or clause-processors.  But how do we know that evaluation produces theorems
; in the resulting evaluation history?  If raw-Lisp functions installed by ACL2
; involve mbe, then we need to know that their guards hold.  Thus we need to
; know that the guard proof obligation holds when a function is calling its
; attachment.  This was in essence proved when the defattach event was
; admitted, but after applying the entire functional substitution of that
; event.  Thus, we include guards in our notion of ancestor so that this guard
; obligation clearly holds; see the calls of canonical-ancestors-lst in
; function chk-evaluator-use-in-rule.

; So, we enrich the notion of ancestor to include guards.  However, we can
; weaker our notion of ancestor to avoid the next-to-last argument of
; return-last, except when it is used to implement mbe (see function
; canonical-ffn-symbs).  This weakening was inspired by an example sent to us
; by Sol Swords, who derived it from his own experience, and is justified by
; imagining that all such calls of return-last are expanded away before storing
; events.  The parameter rlp passed to our functions is true when this special
; handling of return-last is to be performed.

; Appendix.  Sol Swords observes that the restrictions in the Theorem above may
; be weakened to allow attachments ev* and ev*-lst to ev and ev-lst even if ev
; is ancestral in meta-fn or hyp-fn, provided ev* and ev*-lst are an evaluator
; pair and that neither they nor EXTRA-FNS have any ancestral attachments.  (He
; also notes that these attachments need not be direct: they can be by way of a
; chain of attachments.)  He sketches the following modification of the
; argument above.  As before we derive (2) in the evaluation theory, by
; reducing (1) using evaluation.  Let (2*) be the result of replacing ev by ev*
; in (2); then since ev and ev* are provably equal in the evaluation theory,
; (2*) also holds there.  Since (2*) has no functions with ancestral
; attachments, it holds in the current world by the usual conservativity
; argument, as before.  Finally, complete the argument (the part after the
; Claim) as before, replacing ev by ev*; here we use the fact that ev* is an
; evaluator.

; End of Essay on Correctness of Meta Reasoning

(defun search-type-alist+ (term typ type-alist unify-subst ttree wrld)

; Keep this in sync with search-type-alist.  One difference between this
; function and search-type-alist is that the present function returns one
; additional argument: the remainder of type-alist to be searched.  Another is
; that we assume here that term has at least one variable not bound by
; unify-subst.

; No-change loser except for type-alist.

  (mv-let (term alt-term)
    (cond ((or (variablep term)
               (fquotep term)
               (not (equivalence-relationp (ffn-symb term) wrld)))
           (mv term nil))
          (t ; we know there are free vars in term
           (mv term
               (fcons-term* (ffn-symb term) (fargn term 2) (fargn term 1)))))
    (search-type-alist-rec term alt-term typ type-alist unify-subst ttree)))

(defun oncep (nume-runes match-free rune nume)

; We are given a oncep-override value (e.g., from the :oncep-override value of
; a rewrite constant), nume-runes; a rune, rune and its corresponding nume; and a
; value :once or :all from the match-free field of the rule corresponding to
; that rune.  We want to determine whether we should try only one binding when
; relieving a hypothesis in order to relieve subsequent hypotheses, and return
; non-nil in that case, else nil.

  (if (or (eq nume-runes :clear)
          (<= (car nume-runes) nume))
      (eq match-free :once)
    (member-equal rune (cdr nume-runes))))

(defmacro zero-depthp (depth)

; We use this macro instead of zpf for two reasons.  For one, we have not (as
; of this writing) made zpf a macro, and we want efficiency.  For another, we
; want to be able to experiment to see what sort of stack depth is used for
; a given event.  Use the first body below for that purpose, but use the second
; body for normal operation.

  #+acl2-rewrite-meter ; for stats on rewriter depth
  `(prog2$ #+acl2-loop-only
           ,depth
           #-acl2-loop-only
           (setq *rewrite-depth-max* (max ,depth *rewrite-depth-max*))
           nil)
  #-acl2-rewrite-meter ; normal stats (no stats)
  `(eql (the-fixnum ,depth) 0))

(defmacro rdepth-error (form &optional preprocess-p)
  (if preprocess-p
      (let ((ctx ''preprocess))
        `(prog2$ (er hard ,ctx
                     "The call depth limit of ~x0 has been exceeded in the ~
                      ACL2 preprocessor (a sort of rewriter).  There might be ~
                      a loop caused by some set of enabled simple rules.  To ~
                      see why the limit was exceeded, ~@1retry the proof with ~
                      :hints~%  :do-not '(preprocess)~%and then follow the ~
                      directions in the resulting error message.  See :DOC ~
                      rewrite-stack-limit for a possible solution when there ~
                      is not a loop."
                     (rewrite-stack-limit wrld)
                     (if (f-get-global 'gstackp state)
                         ""
                       "execute~%  :brr t~%and next "))
                 ,form))
    (let ((ctx ''rewrite))
      `(prog2$ (er hard ,ctx
                   "The call depth limit of ~x0 has been exceeded in the ACL2 ~
                    rewriter.  To see why the limit was exceeded, ~@1execute ~
                    the form (cw-gstack) or, for less verbose output, instead ~
                    try (cw-gstack :frames 30).  You may then notice a loop ~
                    caused by some set of enabled rules, some of which you ~
                    can then disable; see :DOC disable.  For a possible ~
                    solution when there is not a loop, see :DOC ~
                    rewrite-stack-limit."
                   (rewrite-stack-limit wrld)
                   (if (f-get-global 'gstackp state)
                       ""
                     "first execute~%  :brr ~
                      t~%and then try the proof again, and then "))
               ,form))))

(defun bad-synp-hyp-msg1 (hyp bound-vars all-vars-bound-p wrld)

; A hyp is a "good synp hyp" if either it does not mention SYNP as a function
; symbol or else it is a call of SYNP that we know how to handle in our
; processing of rewrite and linear rules.  We return nil as the first value in
; this case, or else an appropriate message explaining the problem.  See
; bad-synp-hyp-msg.

  (if (ffnnamep 'synp hyp)
      (cond ((not (eq (ffn-symb hyp) 'synp))

; Through Version_8.1, the message below seemed to suggest that we insist that
; synp only occur as the top function symbol of hyp.  However, we can actually
; allow it below that in a non-executable context, provided it also occurs as
; the top function symbol.  So we changed "can occur only" to "should occur
; only", since really, this weaker check is probably good enough.

             (mv (cons
                  "a call of syntaxp or bind-free should occur only ~
                   at the top level of a hypothesis, but in ~x0 it ~
                   appears elsewhere but not at the top level."
                  (list (cons #\0 (untranslate hyp t wrld))))
                 bound-vars all-vars-bound-p))
            ((not (all-quoteps (fargs hyp)))
             (mv (cons
                  "a call of ~x0 in a hypothesis should be made on quoted ~
                   arguments, but that is not true for the hypothesis, ~x1."
                  (list (cons #\0 'synp)
                        (cons #\1 (untranslate hyp nil wrld))))
                 bound-vars all-vars-bound-p))

; Note that we check for the well-formedness of a call to synp in
; translate, so the following bindings should be safe.

            (t
             (let* ((term-to-be-evaluated (unquote (fargn hyp 3)))
                    (vars (all-vars term-to-be-evaluated))
                    (saved-term (unquote (fargn hyp 2)))
                    (vars-to-be-bound (unquote (fargn hyp 1))))
               (cond ((not (termp term-to-be-evaluated wrld))
                      (mv (cons
                           "the term to be evaluated by the syntaxp or ~
                            bind-free hypothesis must be an ACL2 term, but ~
                            this is not the case in ~x0.  The term's internal ~
                            (translated) form is ~x1."
                           (list (cons #\0 (untranslate hyp nil wrld))
                                 (cons #\1 term-to-be-evaluated)))
                          bound-vars all-vars-bound-p))
                     ((or (variablep saved-term)
                          (fquotep saved-term)
                          (not (member-eq (ffn-symb saved-term)
                                          '(syntaxp bind-free))))
                      (mv (cons
                           "a synp hyp has been found which does not appear to ~
                            have come from a syntaxp or bind-free hypothesis: ~
                            ~x0. This is not, at present, allowed.  If we are ~
                            in error or you believe we have been otherwise too ~
                            restrictive, please contact the maintainers of ~
                            ACL2."
                           (list (cons #\0 (untranslate hyp nil wrld))))
                          bound-vars all-vars-bound-p))
                     ((and (not (equal vars-to-be-bound nil)) ; not syntaxp
                           (not (equal vars-to-be-bound t))
                           (or (collect-non-legal-variableps vars-to-be-bound)
                               all-vars-bound-p
                               (intersectp-eq vars-to-be-bound bound-vars)))
                      (mv (cons
                           "the vars to be bound by a bind-free hypothesis ~
                            must be either t or a list of variables which ~
                            are not already bound.  This is not the case in ~
                            ~x0.  The vars to be bound are ~x1 and the vars ~
                            already bound are ~x2."
                           (list (cons #\0 (untranslate hyp t wrld))
                                 (cons #\1 vars-to-be-bound)
                                 (cons #\2
                                       (if all-vars-bound-p
                                           '<all_variables>
                                           (reverse bound-vars)))))
                          bound-vars all-vars-bound-p))
                     ((and (not all-vars-bound-p)
                           (not (subsetp-eq (set-difference-eq vars
                                                               '(state mfc))
                                            bound-vars)))
                      (mv (cons
                           "any vars, other than ~x2 and ~x3, used in ~
                            the term to be evaluated by a ~
                            syntaxp or bind-free hypothesis must already be ~
                            bound.  This does not appear to be the case ~
                            in ~x0.  The vars already bound are ~x1."
                           (list (cons #\0 (untranslate hyp t wrld))
                                 (cons #\1 (reverse bound-vars))
                                 (cons #\2 'mfc)
                                 (cons #\3 'state)))
                          bound-vars all-vars-bound-p))
                     ((or (member-eq 'state vars)
                          (member-eq 'mfc vars))
                      (cond ((or (member-eq 'state bound-vars)
                                 (member-eq 'mfc bound-vars)
                                 all-vars-bound-p)

; The point here is that if state or mfc is already bound, then the user may be
; confused as to whether the present uses are intended to refer to the "real"
; state and mfc or whether they are intended to refer to the variables already
; bound.

                             (mv (cons
                                  "we do not allow the use of state or mfc ~
                                   in a syntaxp or bind-free hypothesis ~
                                   in a context where either state or ~
                                   mfc is already bound.  This restriction ~
                                   is violated in ~x0.  The vars already ~
                                   bound are ~x1."
                                  (list (cons #\0 (untranslate hyp nil wrld))
                                        (cons #\1 (if all-vars-bound-p
                                                      '<all_variables>
                                                    (reverse bound-vars)))))
                                 bound-vars all-vars-bound-p))
                            ((or (not (eq 'state (car vars)))
                                 (member-eq 'state (cdr vars))
                                 (not (eq 'mfc (cadr vars)))
                                 (member-eq 'mfc (cddr vars))
                                 (and (not all-vars-bound-p)
                                      (not (subsetp-eq (cddr vars) bound-vars))))
                             (mv (cons
                                  "if either state or mfc is a member of the ~
                                   vars of the term to be evaluated, we ~
                                   require that both mfc and state be present ~
                                   and that they be the last two args of the ~
                                   term, in that order.  We also require that ~
                                   the remaining vars be already bound.  This ~
                                   does not appear to be the case in ~x0.  The ~
                                   vars already bound are ~x1."
                                  (list (cons #\0 (untranslate hyp nil wrld))
                                        (cons #\1 (if all-vars-bound-p
                                                      '<all_variables>
                                                    (reverse bound-vars)))))
                                 bound-vars all-vars-bound-p))
                            (t
                             (mv nil
                                 (cond ((eq vars-to-be-bound nil)
                                        bound-vars)
                                       ((eq vars-to-be-bound t)
                                        bound-vars)
                                       (t
                                        (union-eq vars-to-be-bound
                                                  bound-vars)))
                                 (or all-vars-bound-p
                                     (equal vars-to-be-bound t))))))
                     (t
                      (mv nil
                          (cond ((equal vars-to-be-bound nil)
                                 bound-vars)
                                ((equal vars-to-be-bound t)
                                 bound-vars)
                                (t
                                 (union-eq vars-to-be-bound
                                           bound-vars)))
                          (or all-vars-bound-p
                              (equal vars-to-be-bound t))))))))

; We do not have a synp hyp.

    (mv nil
        (union-eq (all-vars hyp) bound-vars)
        all-vars-bound-p)))

(defun bad-synp-hyp-msg (hyps bound-vars all-vars-bound-p wrld)

; We check hyps for any bad synp hyps and return either nil, if there
; were none found, or an error message suitable for use with ~@.  This
; message will describe what is wrong with the first (and only) bad
; synp hyp found and will be used in chk-acceptable-rewrite-rule2
; (and related checkers for linear and quoted constant rules)
; and in rewrite-with-lemma.

; Hyps is a list of hypotheses we are to check, bound-vars is an
; accumulator of all the vars known to be bound (initially set to the
; vars in the lhs of the rewrite rule or the trigger term of a linear
; rule), and all-vars-bound-p is a boolean which indicates whether all
; vars are potentially bound (due to the presence of a 't var-list in
; an earlier synp hyp) and is initially nil.

; See bad-synp-hyp-msg1 for the checks we perform.  Crudely, we
; check that a synp hyp looks like it came from the expansion of a
; syntaxp or bind-free hyp and that it does not appear to rebind any
; vars that are already bound.

  (if (null hyps)
      nil
    (mv-let (bad-synp-hyp-msg bound-vars all-vars-bound-p)
      (bad-synp-hyp-msg1 (car hyps) bound-vars all-vars-bound-p wrld)
      (or bad-synp-hyp-msg
          (bad-synp-hyp-msg (cdr hyps) bound-vars all-vars-bound-p wrld)))))

(defmacro sl-let (vars form &rest rest)

; Keep in sync with sl-let@par.

  (let ((new-vars (cons 'step-limit vars)))
    `(mv-let ,new-vars
             ,form
             (declare (type (signed-byte 30) step-limit))
             ,@rest)))

#+acl2-par
(defmacro sl-let@par (vars form &rest rest)

; Keep in sync with sl-let.

  (declare (xargs :guard ; sanity check inherited from mv-let@par
                  (member-eq 'state vars)))
  (let ((new-vars (cons 'step-limit vars)))
    `(mv-let@par ,new-vars
                 ,form
                 (declare (type (signed-byte 30) step-limit))
                 ,@rest)))

(defmacro rewrite-entry-extending-failure (unify-subst failure-reason form
                                                       &rest args)
  `(mv-let (step-limitxx relieve-hyps-ansxx failure-reason-lstxx unify-substxx
                         ttreexx allpxx rw-cache-alist-newxx)
           (rewrite-entry ,form ,@args)
           (mv step-limitxx relieve-hyps-ansxx
               (and (null relieve-hyps-ansxx)
                    (cons (check-vars-not-free
                           (step-limitxx relieve-hyps-ansxx
                                         failure-reason-lstxx unify-substxx
                                         ttreexx allpxx rw-cache-alist-newxx)
                           (cons ,unify-subst ,failure-reason))
                          failure-reason-lstxx))
               unify-substxx ttreexx allpxx rw-cache-alist-newxx)))

(defun set-difference-assoc-eq (lst alist)
  (declare (xargs :guard (and (true-listp lst)
                              (alistp alist)
                              (or (symbol-listp lst)
                                  (symbol-alistp alist)))))
  (cond ((endp lst) nil)
        ((assoc-eq (car lst) alist)
         (set-difference-assoc-eq (cdr lst) alist))
        (t (cons (car lst) (set-difference-assoc-eq (cdr lst) alist)))))

(defun extend-unify-subst (alist unify-subst)

; We attempt to keep all terms in quote-normal form, which explains the use of
; quote-normal-form below.  There are also three calls of quote-normal-form in
; rewrite-with-lemma.

; The rest of this remark was written before the introduction of the function
; quote-normal-form, using (sublis-var nil ...) instead, which, unlike
; quote-normal-form, recurred inside calls of HIDE.

; We wondered if for large problems, the cost of exploring large terms might
; not be worth the benefit of maintaining quote-normal form, so we tried
; replacing the pairlis$ call below with, simply, alist.  However, we found
; relatively little benefit, as we now describe.

; Below are timings from 4 different configurations.  In all cases, we
; abstained from doing anything else on the laptop during the run.  So the
; differences you see are real, up to GC time.  All the runs were conducted
; sequentially in the same image.
;
; The first configuration, A, is as reported in the Stateman paper (by J Moore)
; at the 2015 ACL2 Workshop.  The relevant fact is that sublis-var1 is memoized
; when the substitution is nil and the term has a HIDE on it.  Three runs were
; done to see if the time would stabilize.  The time reported in the paper was
; 275 seconds.
;
; ; A runs:
; ; 388.94 seconds realtime, 382.18 seconds runtime
; ; 265.68 seconds realtime, 262.71 seconds runtime
; ; 274.68 seconds realtime, 272.27 seconds runtime
;
; The next configuration is the same as A except that here, sublis-var1 is not
; memoized.  So here you see the extra cost of the sublis-var nil calls.
;
; ; B runs:
; ; 485.81 seconds realtime, 482.91 seconds runtime
; ; 494.81 seconds realtime, 491.70 seconds runtime
;
; The next configuration is with the change described above, as follows: we
; replaced the pairlis$ call with the variable, alist, and replaced each
; (sublis-var nil X) call in rewrite-with-lemma by the corresponding X.  Note
; that sublis-var is not memoized here either.
;
; ; C runs:
; ; 281.10 seconds realtime, 278.37 seconds runtime
; ; 284.11 seconds realtime, 281.30 seconds runtime
;
; So eliminating the call has about the same effect on time as memoizing it.
;
; The final experiment leaves memoization on (for sublis-var1 with nil
; substitution and a term beginning with HIDE) but also includes the
; modifications described above, that is, to avoid the (sublis-var nil ...)
; call in this function and the three such calls in rewrite-with-lemma.

; D runs:
; 273.10 seconds realtime, 270.52 seconds runtime
; 299.00 seconds realtime, 277.31 seconds runtime

; This suggests that memoizing sublis-var as Stateman does and eliminating
; these sublis-var calls is marginally worse than just memoizing sublis-var (as
; in A).  That seems rather unlikely, so we are willing to conclude that the
; differences are just noise.  So we have decided to keep these four calls of
; sublis-var-lst or sublis-var, which will avoid the potential pain of
; modifying some books to accommodate their removal.  (Actually no regression
; books as of early November 2015 needed to be modified; but other user books
; might need to be.)

  (append (pairlis$ (strip-cars alist)
                    (quote-normal-form (strip-cdrs alist)))
          unify-subst))

(defun relieve-hyp-synp (rune hyp0 unify-subst rdepth type-alist wrld state
                              fnstack ancestors backchain-limit
                              simplify-clause-pot-lst rcnst gstack ttree bkptr)

; Hyp0 is a call of synp.  This special case of relieve-hyp returns some of the
; same values as does relieve-hyp, namely the following
; where wonp is t, nil, or :unify-subst-list:

; (mv wonp failure-reason unify-subst' ttree'')

  (let* ((synp-fn (car (get-evg (fargn hyp0 2) 'relieve-hyp)))
         (mfc (if (member-eq 'state (all-vars (get-evg (fargn hyp0 3)
                                                       'relieve-hyp)))
                  (make metafunction-context
                        :rdepth rdepth
                        :type-alist type-alist

; The user-supplied term for synp may use the mfc in arbitrary ways, so we
; don't have a clear :obj and we cannot do better than equality for :geneqv.

                        :obj '?
                        :geneqv nil
                        :wrld wrld
                        :fnstack fnstack
                        :ancestors ancestors
                        :backchain-limit backchain-limit
                        :simplify-clause-pot-lst simplify-clause-pot-lst
                        :rcnst rcnst
                        :gstack (if bkptr

; Bkptr is nil when we turn off tracking, e.g. for show-rewrites.

                                    (push-gframe 'synp
                                                 bkptr
                                                 (if (eq synp-fn 'syntaxp)
                                                     synp-fn
                                                   'bind-free))
                                  gstack)
                        :ttree ttree
                        :unify-subst unify-subst)
                nil)))
    (mv-let (erp val latches)
            (ev-synp (fargn hyp0 3) unify-subst mfc state)
            (declare (ignore latches))
            #-acl2-loop-only (setq *deep-gstack* gstack)
            (cond
             ((or erp (null val))
              (let ((sym (cond ((null mfc) synp-fn)
                               ((eq synp-fn 'syntaxp) 'syntaxp-extended)
                               ((eq synp-fn 'bind-free) 'bind-free-extended)
                               (t ; impossible?
                                synp-fn))))
                (mv nil
                    (list sym erp val)
                    unify-subst
                    ttree)))
             ((eq synp-fn 'syntaxp)
              (cond
               ((eq val t)
                (mv t nil unify-subst
                    (push-lemma
                     (fn-rune-nume 'synp nil nil wrld)

; It is tempting to record the following:

;                           (definition-runes
;                             (all-fnnames (get-evg (fargn hyp0 3) 'relieve-hyp))
;                             t wrld))

; However, some of the functions in question may be :program mode functions, in
; which case they will not have executable-counterpart runes.  It is fine not
; to track these, even if they are in logic mode, since these functions
; contribute only heuristically to the proof, not logically; and besides, it
; would be confusing to report runes that are disabled, which they may well be.

                     ttree)))
               (t
                (mv (er hard 'relieve-hyp
                        "The evaluation of the SYNTAXP test in :HYP ~x0 of ~
                         rule ~x1 produced something other than t or nil, ~
                         ~x2. This was unexpected and is illegal.  Please ~
                         contact the maintainers of ACL2 with a description ~
                         of the situation that led to this message."
                        (get-evg (fargn hyp0 1) 'relieve-hyp)
                        rune
                        val)
                    nil unify-subst ttree))))
             (t (let ((info (bind-free-info val unify-subst (fargn hyp0 1)
                                            wrld)))
                  (cond
                   ((eq info nil)
                    (mv t nil
                        (extend-unify-subst val unify-subst)
                        (push-lemma
                         (fn-rune-nume 'synp nil nil wrld) ; see comment above
                         ttree)))
                   ((eq info t)
                    (mv :unify-subst-list nil
                        val ; a list of alists with which to extend unify-subst
                        (push-lemma
                         (fn-rune-nume 'synp nil nil wrld) ; see comment above
                         ttree)))
                   (t
                    (mv (er hard 'relieve-hyp
                            "The evaluation of the BIND-FREE form in ~
                             hypothesis ~p0 of rule ~x1 produced the result ~
                             ~x2, which is illegal because ~@3."
                            (untranslate hyp0 t wrld)
                            rune val info)
                        nil unify-subst ttree)))))))))

(defmacro push-lemma+ (rune ttree rcnst ancestors rhs rewritten-rhs)

; Warning: Keep this in sync with push-splitter?; see the comment there for how
; these two macros differ.

  `(cond ((and (null ,ancestors)
               (access rewrite-constant ,rcnst :splitter-output)
               (ffnnamep-hide 'if ,rhs t)
               (ffnnamep-hide 'if ,rewritten-rhs t))
          (let ((rune ,rune)
                (ttree ,ttree))
            (add-to-tag-tree 'splitter-if-intro rune
                             (push-lemma rune ttree))))
         (t (push-lemma ,rune ,ttree))))

(defmacro push-splitter? (rune ttree rcnst ancestors rhs rewritten-rhs)

; Warning: Keep this in sync with push-lemma+, which differs in three ways:
; that macro does not require that rune is bound to a symbol, it does not allow
; the value of rune to be nil, and it also adds a 'lemma tag.

; We could easily remove the guard below, which simply avoids the need to bind
; rune and hence ttree.

  (declare (xargs :guard (symbolp rune)))
  `(cond ((and ,rune
               (null ,ancestors)
               (access rewrite-constant ,rcnst :splitter-output)
               (ffnnamep-hide 'if ,rhs t)
               (ffnnamep-hide 'if ,rewritten-rhs t))
          (add-to-tag-tree 'splitter-if-intro ,rune ,ttree))
         (t ,ttree)))

(defmacro prepend-step-limit (n form)
  (let ((vars (if (consp n)
                  n
                (make-var-lst 'x n))))
    `(mv-let ,vars
             ,form
             (mv step-limit ,@vars))))

; We are almost ready to define the rewrite mutual-recursion nest.  But first
; we provide support for the rw-cache; see the Essay on Rw-cache.

(defrec rw-cache-entry

; This structure is a record of a failed attempt at relieve-hyps.  The
; :step-limit is set to the step-limit upon entry to the failed relieve-hyps
; call.

; There are two cases, which we call the "normal-failure" case and the
; "free-failure" case.  In the free-failure case, a preceding hypothesis bound
; a free variable without being a binding hypothesis or being a call of
; bind-free that returns a single substitution; otherwise, we are in the
; normal-failure case.

; Consider first the normal-failure case.  Then the :unify-subst is the
; restriction of a failed attempt to rewrite the nth hypothesis, stored in
; :hyp-info, to true, where the :failure-reason has the form (n . &), and the
; indexing is one-based.

; In the free-failure case, failure-reason is a structure satisfying
; free-failure-p, i.e.  of the form (:RW-CACHE-ALIST . alist), where each key
; of alist is a unify-subst and each value is a failure reason (either
; normal-failure or recursively of this form).  We sometimes call alist an
; "rw-cache-alist".  The :hyp-info field contains the :hyps field of the
; rewrite-rule, and the :step-limit is as above.  The following example
; illustrates the form of the :failure-reason.  Suppose we have a rewrite rule
; whose left-hand side has variables x1 and x2, such that hypothesis 2 binds
; free variable y and hypothesis 6 binds free variable z.  Suppose that when
; binding x1 to a1 and x2 to a2 we find:

; - bind y to b1
;    - obtained failure-reason-1 at hypothesis 4
; - bind y to b2
;    - bind z to c1
;      - obtained failure-reason-2 at hypothesis 8
;    - bind z to c2
;      - obtained failure-reason-3 at hypothesis 8

; Then the :unify-subst is ((x1 . a1) (x2 . a2)), and the corresponding
; :failure-reason looks as follows.

; (:RW-CACHE-ALIST
;  (((y . b1) (x1 . a1) (x2 . a2)) ; unify-subst
;   . failure-reason-1)
;  (((y . b2) (x1 . a1) (x2 . a2)) ; unify-subst
;   . (:RW-CACHE-ALIST
;      (((z . c1) (y . b2) (x1 . a1) (x2 . a2)) ; unify-subst
;       . failure-reason-2)
;      (((z . c2) (y . b2) (x1 . a1) (x2 . a2)) ; unify-subst
;       . failure-reason-3))))

; Note that if for example we bind y to b3 at hypothesis 2 and fail by finding
; no binding of z at hypothesis 6, then we do not store a failure-reason; and
; this is reasonable, because maybe a later context will find a binding of z.
; Another way to look at this case is to notice that above, we are storing a
; failure reason for each binding of z; so if there are no bindings of z, then
; there is nothing to store!

; We use lexorder a lot, so we put the step-limit field first.

  ((step-limit . failure-reason)
   .
   (unify-subst . hyp-info))
  t)

(defmacro free-failure-p (r)
  `(eq (car ,r) :RW-CACHE-ALIST))

(defabbrev combine-free-failure-reasons (r1 r2)

; See the Essay on Rw-cache.

; R1 and r2 are failure reasons satisfying free-failure-p.  We return (mv flg
; r), where r is a merge of the given failure reasons and if flg is t, then r
; is equal (in fact eq) to r2.

  (mv-let (flg alist)
          (combine-free-failure-alists (cdr r1) (cdr r2))
          (cond (flg (mv t r2))
                (t (mv nil (cons :RW-CACHE-ALIST alist))))))

(defun combine-free-failure-alists (a1 a2)

; A1 and a2 are rw-cache-alists, as described in (defrec rw-cache-entry ...).

  (cond
   ((endp a1) (mv t a2))
   (t
    (let ((pair (assoc-equal (caar a1) a2)))
      (cond
       (pair ; then first update a2 with (car a1)
        (let ((failure-reason-1 (cdar a1))
              (failure-reason-2 (cdr pair)))
          (mv-let
           (flg a2)
           (cond
            ((not (free-failure-p failure-reason-2)) ; keep normal-failure reason
             (mv t a2))
            ((not (free-failure-p failure-reason-1))
             (mv nil (put-assoc-equal (caar a1) failure-reason-1 a2)))
            (t
             (mv-let
              (flg2 new-reason)
              (combine-free-failure-reasons failure-reason-1 failure-reason-2)
              (cond
               (flg2 (mv t a2))
               (t (mv nil (put-assoc-equal (caar a1) new-reason a2)))))))
           (cond
            (flg (combine-free-failure-alists (cdr a1) a2))
            (t ; a2 has been updated, so returned flag must be nil
             (mv-let
              (flg alist)
              (combine-free-failure-alists (cdr a1) a2)
              (declare (ignore flg))
              (mv nil alist)))))))
       (t ; (null pair); in this case, a2 has not yet been updated
        (mv-let
         (flg alist)
         (combine-free-failure-alists (cdr a1) a2)
         (declare (ignore flg))
         (mv nil (cons (car a1) alist)))))))))

(defun combine-sorted-rw-cache-lists1 (l1 l2)

; We are given two rw-cache-lists l1 and l2, where each element is an
; rw-cache-entry record (not t) and the lists are sorted by lexorder.  We
; return (mv flg lst), where lst is a sorted list that suitably combines l1 and
; l2, and if flg is true then lst is l2.  Note that t is not a member of the
; result.

  (cond ((endp l1) (mv t l2))
        ((endp l2) (mv nil l1))
        ((and (equal (access rw-cache-entry (car l1) :unify-subst)
                     (access rw-cache-entry (car l2) :unify-subst))
              (equal (access rw-cache-entry (car l1) :hyp-info)
                     (access rw-cache-entry (car l2) :hyp-info)))
         (mv-let
          (flg lst)
          (combine-sorted-rw-cache-lists1 (cdr l1) (cdr l2))
          (let ((r1 (access rw-cache-entry (car l1) :failure-reason))
                (r2 (access rw-cache-entry (car l2) :failure-reason)))
            (cond
             ((and (free-failure-p r1)
                   (free-failure-p r2))
              (mv-let
               (flg2 failure-reason)
               (combine-free-failure-reasons r1 r2)
               (cond
                ((and flg flg2)
                 (mv t l2))
                (t (mv nil (cons (change rw-cache-entry (car l2)
                                         :failure-reason
                                         failure-reason)
                                 lst))))))

; Otherwise we prefer r2 to r1, at least if flg is true (so that we return a
; true flg).  If r2 is a free-failure-p and r1 is not, then r1 would actually
; be preferable.  But we expect that case to be virtually impossible, both
; because the failure that produced r1 would presumably have produced r2 as
; well, and because the :hyp-info field of r1 would be a single hypothesis but
; for r2 it would be a list of hypotheses.

             (flg (mv flg l2))
             (t (mv nil (cons (car l2) lst)))))))
        ((lexorder (car l1) (car l2))
         (mv-let (flg lst)
                 (combine-sorted-rw-cache-lists1 (cdr l1) l2)
                 (declare (ignore flg))
                 (mv nil (cons (car l1) lst))))
        (t
         (mv-let (flg lst)
                 (combine-sorted-rw-cache-lists1 l1 (cdr l2))
                 (cond (flg (mv t l2))
                       (t (mv nil (cons (car l2) lst))))))))

(defun split-psorted-list1 (lst acc)
  (cond ((endp lst)
         (mv acc nil))
        ((eq (car lst) t)
         (assert$ (not (member-eq t (cdr lst)))
                  (mv acc (cdr lst))))
        (t (split-psorted-list1 (cdr lst) (cons (car lst) acc)))))

(defun split-psorted-list (lst)

; Lst is a list with at most one occurrence of t, the idea being that the tail
; after T is sorted.  We return the list of elements of lst preceding that
; occurrence of T if any, in any order, together with the list of elements
; after the T (possibly empty, if there is no such T), in their given order.

; We assume that (car lst) is not t.

  (cond ((member-eq t (cdr lst))
         (split-psorted-list1 (cdr lst) (list (car lst))))
        (t (mv lst nil))))

(defun merge-lexorder-fast (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2))
                  :measure (+ (len l1) (len l2))))
  (cond ((endp l1) (mv t l2))
        ((endp l2) (mv nil l1))
        ((lexorder (car l1) (car l2))
         (mv-let (flg x)
                 (merge-lexorder-fast (cdr l1) l2)
                 (declare (ignore flg))
                 (mv nil (cons (car l1) x))))
        (t ; (lexorder (car l2) (car l1))
         (mv-let (flg x)
                 (merge-lexorder-fast l1 (cdr l2))
                 (cond (flg (mv t l2))
                       (t (mv nil (cons (car l2) x))))))))

(defun merge-sort-lexorder-fast (l)

; We have considered calling merge-lexorder below instead of
; merge-lexorder-fast.  However, the realtime of a one-processor regression
; increased by nearly 1% when we tried that -- not a lot, but enough to keep
; using merge-lexorder-fast, especially since it might generate less garbage
; (which could be useful for ACL2(p)).  Note: The above experiment took place
; before adding the cddr case, and before removing the equal case from
; merge-lexorder-fast, which should be an impossible case for our application
; of sorting the "front" (unsorted) part of a psorted list.  But we did a
; second experiment with a later version, on an "insert-proof" example from
; Dave Greve.

; Using merge-lexorder-fast:
; ; 387.18 seconds realtime, 297.43 seconds runtime
; ; (19,564,695,712 bytes allocated).
; Total GC time: 44573873 T

; Using merge-lexorder:
; ; 388.84 seconds realtime, 298.74 seconds runtime
; ; (19,739,620,816 bytes allocated).
; Total GC time: 44831695 T

; So, we'll use merge-lexorder-fast.

  (declare (xargs :guard (true-listp l)
                  :measure (len l)))
  (cond ((endp (cdr l)) l)
        ((endp (cddr l)) ; avoid the cons built by calling take below
         (cond ((lexorder (car l) (cadr l)) l)
               (t (list (cadr l) (car l)))))
        (t (let* ((n (length l))
                  (a (ash n -1)))
             (mv-let (flg x)
                     (merge-lexorder-fast
                      (merge-sort-lexorder-fast (take a l))
                      (merge-sort-lexorder-fast (nthcdr a l)))
                     (declare (ignore flg))
                     x)))))

(defun sort-rw-cache-list (lst)

; See the Essay on Rw-cache.

; Lst is an rw-cache-list.  We return a corresponding sorted list of
; rw-cache-entry records, without t as a member.

  (cond ((eq (car lst) t) (cdr lst))
        ((null (cdr lst)) lst)
        (t (mv-let (front back)
                   (split-psorted-list lst)
                   (mv-let (flg ans)
                           (combine-sorted-rw-cache-lists1
                            (merge-sort-lexorder-fast front)
                            back)
                           (declare (ignore flg))
                           ans)))))

(defun combine-rw-cache-lists (lst1 lst2)

; See the Essay on Rw-cache.

; Lst1 and lst2 are rw-cache-lists.  We return a suitable combination of the
; two, together with a flag which, when true, implies that the result is equal
; (in fact, eq) to lst2.

  (cond ((null lst1) (mv t lst2))
        ((null lst2) (mv nil lst1))
        ((eq (car lst2) t)
         (mv-let (flg ans)
                 (combine-sorted-rw-cache-lists1 (sort-rw-cache-list lst1)
                                                 (cdr lst2))
                 (cond (flg (mv t lst2))
                       (t (mv nil (cons t ans))))))
        (t (mv nil (cons t
                         (mv-let (flg ans)
                                 (combine-sorted-rw-cache-lists1
                                  (sort-rw-cache-list lst1)
                                  (sort-rw-cache-list lst2))
                                 (declare (ignore flg))
                                 ans))))))

(defun merge-rw-caches (alist1 alist2)

; Each of alist1 and alist2 is a symbol-alist sorted by car according to
; symbol<.  The value of each key is a sorted-rw-cache-list.  We return a
; symbol-alist, sorted that same way, such that each key's value is the
; suitable combination of its values in the two alists.  We avoid some consing
; by returning an additional value: a flag which, if true, implies that the
; result is equal (in fact, eq) to alist2.

  (cond ((endp alist1) (mv t alist2))
        ((endp alist2) (mv nil alist1))
        ((eq (caar alist1) (caar alist2))
         (mv-let (flg rest)
                 (merge-rw-caches (cdr alist1) (cdr alist2))
                 (mv-let (flg2 objs)
                         (combine-rw-cache-lists
                          (cdar alist1)
                          (cdar alist2))
                         (cond ((and flg flg2) (mv t alist2))
                               (flg2 (mv nil (cons (car alist2) rest)))
                               (t (mv nil (acons (caar alist2) objs rest)))))))
        ((symbol< (caar alist1) (caar alist2))
         (mv-let (flg rest)
                 (merge-rw-caches (cdr alist1) alist2)
                 (declare (ignore flg))
                 (mv nil (cons (car alist1) rest))))
        (t ; (symbol< (caar alist2) (caar alist1))
         (mv-let (flg rest)
                 (merge-rw-caches alist1 (cdr alist2))
                 (cond (flg (mv t alist2))
                       (t   (mv nil (cons (car alist2) rest))))))))

(defmacro sorted-rw-cache-p (cache)

; WARNING: This macro assumes that the given rw-cache is non-empty.

  `(eq (car ,cache) t))

(defun merge-symbol-alistp (a1 a2)
  (cond ((endp a1) a2)
        ((endp a2) a1)
        ((symbol< (caar a1) (caar a2))
         (cons (car a1)
               (merge-symbol-alistp (cdr a1) a2)))
        (t
         (cons (car a2)
               (merge-symbol-alistp a1 (cdr a2))))))

(defun merge-sort-symbol-alistp (alist)
  (cond ((endp (cdr alist)) alist)
        ((endp (cddr alist))
         (cond ((symbol< (car (car alist)) (car (cadr alist)))
                alist)
               (t (list (cadr alist) (car alist)))))
        (t (let* ((n (length alist))
                  (a (ash n -1)))
             (merge-symbol-alistp
              (merge-sort-symbol-alistp (take a alist))
              (merge-sort-symbol-alistp (nthcdr a alist)))))))

(defun cdr-sort-rw-cache (cache)

; We sort the given rw-cache.

  (assert$
   cache
   (cond ((sorted-rw-cache-p cache) (cdr cache))
         (t (mv-let (front back)
                    (split-psorted-list cache)
                    (mv-let (flg ans)
                            (merge-rw-caches (merge-sort-symbol-alistp front)
                                             back)
                            (declare (ignore flg))
                            ans))))))

(defun combine-rw-caches (c1 c2)

; See the Essay on Rw-cache.

; C1 and c2 are rw-caches, typically the respective values in two caches of
; either 'rw-cache-any-tag or 'rw-cache-nil-tag.  Thus, they are psorted
; symbol-alists.  We return a suitable combination of c1 and c2, together with
; a flag implying that the result is equal (in fact eq) to c2.

  (cond ((null c1) (mv t c2))
        ((null c2) (mv nil c1))
        (t (mv-let (flg x)
                   (merge-rw-caches (cdr-sort-rw-cache c1)
                                    (cdr-sort-rw-cache c2))
                   (cond ((and flg (sorted-rw-cache-p c2))
                          (mv t c2))
                         (t (mv nil (cons t x))))))))

(defun unify-subst-subsetp (a1 a2)

; Both a1 and a2 satisfy symbol-alistp.  We assume that if a1 is a subset of
; a2, then their keys occur in the same order.

  (cond ((endp a1) t)
        ((endp a2) nil)
        ((eq (caar a1) (caar a2))
         (and (equal (cdar a1) (cdar a2))
              (unify-subst-subsetp (cdr a1) (cdr a2))))
        (t (unify-subst-subsetp a1 (cdr a2)))))

(defun rw-cache-list-lookup (unify-subst hyps recs)
  (cond
   ((endp recs) nil)
   ((eq (car recs) t)
    (rw-cache-list-lookup unify-subst hyps (cdr recs)))
   ((let* ((rec (car recs))
           (failure-reason (access rw-cache-entry rec :failure-reason))
           (hyp-info (access rw-cache-entry rec :hyp-info)))
      (and
       (cond ((free-failure-p failure-reason)
              (and (equal hyps hyp-info)
                   (equal (access rw-cache-entry rec :unify-subst)
                          unify-subst)))
             (t (and (equal hyp-info

; We test the stored hypothesis against the corresponding current hypothesis
; because the same rune can correspond to several different rules.  Theorem
; mod-completion in community book arithmetic-2/floor-mod/floor-mod.lisp
; fails if we cache a failure for one rule stored under (:rewrite
; mod-completionxxx) and then decide not to fire the other rule because we come
; across the same unify-subst.

                            (nth (1- (car failure-reason)) hyps))
                     (unify-subst-subsetp (access rw-cache-entry rec
                                                  :unify-subst)
                                          unify-subst))))
           rec)))
   (t (rw-cache-list-lookup unify-subst hyps (cdr recs)))))

(defstub relieve-hyp-failure-entry-skip-p
  (rune unify-subst hyps ttree step-limit)
  t)

(defun relieve-hyp-failure-entry-skip-p-builtin (rune unify-subst hyps ttree
                                                      step-limit)
  (declare (ignore rune unify-subst hyps ttree step-limit)
           (xargs :mode :logic :guard t))
  nil)

(defattach (relieve-hyp-failure-entry-skip-p
            relieve-hyp-failure-entry-skip-p-builtin))

(defmacro rw-cache-active-p (rcnst)
  `(member-eq (access rewrite-constant ,rcnst :rw-cache-state)
              '(t :atom)))

(defun assoc-rw-cache (key alist)
  (cond ((endp alist) nil)
        ((eq (car alist) t)
         (assoc-eq key (cdr alist)))
        ((eql key (caar alist))
         (car alist))
        (t (assoc-rw-cache key (cdr alist)))))

(defun put-assoc-rw-cache1 (key val alist)

; Alist is a psorted-alist (see the Essay on Rw-cache) and key is a key of
; alist.  We return the result of replacing the value of key with val in alist.

  (cond ((atom alist) (list (cons key val)))
        ((eq (car alist) t)
         (cons (car alist)
               (put-assoc-eq key val (cdr alist))))
        ((eq key (caar alist)) (cons (cons key val) (cdr alist)))
        (t (cons (car alist) (put-assoc-rw-cache1 key val (cdr alist))))))

(defun put-assoc-rw-cache (key val alist)

; Alist is a psorted-alist (see the Essay on Rw-cache).  We return a
; psorted-alist that associates key with val.

  (cond ((assoc-rw-cache key alist)
         (put-assoc-rw-cache1 key val alist))
        (t (acons key val alist))))

(defun relieve-hyp-failure-entry (rune unify-subst hyps ttree step-limit)

; We return either nil or else an rw-cache-entry from the rw-cache of the
; ttree.

  (let* ((cache (tagged-objects 'rw-cache-any-tag ttree))
         (entry (and cache ; optimization
                     (rw-cache-list-lookup
                      unify-subst
                      hyps
                      (cdr (assoc-rw-cache (base-symbol rune) cache))))))

; We could do our check with relieve-hyp-failure-entry-skip-p before even
; looking up the entry, above.  Instead, we optimize for the common case that
; relieve-hyp-failure-entry-skip-p returns nil, hence only calling it when
; necessary.  This way, the user's attachment to
; relieve-hyp-failure-entry-skip-p could print (with cw or observation-cw, say)
; when an entry is found but skipped.

    (cond ((null entry) nil)
          ((relieve-hyp-failure-entry-skip-p rune unify-subst hyps ttree
                                             step-limit)
           nil)
          (t entry))))

(defun maybe-extend-tag-tree (tag vals ttree)

; Warning: We assume that tag is not a key of ttree.

  (cond ((null vals) ttree)
        (t (extend-tag-tree tag vals ttree))))

(defun accumulate-rw-cache1 (replace-p tag new-ttree old-ttree)

; This function is intended to return an extension of the rw-cache of old-ttree
; according to new-ttree, or else nil if the "extension" would not actually
; change old-ttree.  Below we describe more precisely what we mean by
; "extension", hence specifying the tag-tree returned in the non-nil case.

; If replace-p is true, then replace the caches tagged by the rw-cache tag in
; old-ttree with those tagged by tag in new-ttree, the expectation being that
; the value of tag in new-ttree extends its value in old-ttree.  If replace-p
; is false, then instead of replacing, combine the two caches.  In the case
; that replace-p is nil, performance may be best if the value of tag in
; new-ttree is more likely to be contained in its value in old-ttree, than the
; other way around (given our use below of combine-rw-caches).

  (let ((new-vals (tagged-objects tag new-ttree))
        (old-vals (tagged-objects tag old-ttree)))
    (cond
     ((and replace-p ; restrict optimization (else equality is unlikely)
           (equal new-vals old-vals))

; It's not clear to us whether this COND branch is helpful or harmful.  It can
; avoid modifying the tag-tree, but only to save at most a few conses, and at
; the cost of the above equality check.

      nil)
     (old-vals
      (cond
       (replace-p
        (assert$
         new-vals ; extends non-nil old-vals
         (extend-tag-tree tag
                          new-vals
                          (remove-tag-from-tag-tree! tag old-ttree))))
       (t (mv-let
           (flg objs)
           (combine-rw-caches new-vals old-vals)
           (assert$
            objs
            (cond (flg old-ttree)
                  (t (extend-tag-tree
                      tag
                      objs
                      (remove-tag-from-tag-tree! tag old-ttree)))))))))
     (new-vals (extend-tag-tree tag new-vals old-ttree))
     (t nil))))

(defun accumulate-rw-cache (replace-p new-ttree old-ttree)

; Keep this in sync with accumulate-rw-cache?, which is similar but may (and
; usually will) return nil if old-ttree is unchanged.

; New-ttree is an extension of old-ttree.  We incorporate the rw-cache from
; new-ttree into old-ttree, generally because new-ttree is to be discarded
; after a failure but we want to save its cached failures to relieve
; hypotheses.  If replace-p is true then we actually ignore the list of values
; of the relevant tags in old-ttree, assuming (and perhaps checking with an
; assert$) that this list forms a tail of the corresponding list of values in
; new-ttree.

  (let ((ttree1 (or (accumulate-rw-cache1 replace-p 'rw-cache-nil-tag
                                          new-ttree old-ttree)
                    old-ttree)))
    (or (accumulate-rw-cache1 replace-p 'rw-cache-any-tag new-ttree ttree1)
        ttree1)))

(defun accumulate-rw-cache? (replace-p new-ttree old-ttree)

; Keep this in sync with accumulate-rw-cache, which is similar; see comments
; there.  However, that function always returns a tag-tree, while the present
; function may (and usually will) return nil if old-ttree is unchanged.

  (let* ((ttree1-or-nil (accumulate-rw-cache1 replace-p 'rw-cache-nil-tag
                                              new-ttree old-ttree))
         (ttree1 (or ttree1-or-nil old-ttree))
         (ttree2-or-nil (accumulate-rw-cache1 replace-p 'rw-cache-any-tag
                                              new-ttree ttree1)))
    (or ttree2-or-nil
        ttree1-or-nil)))

(defun restrict-alist-to-all-vars1 (alist term)

; Return the result of restricting alist to those pairs whose key is a variable
; occurring free in term, together with a flag that, if nil, implies that the
; result is equal (in fact eq) to alist.

  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-termp term))))
  (cond ((endp alist) (mv nil nil))
        (t (mv-let (changedp rest)
                   (restrict-alist-to-all-vars1 (cdr alist) term)
                   (cond ((dumb-occur-var (caar alist) term)
                          (cond (changedp (mv t (cons (car alist) rest)))
                                (t (mv nil alist))))
                         (t (mv t rest)))))))

(mutual-recursion

(defun all-vars-boundp (term alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-alistp alist))))
  (cond ((variablep term)
         (assoc-eq term alist))
        ((fquotep term) t)
        (t (all-vars-lst-boundp (fargs term) alist))))

(defun all-vars-lst-boundp (lst alist)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (symbol-alistp alist))))
  (cond ((endp lst) t)
        (t (and (all-vars-boundp (car lst) alist)
                (all-vars-lst-boundp (cdr lst) alist)))))

)

(defun restrict-alist-to-all-vars (alist term)

; We return a subset of alist, with the order of elements unchanged.  In our
; intended application of this function, alist is a unify-subst obtained by
; matching the lhs of a rewrite-rule, and term is a hypothesis of that rule
; that has generated a failure reason other than a free-failure.  The return
; value is then intended to capture enough of the unify-subst such that for any
; extension of it encountered subsequently, we can reasonably expect the same
; hypothesis to fail again.

  (cond ((all-vars-boundp term alist)
         (mv-let (changedp result)
                 (restrict-alist-to-all-vars1 alist term)
                 (declare (ignore changedp))
                 result))
        (t

; This case can happen when we have a binding hypothesis.  If we pass in the
; list of all hypotheses in our intended application (see above), we could
; compute which variables bound by alist are really relevant to term.

         alist)))

(defun push-rw-cache-entry (entry tag rune ttree)

; Add entry, an rw-cache-entry record that corresponds to rune, to the records
; associated with tag (which is 'rw-cache-any-tag or 'rw-cache-nil-tag) in
; ttree.

  (let* ((cache (tagged-objects tag ttree))
         (base (base-symbol rune))
         (recs (and cache ; optimization
                    (cdr (assoc-rw-cache base cache)))))
    (cond ((null cache)
           (extend-tag-tree tag
                            (list (cons base (list entry)))
                            ttree))
          (t (extend-tag-tree
              tag
              (put-assoc-rw-cache
               base
               (cons entry recs)
               cache)
              (remove-tag-from-tag-tree tag ttree))))))

(defstub rw-cache-debug
  (rune target unify-subst relieve-hyp-failure-reason step-limit)
  t)

(defstub rw-cache-debug-action
  (rune target unify-subst relieve-hyp-failure-reason step-limit)
  t)

(defun rw-cache-debug-builtin (rune target unify-subst failure-reason
                                    step-limit)
  (declare (ignore rune target unify-subst failure-reason step-limit)
           (xargs :guard t))
  nil)

(defun rw-cache-debug-action-builtin (rune target unify-subst failure-reason
                                           step-limit)
  (declare (xargs :guard t))
  (cw "@@ rw-cache-debug:~|~x0~|"
      (list :step-limit step-limit
            :rune rune
            :target target
            :unify-subst unify-subst
            :relieve-hyp-failure-reason failure-reason)))

(encapsulate
 (((rw-cacheable-failure-reason *) => *
   :formals (failure-reason)
   :guard (and (consp failure-reason)
               (posp (car failure-reason)))))
 (logic)
 (local (defun rw-cacheable-failure-reason (failure-reason)
          failure-reason)))

(defun rw-cacheable-failure-reason-builtin (failure-reason)

; This function recognizes non-free-failure reasons.  The guard is important
; for note-relieve-hyp-failure, as noted in a comment in its definition.

  (declare (xargs :guard (and (consp failure-reason)
                              (posp (car failure-reason)))))
  (and (consp (cdr failure-reason))
       (member-eq (cadr failure-reason) '(rewrote-to syntaxp bind-free))))

(defattach (rw-cacheable-failure-reason rw-cacheable-failure-reason-builtin)
  :skip-checks t)

(defun rw-cacheable-nil-tag (failure-reason)

; Failure-reason is assumed to satisfy rw-cacheable-failure-reason.  We return
; true if it is a reason we want to put into the "nil" cache, i.e., one that we
; generally expect to remain suitable when we strengthen the original context
; of the failure.

  (and (consp (cdr failure-reason))
       (cond ((eq (cadr failure-reason) 'rewrote-to)
              (equal (cddr failure-reason) *nil*))
             (t
              (assert$ (member-eq (cadr failure-reason)
                                  '(syntaxp bind-free))

; Quoting :doc bind-free (and similarly for syntaxp): "every variable occurring
; freely in term occurs freely in lhs or in some hypi, i<n."  So the
; unify-subst for which we obtained this failure-reason will continue to yield
; this failure-reason in stronger contexts.

                       t)))))

(defun note-relieve-hyp-failure (rune unify-subst failure-reason ttree hyps
                                      step-limit)

; We return the given ttree but with its rw-cache possibly extended according
; to the indicated failure information.  See the Essay on Rw-cache.

; We considered checking (rw-cache-list-lookup rune unify-subst recs), where
; recs is the list of rw-cache-entry records that may be extended, before
; making any such extension.  However, our intended use of this function is
; only for situations where a relieve-hyps call fails after a cache miss.  So a
; cache hit here would mean that the same relieve-hyps call failed in the
; course of relieving the original hyps.  That seems sufficiently rare not to
; justify the cost of the lookup, since the penalty is just an occasional
; duplicate entry.  Indeed, using a preliminary version of our rw-cache
; implementation, we found no such cases in community books
; books/workshops/2004/legato/support/proof-by-generalization-mult.lisp,
; books/workshops/2004/smith-et-al/support/bags/eric-meta.lisp, or an
; "insert-proof" example sent to us by Dave Greve.

  (cond
   ((and failure-reason ; could be nil; see "save some conses" in relieve-hyps1
         (rw-cacheable-failure-reason failure-reason))

; Since failure-reason is non-nil, we expect (just as in the guard on
; rw-cacheable-failure-reason) that (consp failure-reason) and (posp (car
; failure-reason)).

    (let* ((hyp (nth (1- (car failure-reason)) hyps))
           (entry (make rw-cache-entry
                        :unify-subst
                        (restrict-alist-to-all-vars
                         unify-subst

; In the case of a synp hypothesis, our possible restriction of unify-subst is
; based on the variables occurring free in the term that is to be evaluated.

                         (cond ((ffn-symb-p hyp 'synp)
                                (let ((qterm (fargn hyp 3)))
                                  (cond ((quotep qterm)

; Probably qterm is always a quotep, but we prefer to be cautious here.

                                         (unquote qterm))
                                        (t hyp))))
                               (t hyp)))
                        :failure-reason failure-reason
                        :hyp-info hyp
                        :step-limit step-limit))
           (ttree
            (cond ((rw-cacheable-nil-tag failure-reason)
                   (push-rw-cache-entry entry 'rw-cache-nil-tag rune ttree))
                  (t ttree))))
      (push-rw-cache-entry entry 'rw-cache-any-tag rune ttree)))
   (t ttree)))

(defun replace-free-rw-cache-entry1 (unify-subst hyps entry recs)

; Recs is a psorted list of rw-cache-entry records.  If some record in recs
; whose :failure-reason satisfies free-failure-p has the given unify-subst and
; hyps fields, then we replace it by the given entry.

  (cond ((endp recs)
         (list entry))
        ((and (not (eq (car recs) t))
              (free-failure-p (access rw-cache-entry (car recs)
                                      :failure-reason))
              (equal unify-subst
                     (access rw-cache-entry (car recs) :unify-subst))
              (equal hyps
                     (access rw-cache-entry (car recs) :hyp-info)))
         (cons entry (cdr recs)))
        (t (cons (car recs)
                 (replace-free-rw-cache-entry1 unify-subst hyps entry
                                               (cdr recs))))))

(defun replace-free-rw-cache-entry (entry tag rune unify-subst hyps ttree)

; Some existing entry in the "any" or "nil" cache of ttree (depending on tag),
; stored under the base-symbol of rune as the key, may have the given
; unify-subst and hyps.  If so, we replace it with entry.  Otherwise, we simply
; extend the list of entries by adding that entry to those for the given
; base-symbol.

; The "Otherwise" case didn't occur for many years, so it is probably rare.  At
; one time we thought that such an entry always exists in recs.  However, an
; example arose in which that was not the case.  What happened was that
; relieve-hyps called note-relieve-hyps-failure-free, which passed in an "old"
; rw-cache entry obtained from the input ttree, yet another argument was a
; ttree (passed along to the present function) returned by a call of
; relieve-hyps1 that no longer had the unify-subst where one might expect.  As
; noted above, we handle this (rare) case simply by adding the new entry.
; We believe that this is sound, since soundness doesn't depend on the
; rw-cache, whose only function is to defeat the rewriter.

  (let* ((cache (tagged-objects tag ttree))
         (base (base-symbol rune))
         (recs (cdr (assoc-rw-cache base cache))))

; At one time we asserted here that recs is non-nil.  Perhaps that is a valid
; assertion, but given the comment above about changes in the ttree, we are no
; longer all that confident about it.  Since it seems harmless to to this
; extension when recs is nil, we no longer assert recs.

    (extend-tag-tree
     tag
     (put-assoc-rw-cache
      base
      (replace-free-rw-cache-entry1 unify-subst hyps entry recs)
      cache)
     (remove-tag-from-tag-tree tag ttree))))

(defun rw-cache-alist-nil-tag-p (alist)

; Alist is an rw-cache-alist, i.e., an alist mapping unify-substs to
; failure-reasons.  We return true when there is at least one normal-failure
; reason somewhere within one of these failure-reasons that could belong in a
; "nil" cache.

  (cond ((endp alist) nil)
        (t (or (let ((failure-reason (cdar alist)))
                 (cond ((free-failure-p failure-reason)
                        (rw-cache-alist-nil-tag-p (cdr failure-reason)))
                       (t (rw-cacheable-nil-tag failure-reason))))
               (rw-cache-alist-nil-tag-p (cdr alist))))))

(defabbrev merge-free-failure-reasons-nil-tag (r1 r2)

; R1 is a failure reason satisfying free-failure-p, as is r2 unless r2 is nil.
; This function is analogous to combine-free-failure-reasons, but where we are
; merging into r2 only those parts of r1 that are suitable for the "nil" cache.

  (mv-let (flg alist)
          (merge-free-failure-alists-nil-tag (cdr r1) (cdr r2))
          (cond (flg (mv t r2))
                (t (assert$
                    alist ; even if r2 is nil, flg implies alist is not nil
                    (mv nil (cons :RW-CACHE-ALIST alist)))))))

(defun merge-free-failure-alists-nil-tag (a1 a2)

; Each of the arguments is an rw-cache-alist.  We merge the part of a1 suitable
; for a "nil" cache into a2 to obtain an rw-cache-alist, alist.  We return (mv
; flg alist), where if flg is true then alist is a2.

; See also combine-free-failure-alists for a related function for the "any"
; cache.

  (cond
   ((endp a1) (mv t a2))
   (t
    (let* ((failure-reason (cdar a1))
           (free-p (free-failure-p failure-reason)))
      (cond
       ((and (not free-p)
             (not (rw-cacheable-nil-tag failure-reason)))
        (merge-free-failure-alists-nil-tag (cdr a1) a2))
       (t ; then first update a2 with (car a1)
        (mv-let
         (flg a2)
         (let ((pair (assoc-equal (caar a1) a2)))
           (cond
            ((and pair (not (free-failure-p (cdr pair))))
             (mv t a2))   ; keep normal-failure reason
            ((not free-p) ; then (rw-cacheable-nil-tag failure-reason)
             (mv nil
                 (cond (pair (put-assoc-equal (caar a1) failure-reason a2))
                       (t (acons (caar a1) failure-reason a2)))))
            (t
             (mv-let
              (flg2 sub-reason)
              (merge-free-failure-reasons-nil-tag failure-reason (cdr pair))
              (cond
               (flg2 (mv t a2))
               (pair (mv nil (put-assoc-equal (caar a1) sub-reason a2)))
               (t (mv nil (acons (caar a1) sub-reason a2))))))))
         (cond
          (flg (merge-free-failure-alists-nil-tag (cdr a1) a2))
          (t ; a2 has been updated, so returned flag must be nil
           (mv-let
            (flg alist)
            (merge-free-failure-alists-nil-tag (cdr a1) a2)
            (declare (ignore flg))
            (mv nil alist)))))))))))

(defun note-rw-cache-free-nil-tag (rune unify-subst hyps ttree
                                        new-rw-cache-alist step-limit)
  (cond
   ((rw-cache-alist-nil-tag-p new-rw-cache-alist)
    (let* ((cache (tagged-objects 'rw-cache-nil-tag ttree))
           (base (base-symbol rune))
           (recs (and cache ; optimization
                      (cdr (assoc-rw-cache base cache))))
           (entry (rw-cache-list-lookup unify-subst hyps recs))
           (failure-reason (and entry (access rw-cache-entry entry
                                              :failure-reason))))
      (cond
       ((and entry
             (not (free-failure-p failure-reason)))
        ttree) ; odd case; keep the old normal-failure reason
       (t
        (mv-let
         (flg alist)
         (merge-free-failure-alists-nil-tag new-rw-cache-alist
                                            (cdr failure-reason))
         (cond
          (flg ttree)
          (entry
           (replace-free-rw-cache-entry
            (change rw-cache-entry entry
                    :failure-reason (cons :RW-CACHE-ALIST alist))
            'rw-cache-nil-tag rune unify-subst hyps ttree))
          (t
           (let ((new-entry (make rw-cache-entry
                                  :unify-subst unify-subst
                                  :failure-reason (cons :RW-CACHE-ALIST alist)
                                  :hyp-info hyps
                                  :step-limit step-limit)))
             (cond
              ((null cache)
               (extend-tag-tree 'rw-cache-nil-tag
                                (list (cons base (list new-entry)))
                                ttree))
              ((null recs)
               (extend-tag-tree
                'rw-cache-nil-tag
                (acons ; put-assoc-rw-cache
                 base
                 (cons new-entry nil)
                 cache)
                (remove-tag-from-tag-tree 'rw-cache-nil-tag ttree)))
              (t
               (push-rw-cache-entry new-entry 'rw-cache-nil-tag rune
                                    ttree)))))))))))
   (t ttree)))

(defun note-relieve-hyps-failure-free (rune unify-subst hyps ttree old-entry
                                            old-rw-cache-alist
                                            new-rw-cache-alist step-limit)

; We update ttree by replacing the existing rw-cache-entry record for
; rune, unify-subst, and hyps, namely old-rw-cache-alist, by one that is based
; on new-rw-cache-alist.

  (assert$
   new-rw-cache-alist
   (mv-let
    (flg alist)
    (cond
     (old-rw-cache-alist
      (combine-free-failure-alists new-rw-cache-alist old-rw-cache-alist))
     (t (mv nil new-rw-cache-alist)))
    (cond
     (flg ; If the "any" cache is unchanged, then so is the "nil" cache.
      ttree)
     (t
      (let ((ttree (note-rw-cache-free-nil-tag rune unify-subst hyps ttree
                                               new-rw-cache-alist step-limit)))
        (cond
         (old-entry
          (replace-free-rw-cache-entry
           (change rw-cache-entry old-entry
                   :failure-reason (cons :RW-CACHE-ALIST alist))
           'rw-cache-any-tag rune unify-subst hyps ttree))
         (t
          (push-rw-cache-entry
           (make rw-cache-entry
                 :unify-subst unify-subst
                 :failure-reason (cons :RW-CACHE-ALIST alist)
                 :hyp-info hyps
                 :step-limit step-limit)
           'rw-cache-any-tag rune ttree)))))))))

(defun rw-cache-enter-context (ttree)

; Restrict the "any" cache to the "nil" cache.

  (maybe-extend-tag-tree 'rw-cache-any-tag
                         (tagged-objects 'rw-cache-nil-tag ttree)
                         (remove-tag-from-tag-tree 'rw-cache-any-tag ttree)))

(defun erase-rw-cache (ttree)

; Erase all rw-cache tagged objects from ttree.  See also
; erase-rw-cache-from-pspv.

  (remove-tag-from-tag-tree
   'rw-cache-nil-tag
   (remove-tag-from-tag-tree 'rw-cache-any-tag ttree)))

(defun rw-cache-exit-context (old-ttree new-ttree)

; Return the result of modifying new-ttree by restoring the "nil" cache from
; old-ttree and by combining the "any" caches of the two ttrees.

  (mv-let (flg new-any)
          (combine-rw-caches

; If we reverse the order of arguments just below, then in the case that flg is
; t, we could avoid modifying the "any" cache of new-ttree in the case that it
; contains the "any" cache of old-ttree.  However, since rw-cache-enter-context
; clears the "any" cache except for entries from the "nil" cache, it could be
; relatively rare for the "any" cache of new-ttree to have grown enough to
; contain that of old-ttree.  Indeed, we expect that in general new-ttree could
; have a much smaller "any" cache than that of old-ttree, in which case we may
; do less consing by combining new into old, which is what we do.

           (tagged-objects 'rw-cache-any-tag new-ttree)
           (tagged-objects 'rw-cache-any-tag old-ttree))
          (declare (ignore flg))
          (maybe-extend-tag-tree
           'rw-cache-any-tag
           new-any
           (maybe-extend-tag-tree
            'rw-cache-nil-tag
            (tagged-objects 'rw-cache-nil-tag old-ttree)
            (erase-rw-cache new-ttree)))))

(defun restore-rw-cache-any-tag (new-ttree old-ttree)

; New-ttree has an "any" cache that was constructed in a context we do not
; trust for further computation; for example, the fnstack may have extended the
; current fnstack.  We restore the "any" cache of new-ttree to that of
; old-ttree.  While we may be happy to preserve the "nil" cache of new-ttree,
; we have an invariant to maintain: the "nil" cache is always contained in the
; "any" cache.  In a preliminary implementation we kept these two caches
; separate, at the cost of maintaining a third "nil-saved" cache, which added
; complexity.  In the present implementation, we preserve the invariant by
; throwing away new "nil" cache entries.  Early experiments with the regression
; suite suggest that performance does not suffer significantly with such
; deletion.  But it would be interesting to experiment with the alternate
; approach of extending the old "any" cache with the new "nil" cache.

  (maybe-extend-tag-tree
   'rw-cache-any-tag
   (tagged-objects 'rw-cache-any-tag old-ttree)
   (maybe-extend-tag-tree
    'rw-cache-nil-tag
    (tagged-objects 'rw-cache-nil-tag old-ttree)
    (erase-rw-cache new-ttree))))

(defun cons-tag-trees-rw-cache (ttree1 ttree2)

; This is cons-tag-trees, but with normalized rw-caches in the result.  This
; function, as is probably the case for all rw-cache functions, is purely
; heuristic.  So, it is fine to call cons-tag-trees instead of this function.
; But we think that cons-tag-trees-rw-cache might sometimes produce better
; results, by avoiding duplicate keys (base-symbols of runes), since such
; duplicates would make the second occurrence of the key invisible to
; rw-cache-list-lookup.

; We avoid the expense of calling this function when we expect that at least
; one of the ttrees is lacking rw-cache tags, for example because it was
; produced by operations defined before the rewrite nest (such as type-set and
; assume-true-false).

  (let ((rw-cache-any1 (tagged-objects 'rw-cache-any-tag ttree1))
        (rw-cache-any2 (tagged-objects 'rw-cache-any-tag ttree2))
        (rw-cache-nil1 (tagged-objects 'rw-cache-nil-tag ttree1))
        (rw-cache-nil2 (tagged-objects 'rw-cache-nil-tag ttree2)))

; The code below could be simplified by using only the case that all four of
; the above caches are non-nil.  But since we know which ones are nil and which
; ones are not, we might as well use that information to save a bit of
; computation.

    (cond
     ((and rw-cache-any1 rw-cache-any2)
      (mv-let
       (flg-any cache-any)
       (combine-rw-caches rw-cache-any1 rw-cache-any2)
       (declare (ignore flg-any))
       (cond
        ((and rw-cache-nil1 rw-cache-nil2)
         (mv-let
          (flg-nil cache-nil)
          (combine-rw-caches rw-cache-nil1 rw-cache-nil2)
          (declare (ignore flg-nil))
          (extend-tag-tree
           'rw-cache-any-tag
           cache-any
           (extend-tag-tree
            'rw-cache-nil-tag
            cache-nil
            (cons-tag-trees (erase-rw-cache ttree1)
                            (erase-rw-cache ttree2))))))
        (t
         (extend-tag-tree
          'rw-cache-any-tag
          cache-any
          (cons-tag-trees (remove-tag-from-tag-tree
                           'rw-cache-any-tag
                           ttree1)
                          (remove-tag-from-tag-tree
                           'rw-cache-any-tag
                           ttree2)))))))
     ((and rw-cache-nil1 rw-cache-nil2)
      (mv-let
       (flg-nil cache-nil)
       (combine-rw-caches rw-cache-nil1 rw-cache-nil2)
       (declare (ignore flg-nil))
       (extend-tag-tree
        'rw-cache-nil-tag
        cache-nil
        (cons-tag-trees (remove-tag-from-tag-tree
                         'rw-cache-nil-tag
                         ttree1)
                        (remove-tag-from-tag-tree
                         'rw-cache-nil-tag
                         ttree2)))))
     (t (cons-tag-trees ttree1 ttree2)))))

(defun normalize-rw-any-cache (ttree)
  (let ((cache (tagged-objects 'rw-cache-any-tag ttree)))
    (cond ((or (null cache)
               (sorted-rw-cache-p cache))
           ttree)
          (t (extend-tag-tree
              'rw-cache-any-tag
              (cons t (cdr-sort-rw-cache cache))
              (remove-tag-from-tag-tree
               'rw-cache-any-tag
               ttree))))))

(defun cons-tag-trees-rw-cache-first (ttree1 ttree2)

; Combine the two tag-trees, except that the rw-cache of the result is taken
; solely from ttree1.

  (maybe-extend-tag-tree
   'rw-cache-any-tag
   (tagged-objects 'rw-cache-any-tag ttree1)
   (maybe-extend-tag-tree
    'rw-cache-nil-tag
    (tagged-objects 'rw-cache-nil-tag ttree1)
    (cons-tag-trees (erase-rw-cache ttree1)
                    (erase-rw-cache ttree2)))))

(defmacro tag-tree-tags-subsetp (ttree tags)

; Note: Tag-tree primitive

  `(alist-keys-subsetp ,ttree ,tags))

(defun rw-cache (ttree)

; Restrict ttree to its rw-cache tagged objects.

  (cond ((tag-tree-tags-subsetp ttree
                                '(rw-cache-nil-tag rw-cache-any-tag))
         ttree)
        (t (maybe-extend-tag-tree
            'rw-cache-any-tag
            (tagged-objects 'rw-cache-any-tag ttree)
            (maybe-extend-tag-tree
             'rw-cache-nil-tag
             (tagged-objects 'rw-cache-nil-tag ttree)
             nil)))))

(defun rw-cached-failure-pair (unify-subst rw-cache-alist)

; We assume that rw-cache-active-p holds for the current rewrite-constant.

; This function returns (mv cached-free-failure-reason
; cached-normal-failure-reason), where at most one of the two returned values
; is non-nil and as the names suggest: the second is a normal sort of
; failure-reason (as recognized by rw-cacheable-failure-reason), while the
; first is a failure-reason satisfying free-failure-p.

  (let* ((cached-failure-reason-raw
          (and rw-cache-alist ; cheap optimization for (perhaps) common case
               (cdr (assoc-equal unify-subst rw-cache-alist))))
         (cached-failure-reason-free-p
          (and (consp cached-failure-reason-raw)
               (free-failure-p cached-failure-reason-raw))))
    (mv (and cached-failure-reason-free-p
             cached-failure-reason-raw)
        (and (not cached-failure-reason-free-p)
             cached-failure-reason-raw))))

(defun extend-rw-cache-alist-free (rcnst new-unify-subst
                                         inferior-rw-cache-alist-new
                                         rw-cache-alist-new)

; This function ultimately supports the extension of an rw-cache in the
; free-failure case.  If the rw-cache is active (as per rcnst), then we extend
; rw-cache-alist-new by associating a non-nil inferior-rw-cache-alist-new, an
; rw-cache-alist (see the definition of record structure rw-cache-entry) with
; new-unify-subst (which we generally expect to have no such association in
; rw-cache-alist).  See also rw-cache-add-failure-reason, which extends
; new-unify-subst in the case of a normal-failure reason.

  (cond ((and inferior-rw-cache-alist-new
              (rw-cache-active-p rcnst))
         (put-assoc-equal new-unify-subst
                          (cons :RW-CACHE-ALIST
                                inferior-rw-cache-alist-new)
                          rw-cache-alist-new))
        (t rw-cache-alist-new)))

(defun rw-cache-add-failure-reason (rcnst new-unify-subst
                                          failure-reason
                                          rw-cache-alist-new)

; If the rw-cache is active (as per rcnst), then this function extends
; rw-cache-alist-new by associating failure-reason, a normal-failure reason,
; with new-unify-subst (which we generally expect to have no such association
; in rw-cache-alist).  See also extend-rw-cache-alist-free, which is analogous
; but for a free-failure reason.

  (cond ((and (rw-cache-active-p rcnst)
              failure-reason ; always true?
              (rw-cacheable-failure-reason failure-reason))
         (acons new-unify-subst
                failure-reason
                rw-cache-alist-new))
        (t rw-cache-alist-new)))

(defun add-linear-lemma-finish (concl force-flg rune rewritten-p
                                      term type-alist wrld state
                                      simplify-clause-pot-lst rcnst ttree)

; We return (mv contradictionp new-pot-lst failure-reason brr-result), where
; new-pot-lst can be new-pot-lst can be :null-lst when rewritten-p is true, to
; indicate that another try is coming.

  (let ((lst (linearize concl
                        t
                        type-alist
                        (access rewrite-constant rcnst
                                :current-enabled-structure)
                        force-flg
                        wrld
                        (push-lemma rune ttree)
                        state)))
    (cond
     ((and (null lst) rewritten-p) ; another try is coming
      (mv nil :null-lst 'irrelevant 'irrelevant))
     ((cdr lst)
      (mv nil
          simplify-clause-pot-lst
          (if rewritten-p
              'linearize-rewritten-produced-disjunction
            'linearize-unrewritten-produced-disjunction)
          nil))
     ((null lst)

; This case is an optimization of the final case.  We do not know if this case
; can actually occur, but even if not, it's a cheap check and it is nice to
; have in case it could occur in the future even if not now.

      (mv nil simplify-clause-pot-lst nil nil))
     ((new-and-ugly-linear-varsp
       (car lst)
       (<= *max-linear-pot-loop-stopper-value*
           (loop-stopper-value-of-var
            term
            simplify-clause-pot-lst))
       term)
      (mv nil simplify-clause-pot-lst 'linear-possible-loop nil))
     (t
      (mv-let
       (contradictionp new-pot-lst)
       (add-polys (car lst)
                  simplify-clause-pot-lst
                  (access rewrite-constant rcnst :pt)
                  (access rewrite-constant rcnst :nonlinearp)
                  type-alist
                  (access rewrite-constant rcnst
                          :current-enabled-structure)
                  force-flg
                  wrld)
       (cond
        (contradictionp (mv contradictionp nil nil (car lst)))
        (t (mv nil
               (set-loop-stopper-values
                (new-vars-in-pot-lst new-pot-lst
                                     simplify-clause-pot-lst
                                     nil)
                new-pot-lst
                term
                (loop-stopper-value-of-var
                 term simplify-clause-pot-lst))
               nil
               (car lst)))))))))

(defun make-stack-from-alist (term alist)

; We wish to make a stack representing alist, so that term/stack is
; term/alist.  The stack will consist of a single frame.  We used to
; do this with

; (if alist (list (cons (strip-cars alist) (strip-cdrs alist))) nil).

; But that was incorrect.  The free variables of term must be among
; the vars bound by the frame.  (That is, we must imagine that term is
; the body of a lambda expression whose formals are the vars of the
; frame.)  So if term contains a variable not bound in alist then we
; must capture that variable and bind it to itself.

  (if alist
      (let* ((vars-of-term (all-vars term))
             (formals (strip-cars alist))
             (actuals (strip-cdrs alist))
             (free (set-difference-eq vars-of-term formals)))
        (list (cons (append free formals)
                    (append free actuals))))
    nil))

; Here is how we create a lambda application.

(defun collect-by-position (sub-domain full-domain full-range)

; Full-domain and full-range are lists of the same length, where
; full-domain is a list of symbols.  Collect into a list those members
; of full-range that correspond (positionally) to members of
; full-domain that belong to sub-domain.

  (declare (xargs :guard (and (symbol-listp full-domain)
                              (true-listp sub-domain)
                              (true-listp full-range)
                              (eql (length full-domain)
                                   (length full-range)))))
  (if (endp full-domain)
      nil
    (if (member-eq (car full-domain) sub-domain)
        (cons (car full-range)
              (collect-by-position sub-domain
                                   (cdr full-domain)
                                   (cdr full-range)))
      (collect-by-position sub-domain
                           (cdr full-domain)
                           (cdr full-range)))))

(defun make-lambda-application (formals body actuals)

; Warning: If you consider making a call of this function, ask yourself whether
; make-lambda-term would be more appropriate; the answer depends on why you are
; calling this function.  In particular, the present function will drop an
; unused formal, but make-lambda-term does not (though its caller could choose
; to "hide" such a formal; see translate11-let).

; Example:
; (make-lambda-application '(x y z)
;                          '(foo x z)
;                          '((x1 a b) (y1 a b) (z1 a b)))
; equals
; ((lambda (x z) (foo x z)) (x1 a b) (z1 a b))
;
; Note that the irrelevant formal y has been eliminated.

  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-termp body)
                              (true-listp actuals)
                              (eql (length formals)
                                   (length actuals)))))
  (let ((vars (all-vars body)))
    (cond
     ((null vars)
      body)
     ((equal formals actuals)
      body)
     (t (let ((extra-vars (set-difference-eq vars formals)))

; The slightly tricky thing here is to avoid using all the formals, since some
; might be irrelevant.  Note that the call of intersection-eq below is
; necessary rather than just using vars, even though it is a no-op when viewed
; as a set operation (as opposed to a list operation), in order to preserve the
; order of the formals.

          (fcons-term (make-lambda (append? (intersection-eq formals vars)
                                            extra-vars)
                                   body)
                      (append? (collect-by-position vars formals actuals)
                               extra-vars)))))))

; The following two functions help us implement lambda-hide commuting,
; e.g., ((LAMBDA (x) (HIDE body)) arg) => (HIDE ((LAMBDA (x) body) arg)).

(defun lambda-nest-hidep (term)

; We return t iff term is a lambda nest with a HIDE as the inner-most
; body.  E.g.,
; (let ((st ...))
;   (let ((st ...))
;     (let ((st ...))
;       (HIDE ...))))

  (and (lambda-applicationp term)
       (let ((body (lambda-body (ffn-symb term))))
         (cond ((variablep body) nil)
               ((fquotep body) nil)
               ((eq (ffn-symb body) 'hide) t)
               (t (lambda-nest-hidep body))))))

(defun lambda-nest-unhide (term)

; We remove the HIDE from a lambda-nest-hidep term.

  (if (lambda-applicationp term)
      (make-lambda-application
       (lambda-formals (ffn-symb term))
       (lambda-nest-unhide (lambda-body (ffn-symb term)))
       (fargs term))
    (fargn term 1)))

(defabbrev memo-activep (memo)
  (or (eq memo :start) (consp memo)))

(defabbrev activate-memo (memo)
  (if (eq memo t) :start memo))

(defun intersection1-eq (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y)
                              (or (symbol-listp x)
                                  (symbol-listp y)))))
  (cond ((endp x) nil)
        ((member-eq (car x) y) (car x))
        (t (intersection1-eq (cdr x) y))))

(defun forbidden-fns-in-term (term forbidden-fns)
  (intersection-eq (all-fnnames term) forbidden-fns))

(defun forbidden-fns-in-term-list (lst forbidden-fns)
  (intersection-eq (all-fnnames-lst lst) forbidden-fns))

(defun all-fnnames-lst-lst1 (cl-lst acc)
  (cond ((endp cl-lst) acc)
        (t (all-fnnames-lst-lst1 (cdr cl-lst)
                                 (all-fnnames1 t (car cl-lst) acc)))))

(defun forbidden-fns-in-term-list-list (cl-lst forbidden-fns)
  (intersection-eq (all-fnnames-lst-lst1 cl-lst nil) forbidden-fns))

(defun forbidden-fns (wrld state)

; We compute a value of forbidden-fns using the values of globals
; 'untouchable-fns and 'temp-touchable-fns and constant *ttag-fns*.  We might
; expect it to be necessary be concerned about untouchable variables, perhaps
; simply forbidding calls of makunbound-global and put-global; but the event
; (def-glcp-interp-thm glcp-generic-interp-w-state-preserved ...) in community
; book books/centaur/gl/gl-generic-interp.lisp actually calls put-global.  But
; the live state won't be an argument to any function call in the generated
; clause, so this isn't a concern.

  (let* ((forbidden-fns0 (cond ((eq (f-get-global 'temp-touchable-fns state)
                                    t)
                                nil)
                               ((f-get-global 'temp-touchable-fns state)
                                (set-difference-eq
                                 (global-val 'untouchable-fns wrld)
                                 (f-get-global 'temp-touchable-fns state)))
                               (t (global-val 'untouchable-fns wrld)))))
    (reverse-strip-cars
     (and (not (ttag wrld))

; Although translate11 allows the use of *ttag-fns* during the boot-strap, we
; would be surprised to see such use.  So we save the cost of the following
; test, but note here that it is likely OK to uncomment this test.

;         (not (global-val 'boot-strap-flg wrld))
          *ttag-fns*)
     forbidden-fns0)))

(table skip-meta-termp-checks-table nil nil
       :guard
       (and (or (null val)
                (ttag world)
                (er hard 'skip-meta-termp-checks
                    "An active trust tag is required for setting ~x0 except ~
                     when clearing it."
                    'skip-meta-termp-checks-table))
            (eq key t)
            (or (eq val t)
                (symbol-listp val))))

(defmacro set-skip-meta-termp-checks! (x)
  (declare (xargs :guard (or (booleanp x)
                             (symbol-listp x))))
  `(table skip-meta-termp-checks-table t ',x))

(defmacro set-skip-meta-termp-checks (x)
  `(local (set-skip-meta-termp-checks! ,x)))

(defun skip-meta-termp-checks (fn wrld)
  (let ((val (cdr (assoc-eq t (table-alist 'skip-meta-termp-checks-table
                                           wrld)))))
    (or (eq val t)
        (and val ; optimization
             (member-eq fn val)))))

(defun collect-bad-fn-arity-info (alist wrld bad-arity-alist non-logic-fns)
  (cond
   ((endp alist)
    (if (or bad-arity-alist non-logic-fns)
        (cons (reverse bad-arity-alist) ; preserve original order
              non-logic-fns)
      nil))
   (t (let ((arity (arity (car (car alist)) wrld)))
        (collect-bad-fn-arity-info
         (cdr alist)
         wrld
         (if (or (null arity) ; handled below
                 (eql arity (cdr (car alist))))
             bad-arity-alist
           (cons (car alist) bad-arity-alist))
         (if (or (null arity)
                 (programp (car (car alist)) wrld))
             (cons (car (car alist))
                   non-logic-fns)
           non-logic-fns))))))

(defun bad-arities-msg (name token fn hyp-fn wf-thm-name1 wf-thm-name2
                             bad-arity-info)
  (msg
   "The ~s0 ~x1 has a now-invalid well-formedness guarantee.  Its ~s2, ~x3, ~
    ~#4~[was proved in ~x7 to return a ~x6~/and its corresponding hypothesis ~
    metafunction, ~x5, were proved in ~x7 and ~x8 to return ~x6s~] under the ~
    assumption that certain function symbols were in :logic mode and had ~
    certain arities.  But that assumption is now invalid, presumably because of ~
    redefinition.  ~@9We cannot trust the well-formedness guarantee."
   (if (eq token :META)
       "metatheorem"
     "clause-processor correctness theorem")
   name
   (if (eq token :META)
       (if fn
           "metafunction"
         "hypothesis metafunction")
     "clause-processor")
   (or fn hyp-fn)
   (if (and fn hyp-fn) 1 0)
   hyp-fn
   (if (eq token :META)
       'LOGIC-TERMP
     'LOGIC-TERM-LIST-LISTP)
   wf-thm-name1
   wf-thm-name2
   (let ((bad-arities-alist (car bad-arity-info))
         (non-logic-fns (cdr bad-arity-info)))
     (msg "~@0~@1"
          (if (null bad-arities-alist)
              ""
            (msg "The following alist pairs function symbols with their ~
                  assumed arities: ~X01.  Each symbol had the specified arity ~
                  when ~x2 was proved but this is no longer the case.  "
                 bad-arities-alist nil name))
          (if (null non-logic-fns)
              ""
            (msg "The symbol~#0~[ ~x0 is no longer a :logic mode function ~
                  symbol~/s ~&0 are no longer :logic mode function symbols~] ~
                  even though this was the case when ~x2 was proved.  "
                 non-logic-fns nil name))))))

; The following pair of macro definitions replaces function definitions that
; unnecessarily duplicated all-fnnames1 (and all-fnnames, all-fnnames-lst).
; This replacement doesn't perfectly preserve functionality, because the
; original versions below could return the list of function symbols in a
; different order than is returned by all-fnnames1 (and all-fnnames,
; all-fnnames-lst).  Perhaps we will eliminate these macros in the future.
(defmacro all-ffn-symbs (term ans)
  `(all-fnnames1 nil ,term ,ans))
(defmacro all-ffn-symbs-lst (lst ans)
  `(all-fnnames1 t ,lst ,ans))

(defun apply$-rule-name (fn)
  (declare (xargs :guard (symbolp fn)))
  (intern-in-package-of-symbol
   (coerce (append '(#\A #\P #\P #\L #\Y #\$ #\-)
                   (coerce (symbol-name fn) 'list))
           'string)
   fn))

(defun push-warrants (fns target type-alist ens wrld ok-to-force ttree ttree0)

; See the Essay on Evaluation of Apply$ and Loop$ Calls During Proofs.

; This function is called when *aokp* is nil and *warrant-reqs* is non-nil.

; Fns is a list of warranted function symbols, each an argument to
; apply$-userfn or badge-userfn during evaluation of target, which is the
; application of some function symbol to constants and may have subsidiary
; calls of apply$-userfn.  If ok-to-force is true, then we update ttree by
; forcing warrants that are not known, to justify the evaluation of target.
; Since one of the arguments is type-alist, we do not expect to call this
; function during preprocess-clause.  (This is reasonable since execution that
; is conditional on warrants isn't "simple", just as rules with hypotheses
; aren't simple.)

; We return (mv erp ttree), where if erp is nil then ttree extends the input
; ttree (which is initially ttree0) to justify that every symbol in fns has a
; warrant and to record the application of each rule APPLY$-fn.  This is a
; no-change loser: if erp is non-nil then the returned ttree is ttree0.  Note
; however that if ok-to-force is true, then erp will be nil.  If erp is
; non-nil, then the result depends on whether or not the apply$-rule-name is
; enabled.  If so, then erp is the function whose warrant is either false in
; the given context or else cannot be forced.  Otherwise, erp is a one-element
; list containing the apply$-rule-name.

; We overload ok-to-force just a bit.  At the top level it is Boolean.
; Otherwise, it can be :immediate or :force, meaning that it is ok to force
; (the top-level value of ok-to-force is t) and the mode is :immediate or not,
; respectively.

  (cond
   ((endp fns) (mv nil ttree))
   (t
    (let* ((fn (car fns))
           (warrant-name (warrant-name fn))
           (warrant (fcons-term* warrant-name))
           (apply$-rule-name (apply$-rule-name fn))
           (fn-apply$-rule (list :rewrite apply$-rule-name)))
      (assert$
       (and (function-symbolp warrant-name wrld)
            (logicp warrant-name wrld))
       (cond
        ((enabled-runep fn-apply$-rule ens wrld)
         (mv-let (knownp nilp ttree)
           (known-whether-nil warrant type-alist ens nil nil wrld ttree)
           (cond
            (knownp
             (cond
              ((not nilp)
               (push-warrants (cdr fns) target type-alist ens wrld ok-to-force
                              (push-lemma fn-apply$-rule ttree)
                              ttree0))
              (t

; The warrant is known to be false, which is presumably rare.  There is no
; point in trying to force the warrant, so we cause an error.

               (mv fn ttree0))))
            (ok-to-force
             (let* ((ok-to-force
                     (cond ((not (eq ok-to-force t))
                            ok-to-force)
; Else ok-to-force is t, and we convert it to :immediate or :force.
                           ((enabled-numep *immediate-force-modep-xnume*
                                           ens)
                            :immediate)
                           (t :force)))
                    (immediatep (eq ok-to-force :immediate)))
               (mv-let (force-flg ttree)
                 (force-assumption fn-apply$-rule target warrant type-alist nil
                                   immediatep t
                                   (push-lemma fn-apply$-rule ttree))
                 (declare (ignore force-flg)) ; still t
                 (push-warrants (cdr fns) target type-alist ens wrld ok-to-force
                                ttree ttree0))))
            (t ; Forcing is disallowed, so we cause an error.
             (mv fn ttree0)))))
        (t (mv (list apply$-rule-name) ttree0))))))))

(defconst *fake-rune-for-cert-data*
  '(:FAKE-RUNE-FOR-CERT-DATA nil))

(defconst *fake-rune-alist*

; We use this constant for dealing with fake runes in tag-trees.  We ignore
; *fake-rune-for-anonymous-enabled-rule*, because push-lemma is careful not to
; put it into any tag-trees.

  (list (cons (car *fake-rune-for-linear*)
              "linear arithmetic")
        (cons (car *fake-rune-for-type-set*)
              "primitive type reasoning")
        (cons (car *fake-rune-for-cert-data*)
              "previously-computed data")))

(defun merge-runes (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((rune-< (car l1) (car l2))
         (cons (car l1) (merge-runes (cdr l1) l2)))
        (t (cons (car l2) (merge-runes l1 (cdr l2))))))

(defun merge-sort-runes (l)
  (cond ((null (cdr l)) l)
        (t (merge-runes (merge-sort-runes (evens l))
                        (merge-sort-runes (odds l))))))

(defun fn-slot-from-geneqvp (geneqv)
  (cond ((endp geneqv) nil)
        ((eq 'fn-equal (access congruence-rule (car geneqv) :equiv))
         t)
        (t (fn-slot-from-geneqvp (cdr geneqv)))))

(defun partition-userfns-by-warrantp (fns wrld haves have-nots)

; Background: Rewrite-lambda-object, defined in the rewrite clique below, tries
; to rewrite the body of a well-formed quoted lambda object.  But it must first
; make sure that every function symbol occurring in the body either has a
; warrant or doesn't need one (by virtue of being an apply$ primitive or boot
; function).  If all the fns that need a warrant have one, it rewrites the body
; and then forces all the warrants that aren't among the hyps.  But if there
; are fns that don't even have warrants, it doesn't rewrite at all and, at
; most, prints a warning message that the lambda can't be rewritten for that
; reason.  So rewrite-lambda-object needs the list of all fns in the body that
; must have warrants to be apply$d and it needs the list of all fns in the body
; that don't have warrants.  (Note that the question of whether the required
; warrants are assumed true in the context is left unasked here.)

; So let fns be the list of all function symbols occurring the body, then this
; function ``partitions'' fns into those having warrants and those not having
; warrants but requiring them.  We quote ``partitions'' because apply$ primitives
; and apply$ boot functions are just left out all together!

  (cond ((endp fns) (mv haves have-nots))
        ((or
; The following hons-get is equivalent to (apply$-primp (car fns)).
          (hons-get (car fns) ; *badge-prim-falist* is not yet defined!
                    (unquote
                     (getpropc '*badge-prim-falist*
                               'const nil wrld)))
; We similarly inspect the value of *apply$-boot-fns-badge-alist*
          (assoc-eq (car fns)
                    (unquote
                     (getpropc '*apply$-boot-fns-badge-alist*
                               'const nil wrld))))
         (partition-userfns-by-warrantp (cdr fns) wrld haves have-nots))
        ((get-warrantp (car fns) wrld)
         (partition-userfns-by-warrantp (cdr fns) wrld
                                        (add-to-set-eq (car fns) haves)
                                        have-nots))
        (t
         (partition-userfns-by-warrantp (cdr fns) wrld
                                        haves
                                        (add-to-set-eq (car fns) have-nots)))))

(defun rewrite-lambda-object-pre-warning
    (evg not-well-formedp progs pre-have-no-warrants wrld)

; Evg is a lambda object whose body we did not even try to rewrite.  We explain
; why.  Not-well-formedp = t means that evg is not well-formed.  Otherwise,
; progs is the list of :program mode function symbols in the body and
; pre-have-no-warrants is the list of function symbols in the body for which no
; warrants have been issued but would require warrants for apply$ to handle
; them.  We print a rather verbose warning.  This warning can be avoided by
; doing (set-inhibit-warnings "rewrite-lambda-object").

; Note: Wrld is used in the expansion of warning$-cw1.

; Historical Note: Rewrite-lambda-object-pre-warning and
; rewrite-lambda-object-post-warning are sort of parallel, one reporting why we
; avoided rewriting and the other reporting why we rejected the rewrite we did.
; But they are structured somewhat differently for mainly historical reasons.
; The post-warning was done first and no explanation was ever offered for the
; not trying rewriting.  The pre-warning was added only after :program mode
; functions could find their way into well-formed lambdas.  The post-warning
; takes pains to warn the user about combinations of conditions while the
; pre-warning just warns of the first problem detected.  The post-warning
; recomputes the reasons even though the caller, rewrite-lambda-object,
; ``knew'' them, whereas the pre-warning is passed the information it needs to
; avoid recomputation.  These differences are largely just due to laziness!

  (let* ((violations
          (if not-well-formedp
              0
              (if progs
                  1
                  (if pre-have-no-warrants
                      2
                      3)))))
; violations =
; 0 - not well-formed
; 1 - one or more :program mode functions in body
; 2 - one or more symbols without warrants
; 3 - unknown reason for rejection

    (let ((state-vars (default-state-vars nil)))
      (warning$-cw1 'rewrite-lambda-object
                    "rewrite-lambda-object"
                    "We refused to try to rewrite the quoted lambda-like ~
                     object~%~Y01 because ~#2~[it is not well-formed (e.g., ~
                     contains free variables, has a body that is not a term, ~
                     or that contains unbadged function symbols)~/it contains ~
                     the :program mode function symbol~#3~[~/s~] ~&3~/it ~
                     contains the function symbol~#4~[~/s~] ~&4 for which no ~
                     warrant~#4~[ has~/s have~] been issued~/we didn't like ~
                     it but failed to record why~].  See :DOC ~
                     rewrite-lambda-object."
                    evg
                    nil
                    violations
                    progs
                    pre-have-no-warrants))))

(defun rewrite-lambda-object-post-warning
    (evg rewritten-body post-have-no-warrants ttree wrld)

; Evg is a well-formed quoted lambda object whose body has been rewritten to
; rewritten-body using the runes in ttree.  Post-have-no-warrants is the list
; of function symbols (if any) in rewritten-body for which no warrants have
; been issued.  However, rewritten-body has been rejected for various reasons.
; We print a rather verbose warning explaining why.  This warning can be
; avoided by doing (set-inhibit-warnings "rewrite-lambda-object").

; Historical Note: See the note in rewrite-lambda-object-pre-warning about the
; differing styles of this function and its pre-warning version.

  (let* ((free-vars (set-difference-eq (all-vars rewritten-body)
                                       (lambda-object-formals evg)))
         (untamep (not (executable-tamep rewritten-body wrld)))
         (violations
          (if free-vars
              (if (cdr free-vars)
                  (if untamep 0 1)
                  (if untamep 2 3))
              (if untamep
                  4
                  (if post-have-no-warrants 5 6)))))
; violations =
; 0 - multiple free vars and untame
; 1 - multiple free vars [but tame]
; 2 - a single free var and untame
; 3 - a single free var [but tame]
; 4 - [no free vars] untame
; 5 - [no free vars and tame] but some fns have no warrants
; 6 - [no free vars, tame, fully warranted] some warrant assumed false

    (let ((state-vars (default-state-vars nil)))
      (warning$-cw1 'rewrite-lambda-object
                    "rewrite-lambda-object"
                    "The body of the well-formed (and tame) lambda ~
                     object~%~Y01rewrote to~%~Y21which was rejected because ~
                     ~#3~[it contains the variables ~&4 not listed among the ~
                     formals, and it is not tame~/it contains the variables ~
                     ~&4 not listed among the formals~/it contains the ~
                     variable ~&4 not listed among the formals, and it is not ~
                     tame~/it contains the variable ~&4 not listed among the ~
                     formals~/it is not tame~/it contains the function ~
                     symbol~#5~[ ~&5 for which no warrant has~/s ~&5 for ~
                     which no warrants have~] been issued~/some warrant is assumed false ~
                     in the current prover environment~].  The following runes were ~
                     used to produce this rejected object: ~X61.  See :DOC ~
                     rewrite-lambda-object."
                    evg            ; lambda object
                    nil            ; evisc tuple -- print everything
                    `(lambda ,(lambda-object-formals evg)
                       ,rewritten-body) ; rejected body
                    violations     ; 0, 1, 2, 3, 4, 5, or 6
                    free-vars
                    post-have-no-warrants
                    (merge-sort-runes (all-runes-in-ttree ttree nil))))))

(defun collect-0-ary-hyps (type-alist)

; This function returns a type-alist to be used while rewriting the body of a
; quoted lambda object.  We collect every triple in type-alist that assigns a
; type-set to a call of a 0-ary function.  We are actually interested only in
; warrant hypotheses, but there is no harm in collecting other variable-free
; assumptions.  We could even collect the bindings for terms not sharing any
; variables with the locals of the target lambda object, but that might invite
; the introduction of an unbound free var into the rewritten body.  For
; example, the type-alist might include the assumption of (INTEGERP I) and
; while the lambda object formals are just LOOP$-GVARS and LOOP$-IVARS.  But if
; a rewrite rule has a free variable to be assigned by finding some integer,
; the inclusion of this (INTEGERP I) hyp might cause the rewritten body to
; mention I, which would invalidate the lambda body and cause the entire
; rewrite to be abandoned.  So we just don't ``import'' anything but
; variable-free assumptions at the moment.

  (cond ((endp type-alist) nil)
        ((and (consp (car (car type-alist)))
              (null (cdr (car (car type-alist)))))
         (cons (car type-alist)
               (collect-0-ary-hyps (cdr type-alist))))
        (t (collect-0-ary-hyps (cdr type-alist)))))

; Essay on Rewriting Quoted Constants

; ACL2 (and Nqthm before it) never rewrote quoted constants.  In the days
; before user-defined equivalence relations there was no point, since no two
; distinct quoted constants are EQUAL.  (The special handling of IFF slots is
; the exception that proves the utility of the idea, as illustrated below.)
; However, with user-defined equivalences, it is conceivable that two distinct
; (mod EQUAL) constants are equivalent and that one is preferred over the
; other.  It is sort of surprising that ACL2 has supported user-defined
; equivalence and congruence based rewriting for 15 years or so without
; identifying this little weakness in its rewriter.

; For example,

; Example A: one might wish to replace '23 by 'T in a slot where IFF is being
;            maintained.

; Example B: one might wish to replace '(C A B A . 77) by '(A B C) in a slot
;            where SET-EQUALP is being maintained.

; Example C: one might wish to replace '(LAMBDA (X) X) by 'IDENTITY in a slot
;            where FN-EQUAL is being maintained.

; Such replacements cannot be done now because ACL2 won't apply a rewrite rule
; to a quoted constant.  (One can phrase rewrite rules that operate on the
; parent term containing the constant, e.g., if foo is a function that admits
; IFF as as a congruence in its first argument, one might prove (equal (foo 23
; lst) (foo t lst)).  Another such example would be:

; (set-equal (set-union '(C A B A . 77) u)
;            (set-union '(A B C) u))

; but this workaround is unsatisfactory because one needs such a rule for each
; function admitting the equivalence relation as a congruence.  We suspect that
; the reason this weakness in the rewriter was never identified is that user's
; employed this workaround on an as-needed basis.

; To facilitate the rewriting of quoted constants we will add a new rule-class,
; :rewrite-quoted-constant, and a new world global called
; rewrite-quoted-constant-rules which is just a list of ordinary :rewrite rule
; records (but tagged :rewrite-quoted-constant in the :subclass), each of which
; is derived from a corollary of one of these three forms:

; [1] (IMPLIES hyps (equiv 'lhs-evg 'rhs-evg))
; [2] (IMPLIES hyps (equiv (fn x) x)), where x is a variable.
; [3] (IMPLIES hyps (equiv lhs-term rhs-term))

; We now explain how such rules are used.  When the rewriter encounters (QUOTE
; target-evg), it will scan down rewrite-quoted-constant-rules processing each
; rule in turn until it finds the first ``applicable'' rule.  Then it does the
; ``replacement'' described below.

; A rule is ``applicable'' exactly in the sense that an ordinary :rewrite rule
; is, except for how we match the lhs of the rule with the target.  In
; particular, to be applicable the rule must be enabled, the equiv of the rule
; must refine the equiv being maintained by the rewriter, the lhs of the rule
; must ``match'' the target-evg as described below, and the hyps must be
; relieved, etc.  In addition, for a form [2] rule to be applicable, the
; executable counterpart of the fn named in the rule must be enabled.

; The notion of ``match'' for evgs is a bit strange:
;  - a form [1] rule matches when lhs-evg is exactly target-evg.
;  - a form [2] rule matches any target-evg!
;  - a form [3] rule matches if its lhs one-way-unifies with (QUOTE target-evg).

; The ``replacement'' directed by an applicable rule is as follows:
;  - a form [1] rule replaces the target-evg by the rhs-evg
;  - a form [2] rule replaces the target-evg by the (non-erroneous) result of
;    calling the executable counterpart of fn on the target-evg.
;  - a form [3] rule replaces (QUOTE target-evg) by the (rewritten) instantiated
;    rhs-term.

; Notice that the replacement performed by a form [3] rule might not yield a
; quoted constant, but that's ok.

; Rewrite rules generally have a loop-stopper entry in the :heuristic-info
; field of the record.  In the case of rewrite-quoted-constant rules -- which
; are in fact represented by rewrite-rule records but stored in the
; rewrite-quoted-constant-rules global variable -- the :heuristic-info is (n
; . loop-stopper), where n is the form number.  Rules of form [1] and [2] can't
; actually have non-nil loop-stoppers because the variables mentioned in the
; loop-stopper must be distinct and occur in both the lhs and rhs.  But we go
; ahead and compute and store the (usually nil) loop-stopper.

; Worked Examples:

; Here are :rewrite-quoted-constant rules for addressing Examples A, B, and C
; above.  We also add an Example D that illustrates why some Form [1] rules
; might require hypotheses even though the conclusion of a Form [1] rule is a
; ground term.

; Example A: one might wish to replace '23 by 'T in a slot where IFF is being
;            maintained.

; Solution:
; (IFF '23 'T)                                     ; Form [1]
; or, more generally,
; (IMPLIES (AND X (SYNTAXP (NOT (EQUAL X ''NIL)))) ; Form [3]
;          (IFF X 'T))

; The Form [3] rule shown above illustrates why :rewrite-quoted-constant rules
; can't be easily stored as normal :rewrite rules, i.e., on the lemmas property
; of the top function symbol of the lhs.  Here there is no ``top function
; symbol.''

; Example B: one might wish to replace '(C A B A . 77) by '(A B C) in a slot
;            where SET-EQUALP is being maintained.

; Solution:
; (SET-EQUALP (NORMALIZE-SET X) X)                 ; Form [2]

; where NORMALIZE-SET is a function that coerces a non-true-list to a
; true-list, removes duplicates, and sorts a list.  Of course, this example
; could also be coded as the Form [1] rule (SET-EQUALP '(C A B A . 77) '(A B
; C)).  But that raises the question: does it work recursively down the
; cdr-chain of a set?  For example, would the user expect the Form [1] rule to
; replace '(D C A B A . 77) by '(D A B C)?  After all, the lhs-evg does occur
; in a SET-EQUALP slot of the target-evg.  But we decided Form [1] rules will
; only hit at the top-level so that the regression isn't slowed down by them
; when large quoted constants arise.  If you want to sweep the target-evg for
; opportunities, use a Form [2] rule and code the sweep yourself.  Form [2]
; rules are like metafunctions, but only apply to quoted constant terms and so
; the Form [2] rule itself is all you need to prove to effect the
; transformation.

; Example C: one might wish to replace '(LAMBDA (X) X) by 'IDENTITY in a slot
;            where FN-EQUAL is being maintained.
; Solution:
; (FN-EQUAL '(LAMBDA (X) X) 'IDENTITY)             ; Form [1]
; or more generally
; (IMPLIES (SYMBOLP V)                             ; Form [3]
;          (FN-EQUAL (LIST 'LAMBDA (LIST V) V)
;                    'IDENTITY))

; Example D: one might wish to replace '(LAMBDA (X) (FOO X)) by
;            '(LAMBDA (X) (BAR X)) in a slot where FN-EQUAL is
;            being maintained.

; Solution:
; (IMPLIES (WARRANT FOO BAR)                      ; Form [1]
;          (FN-EQUAL '(LAMBDA (X) (FOO X))
;                    '(LAMBDA (X) (BAR X))))
; This illustrates how the equivalence of two quoted constants might
; require a hypothesis.

(mutual-recursion

; State is an argument of rewrite only to permit us to call ev.  In general,
; wrld may be an extension of (f-get-global 'current-acl2-world state), but we
; use state only to pass it down to ev.

; Keep this nest in sync with mfc-rw+ and pc-rewrite*.

(defun rewrite (term alist bkptr ; &extra formals
                     rdepth step-limit
                     type-alist obj geneqv pequiv-info wrld state fnstack
                     ancestors backchain-limit
                     simplify-clause-pot-lst rcnst gstack ttree)

; Comments on the function REWRITE

; The Input
; c term:        the "matrix" term we are to rewrite.
; c alist:       a substitution we are to apply to term before rewriting it.
; h type-alist:  a list of assumptions governing this rewrite
;   obj:         (objective of rewrite) t, nil, or ? - of heuristic use only.
; c geneqv:      a generated equivalence relation to maintain
; c pequiv-info: info on patterned equivalence relations (pequivs) to maintain
;   wrld:        the current world
;   fnstack:     fns and terms currently being expanded - of heuristic use only
; h ancestors:   a list of terms assumed true, modified as we backchain.
; h backchain-limit: of heuristic use only
; h simplify-clause-pot-lst: a pot-lst of polys
; h rcnst:       the rewrite constant arguments
; h ttree:       the evolving ttree describing the rewrites.
;   rdepth:      maximum allowed stack depth - of heuristic use only
;   step-limit:  number of recursive calls permitted for rewrite

; The Output:
; a new step-limit, a term term', and a tag-tree ttree'

; The Specification of Rewrite: The axioms in wrld permit us to infer that the
; Rewrite Assumption implies that term' is equivalent via geneqv+pequiv-info to
; term/alist.  One can write this "wrld |- h -> c."  The args are tagged with h
; and c according to how they are involved in this spec.

; The Rewrite Assumption: the conjunction of (a) the assumptions in type-alist,
; (b) the assumptions in ancestors, (c) the assumption of every "active" poly
; in simplify-clause-pot-lst (where a poly is inactive iff its tag-tree
; contains a 'pt containing some literal number that occurs in the :pt field of
; rcnst), and (d) the 'assumptions in the final tag-tree ttree'.

; Observe that if there are 'assumptions in the incoming ttree they are unioned
; into those made by this rewrite.  Thus, unless you want the assumptions to
; accumulate across many rewrites, you must use the empty initial tag-tree.  It
; would be incorrect to attempt to split on the "new" assumptions in the new
; tag-tree because of the unioning.

; The first value is the rewritten term.  The second is the final
; value of ttree.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   3
   (signed-byte 30)
   (let ((gstack (push-gframe 'rewrite bkptr term alist obj))
         (rdepth (adjust-rdepth rdepth)))
     (declare (type (unsigned-byte 29) rdepth))
     (cond
      ((zero-depthp rdepth)
       (rdepth-error
        (mv step-limit (sublis-var alist term) ttree)))
      ((time-limit5-reached-p
        "Out of time in the rewriter (rewrite).") ; nil, or throws
       (mv step-limit nil nil))
      ((variablep term)
       (rewrite-entry
        (rewrite-solidify-plus (let ((temp (assoc-eq term alist)))
                                 (cond (temp (cdr temp))
                                       (t term))))))
      ((fquotep term)
       (rewrite-entry
        (rewrite-quoted-constant term)))
      ((eq (ffn-symb term) 'if)

; Normally we rewrite (IF a b c) by rewriting a and then one or both
; of b and c, depending on the rewritten a.  But in the special case
; (IF a b b) we just rewrite and return b.  We have seen examples
; where this comes up, e.g., before nth-update-rewriter was removed in
; Version_7.0, it could produce such IFs.

       (cond
        ((equal (fargn term 2) (fargn term 3))
         (rewrite-entry
          (rewrite (fargn term 2) alist 2)))
        (t
         (sl-let (rewritten-test ttree)
                 (rewrite-entry
                  (rewrite (fargn term 1) alist 1)

; When we rewrite the test of the if we use geneqv iff.  What about
; obj.  Mostly we'll use '?.  But there are a few special cases.
; Suppose you are rewriting (if t1 'nil 't) with the objective t.
; Then you should rewrite t1 with the objective nil.  This actually
; comes up in the handling of (<= x y).  That term opens to (if (< y
; x) 'nil 't).  If we had an obj of t initially, and we don't look
; into the if to see which way the branches go, then we rewrite the (<
; y x) with obj '? and miss an opportunity to use linear arithmetic.

; After Version_3.2.1 we added some more special cases.  Consider the
; following example supplied by Robert Krug.

;    (defstub quux (x) t)
;
;    (defaxiom quux-thm-1
;      (<= x (quux x))
;      :rule-classes :linear)
;
;    (defaxiom quux-thm-2
;      (integerp (quux x)))
;
;    ; Good
;
;    (defstub foo-1 (x) t)
;
;    (defun bar-1 (x)
;      (or (not (integerp x))
;          (< 4 x)))
;
;    (defaxiom foo-1-thm
;      (implies (bar-1 (quux x))
;               (foo-1 x)))
;
;    (thm  ; good
;     (implies (and (integerp x)
;                   (integerp y)
;                   (< 2 x)
;                   (< 2 y))
;              (foo-1 (+ x y))))

; Robert pointed out that if instead we switched the order of
; disjuncts in bar-1, the thm fails: (< 4 x) has moved to a test
; position and we had only passed a t or nil :obj down to the true and
; false branches.

;    (defstub foo-2 (x) t)
;
;    (defun bar-2 (x)
;      (or (< 4 x)
;          (not (integerp x))))
;
;    (defaxiom foo-2-thm
;      (implies (bar-2 (quux x))
;               (foo-2 x)))
;
;    (thm  ; bad
;     (implies (and (integerp x)
;                   (integerp y)
;                   (< 2 x)
;                   (< 2 y))
;              (foo-2 (+ x y))))

; Our goal, then, is to recognize the symmetry of OR, AND, and the
; like.  But if we do that naively then we miss the proof of the thm
; in the following case, because (or u v) expands to (if u u v) rather than to
; (if u t v).

;    (defstub foo-3 (x) t)
;
;    (defstub bar-3 (x) t)
;
;    (defaxiom bar-3-open
;      (equal (bar-3 x)
;             (or (< 4 x)
;                 (foo-3 (append x x)) ; optional extra challenge, since this
;                                      ; doesn't rewrite to a constant
;                 (not (integerp x)))))
;
;    (defaxiom foo-3-thm
;      (implies (bar-3 (quux x))
;               (foo-3 x)))
;
;    (thm  ; bad
;     (implies (and (integerp x)
;                   (integerp y)
;                   (< 2 x)
;                   (< 2 y))
;              (foo-3 (+ x y))))

; Therefore, we treat (if u u v) the same as (if u t v) for purposes
; of establishing the :obj.

                  :obj
                  (cond
                   ((eq obj '?) '?)
                   (t (let ((arg2 (if (equal (fargn term 1)
                                             (fargn term 2))
                                      *t*
                                    (fargn term 2))))
                        (cond ((quotep arg2)

; Since (if u  t  v) is essentially (or u v), :obj is same for u and v
; Since (if u nil v) is essentially (and (not u) v), :obj flips for u and v

                               (if (unquote arg2) obj (not obj)))
                              (t (let ((arg3 (fargn term 3)))
                                   (cond ((quotep arg3)

; Since (if u v  t ) is essentially (or (not u) v), :obj flips for u and v
; Since (if u v nil) is essentially (and u v), :obj is same for u and v

                                          (if (unquote arg3) (not obj) obj))
                                         (t '?))))))))
                  :geneqv *geneqv-iff*
                  :pequiv-info nil)
                 (rewrite-entry (rewrite-if rewritten-test
                                            (fargn term 1)
                                            (fargn term 2)
                                            (fargn term 3)
                                            alist))))))
      ((and (eq (ffn-symb term) 'return-last)

; We avoid special treatment for a return-last term when the first argument is
; 'progn, since the user may have intended the first argument to be rewritten
; in that case; consider for example (prog2$ (cw ...) ...).  But it is useful
; in the other cases, in particular for calls of return-last generated by calls
; of mbe, to avoid spending time rewriting the next-to-last argument.

            (not (equal (fargn term 1) ''progn)))
       (rewrite-entry
        (rewrite (fargn term 3) alist 2)
        :ttree (push-lemma
                (fn-rune-nume 'return-last nil nil wrld)
                ttree)))
      ((eq (ffn-symb term) 'hide)

; We are rewriting (HIDE x).  Recall the substitution alist.  We must
; stuff it into x.  That is, if the term is (HIDE (fn u v)) and alist
; is ((u . a) (v . b)), then we must return something equal to (HIDE
; (fn a b)).  We used to sublis-var the alist into the term.  But that
; may duplicate large terms.  So as of Version  2.6 we actually create
; (HIDE ((lambda (u v) x) a b)) or, equivalently, (HIDE (LET ((u a) (v
; b)) x)).

; Care must be taken to ensure that there are no free vars in the
; lambda.  We therefore use make-stack-from-alist to create a stack.
; This stack contains (at most) a single frame consisting of the
; appropriate formals and actuals.

; Also recall :EXPAND hints.  We must check whether we have been told
; to expand this guy.  But which guy?  (HIDE (fn a b)) or (HIDE (LET
; ((u a) (v b)) x))?  We actually ask about the latter because the
; former may be prohibitive to compute.  The fact that HIDEs are
; changed a little may make it awkward for the user to formulate
; :EXPAND or HIDE-rewrite hints without waiting to see what comes out.


       (let* ((stack (make-stack-from-alist (fargn term 1) alist))
              (inst-term (if alist
                             (fcons-term* 'hide
                                          (make-lambda-application
                                           (caar stack)
                                           (fargn term 1)
                                           (cdar stack)))
                           term))
              (new-rcnst (expand-permission-p inst-term rcnst geneqv
                                              wrld)))
         (cond
          (new-rcnst

; We abandon inst-term and rewrite the hidden part under the alist.

           (rewrite-entry (rewrite (fargn term 1) alist 1)
                          :ttree (push-lemma
                                  (fn-rune-nume 'hide nil nil wrld)
                                  ttree)
                          :rcnst new-rcnst))
          (t (rewrite-entry
              (rewrite-with-lemmas inst-term))))))
      ((lambda-nest-hidep term)

; This clause of rewrite implements ``lambda-hide commuting''.  The
; idea is that ((LAMBDA (x) (HIDE body)) actual) can be rewritten to
; (HIDE ((LAMBDA (x) body) actual)).  But, as above, we must be
; careful with the free vars.  (Note: the term is a well-formed lambda
; application, so we know the obvious about the free vars of its body
; versus its formals.  But that is not the question!  The question is:
; what variables are bound in alist?  There is no a priori
; relationship between term and alist.)

       (let* ((new-body (lambda-nest-unhide term))
              (stack (make-stack-from-alist new-body alist))
              (inst-term
               (fcons-term* 'HIDE
                            (if alist
                                (make-lambda-application
                                 (caar stack)
                                 new-body
                                 (cdar stack))
                              new-body)))
              (new-rcnst (expand-permission-p inst-term rcnst geneqv
                                              wrld)))
         (cond
          (new-rcnst

; We rewrite the ``instantiated'' term under the empty substitution.

           (rewrite-entry (rewrite (fargn inst-term 1) nil 1)
                          :ttree (push-lemma
                                  (fn-rune-nume 'hide nil nil wrld)
                                  ttree)
                          :rcnst new-rcnst))
          (t (rewrite-entry
              (rewrite-with-lemmas inst-term))))))
      ((eq (ffn-symb term) 'IMPLIES)

; We handle IMPLIES specially.  We rewrite both the hyps and the
; concl under the original type-alist, and then immediately return the
; resulting expansion.  This prevents the concl from being rewritten
; under the (presumably) more powerful type-alist gotten from assuming
; the hyps true until after any normalization has occurred.  See the
; mini-essay at assume-true-false-if.

; It is possible that this rewriting will force some hypotheses in a
; ``context free'' way, i.e., forcing might occur while rewriting the
; concl but the forced assumption won't record the hypotheses that
; might actually be necessary to establish the assumption.  This is
; not supposed to happen because the only IMPLIES we should see
; (barring any introduced by user supplied rewrite rules) are in :USE
; hyps, and their hyps are normally provable under the hyps of the
; original theorem -- and those original hyps are in the type-alist
; defining this context.

       (sl-let
        (rewritten-test ttree)
        (rewrite-entry (rewrite (fargn term 1) alist 1)
                       :obj '?
                       :geneqv *geneqv-iff*
                       :pequiv-info nil)
        (cond
         ((equal rewritten-test *nil*)
          (mv step-limit *t* ttree))
         (t
          (sl-let (rewritten-concl ttree)
                  (rewrite-entry (rewrite (fargn term 2) alist 1)
                                 :obj '?
                                 :geneqv *geneqv-iff*
                                 :pequiv-info nil)
                  (cond
                   ((equal rewritten-concl *nil*)
                    (mv step-limit
                        (dumb-negate-lit rewritten-test)
                        ttree))
                   ((or (quotep rewritten-concl) ; not *nil*
                        (equal rewritten-test rewritten-concl))
                    (mv step-limit *t* ttree))
                   ((quotep rewritten-test) ; not *nil*

; We already handle the case above that rewritten-test is *nil*.  So (implies
; test concl) almost simplifies to rewritten-concl, the issue being that
; implies returns a boolean but rewritten-concl might not be Boolean.  At this
; point we have already handled the case that rewritten-concl is a quotep (so,
; there is no opportunity at this point to simplify, for example, '3 to 't);
; but we could perhaps simplify here by checking that the rewritten-concl has a
; Boolean type-set.  However, it seems unlikely that such extra computational
; effort would be worthwhile, since calls of implies can generally be expected
; to be in a Boolean context, and we already optimize for that case just below.

                    (let ((rune
                           (geneqv-refinementp 'iff geneqv wrld)))
                      (cond
                       (rune (mv step-limit
                                 rewritten-concl
                                 (push-lemma rune ttree)))
                       (t (mv step-limit
                              (fcons-term* 'if
                                           rewritten-concl
                                           *t*
                                           *nil*)
                              ttree)))))
                   (t (mv step-limit
                          (subcor-var

; It seems reasonable to keep this in sync with the corresponding use of
; subcor-var in rewrite-atm.

                           (formals 'IMPLIES wrld)
                           (list rewritten-test rewritten-concl)
                           (bbody 'IMPLIES))
                          ttree))))))))
      ((eq (ffn-symb term) 'double-rewrite)
       (sl-let
        (term ttree)
        (rewrite-entry (rewrite (fargn term 1) alist 1))
        (rewrite-entry (rewrite term nil bkptr)
                       :ttree (push-lemma (fn-rune-nume 'double-rewrite
                                                        nil nil wrld)
                                          ttree))))
      ((not-to-be-rewrittenp
        term
        alist
        (access rewrite-constant rcnst
                :terms-to-be-ignored-by-rewrite))
       (prepend-step-limit
        2
        (rewrite-solidify (sublis-var alist term)
                          type-alist obj geneqv
                          (access rewrite-constant rcnst
                                  :current-enabled-structure)
                          wrld ttree
                          simplify-clause-pot-lst
                          (access rewrite-constant rcnst :pt))))
      (t
       (let ((fn (ffn-symb term)))
         (mv-let (mv-nth-result mv-nth-rewritep)
           (if (eq fn 'mv-nth)
               (simplifiable-mv-nth term alist)
             (mv nil nil))
           (cond
            (mv-nth-result

; This is a special case.  We are looking at a term/alist of the form (mv-nth
; 'i (cons x0 (cons x1 ... (cons xi ...)...))) and we immediately rewrite it to
; xi.  The mv-nth-result either needs further rewriting under the alist (when
; mv-nth-rewritep is t) or was taken from the alist and needs no further
; rewriting (in which case we finish by calling rewrite-solidify-plus, since
; this case is similar to the variablep case of rewrite).  Before we did this,
; we would rewrite x0, x1, etc., all of which are irrelevant.  This code is
; helpful because of the way (mv-let (v0 v1 ... vi ...) (foo ...)  (p v0 ...))
; is translated.  Note however that the bkptr we report in the rewrite entry
; below is 2, i.e., we say we are rewriting the 2nd arg of the mv-nth, when in
; fact we are rewriting a piece of it (namely xi).

             (let ((ttree (push-lemma
                           (fn-rune-nume 'mv-nth nil nil wrld)
                           ttree))
                   (step-limit (1+f step-limit)))
               (declare (type (signed-byte 30) step-limit))
               (if mv-nth-rewritep
                   (rewrite-entry
                    (rewrite mv-nth-result alist 2))
                 (rewrite-entry
                  (rewrite-solidify-plus mv-nth-result)))))
            (t
             (let ((ens (access rewrite-constant rcnst
                                :current-enabled-structure)))
               (mv-let
                 (deep-pequiv-lst shallow-pequiv-lst)
                 (pequivs-for-rewrite-args fn geneqv pequiv-info wrld ens)
                 (sl-let
                  (rewritten-args ttree)
                  (rewrite-entry
                   (rewrite-args (fargs term) alist 1 nil
                                 deep-pequiv-lst shallow-pequiv-lst
                                 geneqv fn)
                   :obj '?
                   :geneqv
                   (geneqv-lst fn geneqv ens wrld)
                   :pequiv-info nil ; ignored
                   )
                  (cond
                   ((and
                     (or (flambdap fn)
                         (logicp fn wrld))
                     (all-quoteps rewritten-args)
                     (or
                      (flambda-applicationp term)
                      (and (enabled-xfnp fn ens wrld)

; We don't mind disallowing constrained functions that have attachments,
; because the call of ev-fncall below disallows the use of attachments (last
; parameter, aok, is nil).  Indeed, we rely on this check in chk-live-state-p.

                           (not (getpropc fn 'constrainedp nil wrld)))))

; Note: The test above, if true, leads here where we execute the
; executable-counterpart of the fn (or just go into the lambda
; expression if it's a lambda application).  The test however is
; obscure.  What it says is "run the function if (a) it is either a
; lambda or a :logic function symbol, (b) all of its args are quoted
; constants, and either (c1) the fn is a lambda expression, or (c2)
; the fn is enabled and fn is not a constrained fn."  Thus,
; constrained fns fail the test.  Defined functions pass the test
; provided such functions are currently toggled.  Undefined functions
; (e.g., car) pass the test.

                    (cond
                     ((flambda-applicationp term)
                      (rewrite-entry
                       (rewrite (lambda-body fn)
                                (pairlis$ (lambda-formals fn)
                                          rewritten-args)
                                'lambda-body)))
                     (t
                      (let ((ok-to-force (ok-to-force rcnst)))
                        (mv-let
                          (erp val apply$ed-fns)
                          (pstk
                           (ev-fncall+ fn
                                       (strip-cadrs rewritten-args)

; The strictp argument is nil here, as we will deal with required true warrants
; in push-warrants, below.  See the Essay on Evaluation of Apply$ and Loop$
; Calls During Proofs.

                                       nil
                                       state))
                          (mv-let
                            (erp2 ttree)
                            (cond ((or erp

; No special action is necessary if apply$ed-fns is nil, as opposed to a
; non-empty list.

                                       (null apply$ed-fns))
                                   (mv erp ttree))
                                  (t (push-warrants
                                      apply$ed-fns
                                      (cons-term fn rewritten-args)
                                      type-alist ens wrld ok-to-force
                                      ttree ttree)))
                            (cond
                             (erp2

; We following a suggestion from Matt Wilding and attempt to rewrite the term
; before applying HIDE.  This is really a heuristic choice; we could choose
; always to apply HIDE, as we did before v2-8.  So we do not apply
; rewrite-primitive (as in the last COND clause, below) as this would only
; apply in the rare case that the current function symbol (whose evaluation has
; errored out) is a compound recognizer.

                              (let ((new-term1
                                     (cons-term fn rewritten-args)))
                                (sl-let
                                 (new-term2 ttree)
                                 (rewrite-entry
                                  (rewrite-with-lemmas new-term1))
                                 (cond
                                  ((equal new-term1 new-term2)
                                   (mv step-limit
                                       (hide-with-comment
                                        (if erp
                                            (cons :non-executable erp)
                                          (cons :missing-warrant erp2))
                                        new-term1
                                        wrld state)
                                       (push-lemma
                                        (fn-rune-nume 'hide nil nil
                                                      wrld)
                                        ttree)))
                                  (t (mv step-limit new-term2 ttree))))))
                             (t (mv step-limit
                                    (kwote val)
                                    (push-lemma
                                     (fn-rune-nume fn nil t wrld)
                                     ttree))))))))))
                   (t
                    (sl-let
                     (rewritten-term ttree)
                     (rewrite-entry
                      (rewrite-primitive fn rewritten-args))
                     (rewrite-entry
                      (rewrite-with-lemmas
                       rewritten-term)))))))))))))))))

(defun rewrite-solidify-plus (term ; &extra formals
                              rdepth step-limit
                              type-alist obj geneqv pequiv-info wrld state
                              fnstack ancestors backchain-limit
                              simplify-clause-pot-lst rcnst gstack ttree)

; This function allows us one more try at relieving a hypothesis by rewriting
; with lemmas when rewrite-solidify isn't sufficient.  The call of
; rewrite-with-lemmas1 below can allow a hypothesis to be relieved when the
; term in question was previously rewritten in an equality context, rather than
; the more generous propositional context that we have available when relieving
; a hypothesis.

; For a motivating example, see the item in note-2-9 (proofs) starting with:
; "The rewriter has been modified to work slightly harder in relieving
; hypotheses."

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   3
   (signed-byte 30)
   (mv-let (new-term new-ttree)
           (rewrite-solidify term type-alist obj geneqv
                             (access rewrite-constant rcnst
                                     :current-enabled-structure)
                             wrld ttree
                             simplify-clause-pot-lst
                             (access rewrite-constant rcnst :pt))
           (cond ((or (eq obj '?)

; Keep the next four conditions in sync with those in rewrite-with-lemmas.

                      (variablep new-term)
                      (fquotep new-term)
                      (member-equal (ffn-symb new-term)
                                    (access rewrite-constant rcnst
                                            :fns-to-be-ignored-by-rewrite))
                      (flambda-applicationp term)
                      (not (equal geneqv *geneqv-iff*))
                      (not (equal term new-term)))
                  (mv step-limit new-term new-ttree))
                 (t
                  (sl-let (rewrittenp term1 ttree)
                          (rewrite-entry

; We are tempted to call rewrite here.  But the point of this call is to handle
; the case that term was the result of looking up a variable in an alist, where
; the term has already been rewritten but perhaps not under *geneqv-iff*.  All
; we really want to do here is to make another pass through the lemmas in case
; one of them applies this time.

                           (rewrite-with-lemmas1
                            term
                            (getpropc (ffn-symb new-term) 'lemmas nil wrld)))
                          (declare (ignore rewrittenp))
                          (mv step-limit term1 ttree)))))))

(defun rewrite-if (test unrewritten-test left right alist ; &extra formals
                        rdepth step-limit
                        type-alist obj geneqv pequiv-info wrld state fnstack
                        ancestors backchain-limit
                        simplify-clause-pot-lst rcnst gstack ttree)

; Test is the result of rewriting unrewritten-test under the same alist and
; extra formals.  Except, unrewritten-test can be nil, in which case we of
; course make no such claim.

; Warning: If you modify this function, consider modifying the code below a
; comment mentioning rewrite-if in rewrite-with-lemmas.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   3
   (signed-byte 30)
   (mv-let
     (test unrewritten-test left right swapped-p)
     (cond
      ((and (ffn-symb-p test 'if)
            (equal (fargn test 2) *nil*)
            (equal (fargn test 3) *t*))

; Note: In Nqthm the equality test against *t* was a known-whether-nil check.
; But unrewritten-test has been rewritten under equiv = 'iff.  Hence, its two
; branches were rewritten under 'iff.  Thus, if one of them is known non-nil
; under the type-alist then it was rewritten to *t*.

       (mv (fargn test 1) nil right left t))
      (t (mv test unrewritten-test left right nil)))
     (cond
      ((quotep test)

; It often happens that the test rewrites to *t* or *nil* and we can
; avoid the assume-true-false below.

       (if (cadr test)
           (if (and unrewritten-test ; optimization (see e.g. rewrite-if above)
                    (geneqv-refinementp 'iff geneqv wrld)
                    (equal unrewritten-test left))

; We are in the process of rewriting a term of the form (if x x y), which
; presumably came from an untranslated term of the form (or x y).  We do not
; want to rewrite x more than once if we can get away with it.  We are using
; the fact that the following is a theorem:  (iff (if x x y) (if x t y)).
; We will use this observation later in the body of this function as well.

               (mv step-limit *t* ttree)
             (rewrite-entry (rewrite left alist 2)))
         (rewrite-entry (rewrite right alist 3))))
      (t (let ((ens (access rewrite-constant rcnst :current-enabled-structure)))
           (mv-let
             (must-be-true
              must-be-false
              true-type-alist
              false-type-alist
              ts-ttree)

; Once upon a time, the call of assume-true-false below was replaced by a call
; of repetitious-assume-true-false.  See the Essay on Repetitive Typing.  This
; caused a terrible slowdown in the proof of the Nqthm package theorems (e.g.,
; the proof of AX-20-2 seemed never to complete but was not apparently
; looping).  It was apparently due to the opening of MEMBER on a long constant
; list and each time doing a repetition on an increasingly long type-alist (but
; this is just speculation).  For a simple example of a problem that arises if
; repetition is used here, consider the example problem shown with the Satriani
; hack above.  (Search for make-standard-codes.)  Try that thm both with an
; assume-true-false and a repetitious-assume-true-false here.  The former takes
; 3.87 seconds; the latter takes about 13.37 seconds.  The problem is that we
; keep assuming tests of the form (EQUAL X '#\a) on a type-alist that contains
; a litany of all the chars X is not equal to, i.e., a type-alist containing
; such triples as ((EQUAL X '#\b) 64 ; (*ts-nil*)) for lots of different #\b's.
; On the true branch, we add the pair that X is of type *ts-character* and then
; reconsider every one of the (EQUAL X '#\b) assumptions previously posted.

; Note: Running that example will also illustrate another oddity.  You will see
; successive duplicate calls of assume-true-false on the (EQUAL X '#\a)'s.
; What is happening?  In opening (MEMBER X '(#\a ...)) in rewrite-fncall we
; rewrite the body of member, producing the first call of assume-true-false
; when we consider (equal x (car lst)).  The result of rewriting the body is
; essentially an instance of the body; the recursive call within it is unopened
; because member is recursive (!).  Then we decide to keep the rewrite and
; rewrite the body again.  So we again assume-true-false the instance of the
; just produced (EQUAL X '#\a).

; If ancestors is non-nil, ACL2 is backchaining to relieve the hypothesis of
; some rule.  Conversely, if ancestors is nil, ACL2 is rewriting a term in the
; current clause.  As of v2_8 if ACL2 is backchaining, we use the new and
; stronger assume-true-false capability of milking the linear pot.  We apply
; the extra power when backchaining because ACL2's operations are largely
; invisible to the user when backchaining.  The main effect of using
; assume-true-false this way is to cause recursive definitions to open up a
; little more aggressively.  (Since the simplify-clause-pot-lst is passed in,
; linear arithmetic --- via type-reasoning --- can decide the truth or falsity
; of more inequalities than otherwise, causing more if expressions to
; collapse.  This may eliminate recursive calls that would otherwise be passed
; up to rewrite-fncallp and have to be accepted as heuristically simpler.  It
; could also change the too-many-ifs situation.)  We do not apply the extra
; power when rewriting the current clause, because it is potentially expensive
; and the user can see (and therefore change) what is going on.

             (if ancestors
                 (assume-true-false test nil
                                    (ok-to-force rcnst)
                                    nil type-alist ens wrld
                                    simplify-clause-pot-lst
                                    (access rewrite-constant rcnst :pt)
                                    nil)
               (assume-true-false test nil
                                  (ok-to-force rcnst)
                                  nil type-alist ens wrld nil nil nil))
             (cond
              (must-be-true
               (if (and unrewritten-test
                        (geneqv-refinementp 'iff geneqv wrld)
                        (equal unrewritten-test left))
                   (mv step-limit *t* (cons-tag-trees ts-ttree ttree))
                 (rewrite-entry (rewrite left alist 2)
                                :type-alist true-type-alist
                                :ttree (cons-tag-trees ts-ttree ttree))))
              (must-be-false
               (rewrite-entry (rewrite right alist 3)
                              :type-alist false-type-alist
                              :ttree (cons-tag-trees ts-ttree ttree)))
              (t (let ((ttree (normalize-rw-any-cache ttree)))
                   (sl-let
                    (rewritten-left ttree)
                    (if (and unrewritten-test
                             (geneqv-refinementp 'iff geneqv wrld)
                             (equal unrewritten-test left))
                        (mv step-limit *t* ttree)
                      (sl-let (rw-left ttree1)
                              (rewrite-entry (rewrite left alist 2)
                                             :type-alist true-type-alist
                                             :ttree (rw-cache-enter-context ttree))
                              (mv step-limit
                                  rw-left
                                  (rw-cache-exit-context ttree ttree1))))
                    (sl-let (rewritten-right ttree1)
                            (rewrite-entry (rewrite right alist 3)
                                           :type-alist false-type-alist
                                           :ttree (rw-cache-enter-context
                                                   ttree))
                            (mv-let
                              (rewritten-term ttree)
                              (rewrite-if1 test
                                           rewritten-left rewritten-right
                                           swapped-p
                                           type-alist geneqv ens
                                           (ok-to-force rcnst)
                                           wrld
                                           (rw-cache-exit-context ttree ttree1))
                              (rewrite-entry
                               (rewrite-with-lemmas
                                rewritten-term)))))))))))))))

(defun rewrite-args (args alist bkptr rewritten-args-rev
                          deep-pequiv-lst shallow-pequiv-lst
                          parent-geneqv parent-fn ; &extra formals
                          rdepth step-limit
                          type-alist obj geneqv pequiv-info wrld state fnstack
                          ancestors backchain-limit
                          simplify-clause-pot-lst rcnst gstack ttree)

; Note: In this function, the extra formal geneqv is actually a list of geneqvs
; or nil denoting a list of nil geneqvs.

; See the Essay on Patterned Congruences and Equivalences for a discussion of
; non-&extra formals of this function.  Note our assumption in function
; geneqv-for-rewrite that every pequiv in shallow-pequiv-lst has an enabled
; :congruence-rule; this holds because of how shallow-pequiv-lst is created by
; the call of pequivs-for-rewrite-args in rewrite.  Also note that pequiv-info
; is ignored in this function and that deep-pequiv-lst can be the special
; value, :none, which is handled by function pequiv-info-for-rewrite.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit)
           (ignore pequiv-info))
  (the-mv
   3
   (signed-byte 30)
   (cond ((null args)
          (mv step-limit (reverse rewritten-args-rev) ttree))
         (t (mv-let
             (child-geneqv child-pequiv-info)
             (geneqv-and-pequiv-info-for-rewrite
              parent-fn bkptr rewritten-args-rev args alist
              parent-geneqv
              (car geneqv)
              deep-pequiv-lst
              shallow-pequiv-lst
              wrld)
             (sl-let
              (rewritten-arg ttree)
              (rewrite-entry (rewrite (car args) alist bkptr)
                             :geneqv child-geneqv
                             :pequiv-info child-pequiv-info)
              (rewrite-entry
               (rewrite-args (cdr args) alist (1+ bkptr)
                             (cons rewritten-arg rewritten-args-rev)
                             deep-pequiv-lst shallow-pequiv-lst
                             parent-geneqv parent-fn)
               :pequiv-info nil ; ignored
               :geneqv (cdr geneqv))))))))

(defun rewrite-primitive (fn args ; &extra formals
                             rdepth step-limit
                             type-alist obj geneqv pequiv-info wrld state
                             fnstack ancestors backchain-limit
                             simplify-clause-pot-lst rcnst gstack
                             ttree)

  (declare (ignore geneqv pequiv-info obj)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   3
   (signed-byte 30)
   (cond
    ((flambdap fn) (mv step-limit (fcons-term fn args) ttree))
    ((eq fn 'equal)
     (rewrite-entry (rewrite-equal (car args) (cadr args) nil nil)
                    :obj '?
                    :geneqv nil
                    :pequiv-info nil ; ignored
                    ))
    (t (let* ((ens (access rewrite-constant rcnst
                           :current-enabled-structure))
              (recog-tuple (most-recent-enabled-recog-tuple fn wrld ens)))
         (cond
          (recog-tuple
           (prepend-step-limit
            2
            (rewrite-recognizer recog-tuple (car args) type-alist
                                ens
                                (ok-to-force rcnst)
                                wrld
                                ttree
                                simplify-clause-pot-lst
                                (access rewrite-constant rcnst :pt))))
          (t (mv step-limit (cons-term fn args) ttree))))))))

(defun rewrite-equal (lhs rhs lhs-ancestors rhs-ancestors ; &extra formals
                          rdepth step-limit
                          type-alist obj geneqv pequiv-info wrld state fnstack
                          ancestors backchain-limit
                          simplify-clause-pot-lst rcnst gstack ttree)

; We rewrite and return a term equivalent to (EQUAL lhs rhs), plus a ttree.
; We keep lists lhs-ancestors and rhs-ancestors of lhs and rhs parameters from
; superior calls, in order to break loops as explained below.

  (declare (ignore obj geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (cond
    ((equal lhs rhs)
     (mv step-limit *t* (puffert ttree)))
    ((and (quotep lhs)
          (quotep rhs))
     (mv step-limit *nil* (puffert ttree)))
    (t
     (mv-let
      (ts-lookup ttree-lookup)
      (assoc-type-alist (fcons-term* 'equal lhs rhs) type-alist wrld)
      (cond
       ((and ts-lookup (ts= ts-lookup *ts-t*))
        (mv step-limit *t* (cons-tag-trees ttree-lookup ttree)))
       ((and ts-lookup (ts= ts-lookup *ts-nil*))
        (mv step-limit *nil* (cons-tag-trees ttree-lookup ttree)))
       (t
        (let ((ens (access rewrite-constant rcnst
                           :current-enabled-structure))
              (ok-to-force (ok-to-force rcnst)))
          (mv-let
           (ts-lhs ttree-lhs)
           (type-set lhs ok-to-force nil
                     type-alist ens wrld ttree
                     simplify-clause-pot-lst
                     (access rewrite-constant rcnst :pt))
           (mv-let
            (ts-rhs ttree+)
            (type-set rhs ok-to-force nil
                      type-alist ens wrld ttree-lhs
                      simplify-clause-pot-lst
                      (access rewrite-constant rcnst :pt))
            (mv-let
             (ts-equality ttree-equality)
             (type-set-equal ts-lhs ts-rhs ttree+ ttree)
             (cond
              ((ts= ts-equality *ts-t*)
               (mv step-limit *t* ttree-equality))
              ((ts= ts-equality *ts-nil*)
               (mv step-limit *nil* ttree-equality))

; The commented-out case just below, here explicitly before we added the above
; call of type-set-equal, is handled by that call.

;           ((ts-disjointp ts-lhs ts-rhs)
;            (mv *nil* (puffert ttree+)))

              ((equal-x-cons-x-yp lhs rhs)

; Recall that the correctness of a positive answer by equal-x-cons-x-yp doesn't
; rely on type-set knowledge.

               (mv step-limit *nil* (puffert ttree)))
              ((and (ts-subsetp ts-lhs *ts-boolean*)
                    (equal rhs *t*))
               (mv step-limit lhs (puffert ttree-lhs)))
              ((and (ts-subsetp ts-rhs *ts-boolean*)
                    (equal lhs *t*))
               (mv step-limit rhs (puffert ttree+)))
              ((equal lhs *nil*)
               (mv step-limit (mcons-term* 'if rhs *nil* *t*) (puffert ttree)))
              ((equal rhs *nil*)
               (mv step-limit (mcons-term* 'if lhs *nil* *t*) (puffert ttree)))
              ((equalityp lhs)
               (mv step-limit (mcons-term* 'if
                                           lhs
                                           (mcons-term* 'equal rhs *t*)
                                           (mcons-term* 'if rhs *nil* *t*))
                   (puffert ttree)))
              ((equalityp rhs)
               (mv step-limit
                   (mcons-term* 'if
                                rhs
                                (mcons-term* 'equal lhs *t*)
                                (mcons-term* 'if lhs *nil* *t*))
                   (puffert ttree)))
              ((and (ts-subsetp ts-lhs *ts-cons*)
                    (ts-subsetp ts-rhs *ts-cons*)
                    (not (member-equal lhs lhs-ancestors))
                    (not (member-equal rhs rhs-ancestors)))

; If lhs and rhs are both of type cons, we (essentially) recursively rewrite
; the equality of their cars and then of their cdrs.  If either of these two
; tests fails, this equality is nil.  If both succeed, this one is t.
; Otherwise, we don't rewrite term.

; Before attempting to add complete equality we did not do anything like this
; and relied solely on elim to do it for us.  In the first attempt to add it to
; rewrite we just rewrote all such (EQUAL lhs rhs) to the conjunction of the
; equalities of the components.  That was unsatisfactory because it caused such
; equalities as (EQUAL (ADDTOLIST X L) B) to be torn up all the time.  That
; caused us to fail to prove thms like SORT-OF-ORDERED-NUMBER-LIST because weak
; subgoals are pushed -- subgoals about (CAR (ADDTOLIST X L)) and (CDR
; (ADDTOLIST X L)) instead about (ADDTOLIST X L) itself.

; In Version_3.3 and earlier (even as far back as Version_2.2) we rewrote
; equality terms (equal (car lhs) (car rhs)) and (equal (cdr lhs) (cdr rhs)),
; with variables lhs and rhs bound to the parameters lhs and rhs.  But now we
; instead call the rewriter separately on the car and cdr of lhs and rhs (hence
; "essentially" in a paragraph above).  Then to check equality we finish using
; a recursive call of rewrite-equal with lhs and rhs pushed on to the stacks
; lhs-ancestors and rhs-ancestors (respectively).  We avoid making a recursive
; call if we see that we have looped back to a call with the same lhs or rhs,
; which indicates a potential infinite loop.  When we formerly called the full
; rewriter on (equal (car lhs) (car rhs)) and (equal (cdr lhs) (cdr rhs)), We
; did not make such a check and we found an infinite loop in the following
; example (a slight simplification of one Sol Swords sent to us); see just
; below for analysis.

; (thm (implies (and (consp y)
;                    (consp (car y))
;                    (equal (caar y) y))
;               (equal y (car y))))

; If you try the following trace on the above example using Version_3.3, where
; we called rewrite on applications of equal to the two cars and the two cdrs

; (trace$ (rewrite :entry (list 'rewrite term alist type-alist))
;         (rewrite-equal :entry (list 'r-e lhs rhs type-alist)))

; then you will see a loop as follows.

;  98> (R-E Y
;           (CAR Y)
;           (((CAR (CAR Y)) 1536)
;            ((EQUAL (CAR (CAR Y)) Y) 128) ; 128 = *ts-t*
;            ((CAR Y) 1536)
;            (Y 1536)))
;  99> (REWRITE (EQUAL (CAR LHS) (CAR RHS))
;               ((LHS . Y) (RHS CAR Y))
;               (((CAR (CAR Y)) 1536)
;                ((EQUAL (CAR (CAR Y)) Y) 128)
;                ((CAR Y) 1536)
;                (Y 1536)))
;  .... (CAR LHS) rewrites to (CAR Y) and (CAR RHS) rewrites to Y ....
;  .... Then: ....
;  100> (R-E (CAR Y)
;            Y
;            (((CAR (CAR Y)) 1536)
;             ((EQUAL (CAR (CAR Y)) Y) 128)
;             ((CAR Y) 1536)
;             (Y 1536)))

; The calls of rewrite-equal keep toggling between argument list (Y (CAR Y))
; and ((CAR Y) Y), because when we take the CAR, Y becomes (CAR Y), but (CAR Y)
; becomes (CAR (CAR Y)) which simplifies to Y.  Our loop-breaking mechanism
; clearly avoids this problem.  (An elim is still needed to finish the proof,
; but that's fine.)

               (let ((alist (list (cons 'lhs lhs)
                                  (cons 'rhs rhs))))
                 (sl-let
                  (equal-cars new-ttree)
                  (sl-let
                   (cars ttree0)
                   (rewrite-entry (rewrite-args '((car lhs) (car rhs))
                                                alist 1 nil nil nil nil 'equal)
                                  :obj '?
                                  :geneqv nil
                                  :pequiv-info nil ; ignored
                                  :ttree ttree+)
                   (rewrite-entry (rewrite-equal
                                   (car cars)
                                   (cadr cars)

; We considered an alternative to adding the lhs-ancestors and rhs-ancestors
; arguments, namely adding a flag saying whether we could move into this branch
; at all (in place of the member-equal tests above).  With that alternative we
; considered calling rewrite-equal here with that flag set to nil.  However,
; the following example failed when we attempted to make such a restriction on
; making recursive calls.

; (progn (defstub fn (x) t)
;        (defthm test
;          (implies (and (consp (fn x))
;                        (consp (car (fn x)))
;                        (null (cdar (fn x))))
;                   (equal (cons (cons (caar (fn x))
;                                      nil)
;                                (cdr (fn x)))
;                          (fn x)))))

                                   (cons lhs lhs-ancestors)
                                   (cons rhs rhs-ancestors))
                                  :obj nil ; ignored
                                  :geneqv nil ; ignored
                                  :pequiv-info nil ; ignored
                                  :ttree ttree0))

; Note that we pass ttree+ (which includes ttree) into the rewrite of
; the car equality and getting back new-ttree.  We will pass new-ttree
; into the rewrite of the cdr equality and get back new-ttree.  If we
; succeed, we'll return new-ttree, which includes ttree, ttree+, and
; the rewriting; otherwise, we'll stick with the original ttree.

                  (cond
                   ((equal equal-cars *t*)
                    (sl-let
                     (equal-cdrs new-ttree)
                     (sl-let
                      (cdrs ttree0)
                      (rewrite-entry (rewrite-args '((cdr lhs) (cdr rhs))
                                                   alist 1 nil nil nil nil
                                                   'equal)
                                     :obj '?
                                     :geneqv nil
                                     :pequiv-info nil ; ignored
                                     :ttree new-ttree)
                      (rewrite-entry (rewrite-equal
                                      (car cdrs)
                                      (cadr cdrs)
                                      (cons lhs lhs-ancestors)
                                      (cons rhs rhs-ancestors))
                                     :obj nil ; ignored
                                     :geneqv nil ; ignored
                                     :pequiv-info nil ; ignored
                                     :ttree ttree0))
                     (cond ((equal equal-cdrs *t*)
                            (mv step-limit *t* (puffert new-ttree)))
                           ((equal equal-cdrs *nil*)
                            (mv step-limit *nil* (puffert new-ttree)))
                           (t (mv step-limit
                                  (mcons-term* 'equal lhs rhs)
                                  (accumulate-rw-cache t new-ttree ttree))))))
                   ((equal equal-cars *nil*)
                    (mv step-limit *nil* (puffert new-ttree)))
                   (t
                    (let ((ttree (accumulate-rw-cache t new-ttree ttree)))

; If we fail to get a definitive answer then we still might be able to
; answer negatively by rewriting the cdrs.  We have been asymmetric
; for a long time without knowing it; at this point we used to simply
; return (mcons-term* 'equal lhs rhs).  In fact, the following theorem
; didn't prove --

; (implies (equal (cons a b) (cons x y))
;          (equal b y))

; even though the analogous one for the cars did prove:

; (implies (equal (cons a b) (cons x y))
;          (equal a x))

; If the cdrs aren't known to be different, then we do simply return
; the obvious equality.  That is what we would have done had lhs or
; rhs not been of type *ts-cons* -- see the (t (mv (mcons-term* ...)
; ttree)) clause at the very end of this function.  The explicit
; returning of the equality forces us to consider the (and (ts-subsetp
; ts-lhs *ts-cons*) (ts-subsetp ts-rhs *ts-cons*)) case as the second
; to last case in the main cond.  We could have coded the and above
; differently so that if both were conses and the rewrites decide it
; then we return appropriately and otherwise we fall through to
; whatever other rewrites we consider.  But we didn't.

                      (sl-let (equal-cdrs new-ttree)
                              (sl-let
                               (cdrs ttree0)
                               (rewrite-entry
                                (rewrite-args '((cdr lhs) (cdr rhs))
                                              alist 1 nil nil nil nil 'equal)
                                :obj '?
                                :geneqv nil
                                :pequiv-info nil ; ignored
                                :ttree ttree)
                               (rewrite-entry
                                (rewrite-equal
                                 (car cdrs)
                                 (cadr cdrs)
                                 (cons lhs lhs-ancestors)
                                 (cons rhs rhs-ancestors))
                                :obj nil ; ignored
                                :geneqv nil ; ignored
                                :pequiv-info nil ; ignored
                                :ttree ttree0))
                              (cond ((equal equal-cdrs *nil*)
                                     (mv step-limit *nil* (puffert new-ttree)))
                                    (t
                                     (mv step-limit
                                         (mcons-term* 'equal lhs rhs)
                                         (accumulate-rw-cache t
                                                              new-ttree
                                                              ttree)))))))))))
              (t (mv step-limit
                     (mcons-term* 'equal lhs rhs)
                     ttree))))))))))))))

(defun relieve-hyp
  (rune target hyp0 unify-subst bkptr memo ; &extra formals
        rdepth step-limit
        type-alist obj geneqv pequiv-info wrld state fnstack ancestors
        backchain-limit
        simplify-clause-pot-lst rcnst gstack ttree)

; We are trying to rewrite hyp0 to true, where hyp0 is the hypothesis of rune
; at (one-based) position bkptr, and target is an instantiated term to which
; rune is being applied.

; We return six results.  Most often they are interpreted as indicated by the
; names:

; (mv step-limit wonp failure-reason unify-subst' ttree' memo').

; Here wonp is t, nil, :unify-subst-list, or a term.  If it is t, nil, or
; :unify-subst-list, then interpretation of the results is as hinted above:
; wonp indicates whether hyp0 was relieved, failure-reason is nil or else a
; token indicating why we failed, and the rest are extended versions of the
; corresponding inputs except for the case :unify-subst-list, where
; unify-subst' is actually a list of unifying substitutions, each of which is
; sufficient for relieving the remaining hypotheses.

; But there is a special case where they are interpreted quite differently: if
; wonp is a term then it means that hyp0 contains free-vars, it was not
; relieved, and the six results are to be interpreted as follows,
; where the last three are unchanged.

; (mv step-limit term typ unify-subst ttree memo)

; This signals that the caller of relieve-hyp is responsible for relieving the
; hypothesis and may do so in either of two ways: Extend unify-subst to make
; term have typ in the original type-alist or extend unify-subst to make hyp0
; true via ground units.  This is called the SPECIAL CASE.

; This function is a No-Change Loser modulo rw-cache: only the values of
; 'rw-cache-any-tag and 'rw-cache-nil-tag may differ between the input and
; output ttrees.

; Below we describe the memo argument, but first, here is an example that
; illustrates how it is used.

; (defstub p1 (x) t)
; (defstub p2 (x) t)
; (defstub p3 (x) t)
; (defaxiom ax (implies (and (p1 x) (p2 y) (consp x) (symbolp y)) (p3 x)))
; (thm (implies (and (p1 a) (p2 b) (p2 c) (consp a) (symbolp b)) (p3 a)))

; In the proof of thm, a rewrite of (p3 a) triggers application of ax.  Note
; that (p2 c) is in front of (p2 b) on the type-alist.  So, the second
; hypothesis of ax first binds y to c.  Since (symbolp y) fails with this
; binding, we backtrack in the relieving of hyps for ax, and now bind y to b.
; But note that we encounter (consp x) again.  Rather than have to rewrite
; (consp x) again, we save the fact that it was relieved when that happened the
; first time, when y was bound to c.  How do we do this?

; Memo (called "allp" in other functions in this nest) can be an alist with
; entries of the form (n vars (subst0 . ttree0) ... (substk . ttreek)), where n
; is a bkptr, vars is (all-vars hyp0), and ttreei is the result of successfully
; calling relieve-hyp with the following arguments: ttree=nil; bkptr=n;
; unify-subst is some substitution whose restriction to vars is substi; and the
; other arguments are the same.  In these cases substi should bind all the free
; variables of hyp0.  The other legal values of memo are nil, t and :start.  If
; memo is nil or t then we do not memoize, though in the case of t we may start
; memoizing in later calls because we have a free variable.  If memo is :start
; or an alist then we return an extended memo (where :start is viewed as the
; empty memo) if this call of relieve-hyp succeeds and all variables of hyp0
; are bound in unify-subst.

; Note that unlike some other functions in the rewrite clique, here we really
; do care that bkptr is a number representing the hypothesis.

  (declare (ignore obj geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   6
   (signed-byte 30)
   (cond ((ffn-symb-p hyp0 'synp)
          (mv-let (wonp failure-reason unify-subst ttree)
                  (relieve-hyp-synp rune hyp0 unify-subst rdepth type-alist wrld
                                    state fnstack ancestors backchain-limit
                                    simplify-clause-pot-lst rcnst gstack ttree
                                    bkptr)
                  (mv step-limit wonp failure-reason unify-subst ttree memo)))
         (t (mv-let
             (forcep1 bind-flg)
             (binding-hyp-p hyp0 unify-subst wrld)
             (let ((hyp (if forcep1 (fargn hyp0 1) hyp0)))
               (cond
                (bind-flg
                 (sl-let
                  (rewritten-rhs ttree)
                  (rewrite-entry
                   (rewrite (fargn hyp 2)
                            unify-subst
                            (if (or (f-get-global 'gstackp state)
                                    (f-get-global 'dmrp state))
                                (cons 'rhs bkptr)
                              nil))
                   :obj '?
                   :ancestors
                   (cons (make-ancestor-binding-hyp hyp unify-subst)
                         ancestors)
                   :geneqv (and (not (eq (ffn-symb hyp) 'equal))
                                (cadr (geneqv-lst
                                       (ffn-symb hyp)
                                       *geneqv-iff*
                                       (access rewrite-constant rcnst
                                               :current-enabled-structure)
                                       wrld)))
                   :pequiv-info nil)
                  (mv step-limit
                      t
                      nil
                      (cons (cons (fargn hyp 1) rewritten-rhs)
                            unify-subst)
                      ttree
                      memo)))
                ((free-varsp hyp unify-subst)

; See comment above about "SPECIAL CASE".

                 (mv-let (term typ compound-rec-rune?)
                   (term-and-typ-to-lookup
                    hyp wrld (access rewrite-constant
                                     rcnst
                                     :current-enabled-structure))
                   (mv step-limit term typ unify-subst
                       (push-lemma? compound-rec-rune? ttree)
                       memo)))
                (t
                 (let* ((memo-active (memo-activep memo))
                        (memo-entry (and (consp memo)
                                         (cdr (assoc bkptr memo))))
                        (hyp-vars (if memo-entry
                                      (car memo-entry)
                                    (and memo-active ; optimization
                                         (all-vars hyp0))))
                        (restricted-unify-subst
                         (and memo-active ; optimization
                              (restrict-alist hyp-vars unify-subst)))
                        (old-entry (and memo-entry
                                        (assoc-equal restricted-unify-subst
                                                     (cdr memo-entry)))))
                   (cond
                    (old-entry
                     (mv step-limit t nil unify-subst
                         (cons-tag-trees-rw-cache (cdr old-entry) ttree)
                         memo))
                    (t
                     (sl-let
                      (relieve-hyp-ans failure-reason unify-subst ttree0)
                      (let ((ttree (if memo-active

; If memo-active is true, we may be storing a ttree from the work done below,
; and we do not want to accumulate the existing ttree into that one.  Later
; below, if memo-active is true, then we will cons ttree0 (bound above) with
; ttree.

                                       (rw-cache ttree)
                                     ttree)))
                        (mv-let
                         (lookup-hyp-ans unify-subst ttree)
                         (lookup-hyp hyp type-alist wrld unify-subst ttree
                                     (access rewrite-constant
                                             rcnst
                                             :current-enabled-structure))

; We know that unify-subst is not extended, since (free-varsp hyp unify-subst)
; is false, but it still seems appropriate to use the existing code in
; one-way-unify1 under search-type-alist (under lookup-hyp).

                         (cond
                          (lookup-hyp-ans
                           (mv step-limit t nil unify-subst ttree))
                          (t
                           (let* ((inst-hyp (sublis-var unify-subst hyp))
                                  (forcer-fn (and forcep1 (ffn-symb hyp0)))
                                  (force-flg (ok-to-force rcnst))
                                  (forcep (and forcep1 force-flg)))
                             (mv-let
                              (knownp nilp nilp-ttree)
                              (known-whether-nil
                               inst-hyp type-alist
                               (access rewrite-constant rcnst
                                       :current-enabled-structure)
                               force-flg
                               nil ; dwp
                               wrld
                               ttree)
                              (cond
                               (knownp
                                (cond
                                 (nilp
                                  (mv step-limit
                                      nil
                                      'known-nil
                                      unify-subst
                                      ttree))
                                 (t
                                  (mv step-limit
                                      t
                                      nil
                                      unify-subst
                                      nilp-ttree))))
                               (t
                                (mv-let
                                 (on-ancestorsp assumed-true)
                                 (ancestors-check inst-hyp ancestors (list rune))
                                 (cond
                                  ((and on-ancestorsp assumed-true)
                                   (mv step-limit t nil unify-subst ttree))
                                  ((or on-ancestorsp ; and (not assumed-true)
                                       (backchain-limit-reachedp
                                        backchain-limit
                                        ancestors))
                                   (mv-let
                                    (force-flg ttree)
                                    (cond
                                     ((not forcep)
                                      (mv nil ttree))
                                     (t
                                      (force-assumption
                                       rune target inst-hyp
                                       type-alist nil
                                       (immediate-forcep
                                        forcer-fn
                                        (access rewrite-constant rcnst
                                                :current-enabled-structure))
                                       force-flg
                                       ttree)))
                                    (cond
                                     (force-flg
                                      (mv step-limit t nil unify-subst ttree))
                                     (t
                                      (mv step-limit
                                          nil
                                          (if on-ancestorsp
                                              'ancestors
                                            (cons 'backchain-limit ancestors))
                                          unify-subst ttree)))))
                                  (t
                                   (mv-let
                                    (not-flg atm)
                                    (strip-not hyp)
                                    (sl-let
                                     (rewritten-atm new-ttree)
                                     (rewrite-entry (rewrite atm
                                                             unify-subst
                                                             bkptr)
                                                    :obj (if not-flg nil t)
                                                    :geneqv *geneqv-iff*
                                                    :pequiv-info nil
                                                    :ancestors
                                                    (push-ancestor
                                                     (dumb-negate-lit
                                                      inst-hyp)
                                                     (list rune)
                                                     ancestors
                                                     bkptr))
                                     (cond
                                      (not-flg
                                       (if (equal rewritten-atm *nil*)
                                           (mv step-limit t nil unify-subst
                                               new-ttree)
                                         (mv-let
                                          (force-flg new-ttree)
                                          (if (and forcep

; Since we rewrote under *geneqv-iff*, the only way that rewritten-atm
; is known not to be nil is if it's t.

                                                   (not (equal rewritten-atm
                                                               *t*)))
                                              (force-assumption
                                               rune
                                               target
                                               (mcons-term* 'not rewritten-atm)
                                               type-alist
; Note:  :rewrittenp = instantiated unrewritten term.
                                               (mcons-term*
                                                'not
                                                (sublis-var unify-subst atm))
                                               (immediate-forcep
                                                forcer-fn
                                                (access
                                                 rewrite-constant
                                                 rcnst
                                                 :current-enabled-structure))
                                               force-flg
                                               new-ttree)
                                            (mv nil new-ttree))
                                          (cond
                                           (force-flg
                                            (mv step-limit t nil unify-subst
                                                new-ttree))
                                           (t
                                            (mv step-limit
                                                nil
                                                (cons 'rewrote-to
                                                      (dumb-negate-lit
                                                       rewritten-atm))
                                                unify-subst
                                                (accumulate-rw-cache
                                                 t new-ttree ttree)))))))
                                      ((if-tautologyp rewritten-atm)
                                       (mv step-limit t nil unify-subst
                                           new-ttree))
                                      (t (mv-let
                                          (force-flg new-ttree)
                                          (cond
                                           ((and forcep
                                                 (not (equal rewritten-atm
                                                             *nil*)))
                                            (force-assumption
                                             rune
                                             target
                                             rewritten-atm
                                             type-alist
; Note:  :rewrittenp = instantiated unrewritten term.
                                             (sublis-var unify-subst atm)
                                             (immediate-forcep
                                              forcer-fn
                                              (access
                                               rewrite-constant
                                               rcnst
                                               :current-enabled-structure))
                                             force-flg
                                             new-ttree))
                                           (t (mv nil new-ttree)))
                                          (cond
                                           (force-flg
                                            (mv step-limit t nil unify-subst
                                                new-ttree))
                                           (t (mv step-limit
                                                  nil
                                                  (cons 'rewrote-to
                                                        rewritten-atm)
                                                  unify-subst
                                                  (accumulate-rw-cache
                                                   t
                                                   new-ttree
                                                   ttree))))))))))))))))))))
                      (cond
                       (relieve-hyp-ans
                        (mv step-limit relieve-hyp-ans failure-reason
                            unify-subst
                            (if memo-active
                                (cons-tag-trees-rw-cache-first ttree ttree0)
                              ttree0)
                            (cond
                             (memo-entry
                              (put-assoc-eql
                               bkptr
                               (list* hyp-vars
                                      (cons (cons restricted-unify-subst ttree0)
                                            (cdr memo-entry)))
                               memo))
                             (memo-active
                              (put-assoc-eql
                               bkptr
                               (list* hyp-vars
                                      (cons (cons restricted-unify-subst ttree0)
                                            nil))
                               (if (eq memo :start) nil memo)))
                             (t memo))))
                       (t (mv step-limit relieve-hyp-ans failure-reason
                              unify-subst
                              (accumulate-rw-cache t ttree0 ttree)
                              memo)))))))))))))))

(defun relieve-hyps1-unify-subst-lst (unify-subst-lst
                                      rune target hyps backchain-limit-lst
                                      unify-subst bkptr
                                      unify-subst0
                                      ttree0 allp
                                      rw-cache-alist
                                      rw-cache-alist-new ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv pequiv-info
                                      wrld state
                                      fnstack ancestors backchain-limit
                                      simplify-clause-pot-lst rcnst gstack
                                      ttree)

; WARNING: Keep this in sync with relieve-hyps1-free-1.

; This function calls relieve-hyps1 on each alist in unify-subst-list (which is
; non-empty) until the hypotheses are relieved, extending the given unify-subst
; by that alist for each such call.  Note that if this function fails, then the
; failure-reason will be reported based on the last one tried.  That seems the
; simplest approach both for this implementation and for reporting to the
; user.  If there are user complaints about that, we can consider a more
; elaborate form of failure reporting.

  (declare (ignore obj geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   7
   (signed-byte 30)

; In relieve-hyps1-free-1 we extend unify-subst to new-unify-subst by searching
; a type-alist.  Here we perform that extension by taking the first element of
; unify-subst-list.

   (let ((new-unify-subst
          (extend-unify-subst (car unify-subst-lst) unify-subst)))
     (mv-let
       (cached-failure-reason-free cached-failure-reason)
       (rw-cached-failure-pair new-unify-subst rw-cache-alist)
       (sl-let
        (relieve-hyps-ans failure-reason unify-subst1 ttree1 allp
                          inferior-rw-cache-alist-new)
        (cond
         (cached-failure-reason
          (mv step-limit nil
              (and (f-get-global 'gstackp state) ; cons optimization
                   (cons 'cached cached-failure-reason))
              unify-subst ttree allp nil))
         (t
          (rewrite-entry
           (relieve-hyps1 rune target (cdr hyps)
                          (cdr backchain-limit-lst)
                          new-unify-subst
                          (1+ bkptr) unify-subst0 ttree0 allp
                          (cdr cached-failure-reason-free)
                          nil)
           :obj nil :geneqv nil :pequiv-info nil ; all ignored
           )))
        (let ((rw-cache-alist-new
               (extend-rw-cache-alist-free rcnst
                                           new-unify-subst
                                           inferior-rw-cache-alist-new
                                           rw-cache-alist-new)))

          (cond
           (relieve-hyps-ans
            (mv step-limit relieve-hyps-ans nil unify-subst1 ttree1 allp
                rw-cache-alist-new))
           (t
            (let ((rw-cache-alist-new ; add normal-failure reason
                   (rw-cache-add-failure-reason rcnst
                                                new-unify-subst
                                                failure-reason
                                                rw-cache-alist-new)))
              (cond
               ((endp (cdr unify-subst-lst))
                (mv step-limit nil
                    (and (f-get-global 'gstackp state) ; cons optimization
                         (list (cons new-unify-subst
                                     failure-reason)))
                    unify-subst0
                    (accumulate-rw-cache t ttree1 ttree0)
                    nil ; allp
                    rw-cache-alist-new))
               (t ; try the next unify-subst in unify-subst-lst
                (rewrite-entry-extending-failure
                 new-unify-subst
                 failure-reason
                 (relieve-hyps1-unify-subst-lst
                  (cdr unify-subst-lst)
                  rune target hyps backchain-limit-lst
                  unify-subst bkptr
                  unify-subst0 ttree0 allp
                  rw-cache-alist rw-cache-alist-new)
                 :obj nil :geneqv nil :pequiv-info nil ; all ignored
                 :ttree (accumulate-rw-cache t ttree1 ttree0)))))))))))))

(defun relieve-hyps1 (rune target hyps backchain-limit-lst
                           unify-subst bkptr unify-subst0
                           ttree0 allp
                           rw-cache-alist rw-cache-alist-new ; &extra formals
                           rdepth step-limit
                           type-alist obj geneqv pequiv-info wrld state fnstack
                           ancestors backchain-limit
                           simplify-clause-pot-lst rcnst gstack
                           ttree)

; In order to make relieve-hyps a No-Change Loser (modulo rw-cache) without
; making it have to test the answer to its own recursive calls, we have to pass
; down the original unify-subst and ttree so that when it fails it can return
; them instead of the accumulated ones it otherwise would have.

; Parameter allp is nil iff rune has behavior :match-free :once (as opposed to
; :match-free :all).  Its legal non-nil values are explained in a comment in
; relieve-hyp (where it is called memo).  NOTE: if allp is not nil or t then
; allp does not change if we fail, but if allp is :start or an alist then its
; returned value can change even if relieve-hyps1 fails, in order for it to
; serve its memoization purpose.

; We accumulate updates to make to rw-cache-alist into parameter
; rw-cache-alist-new, which is ultimately returned.  Note that
; relieve-hyps1-free-1 and relieve-hyps1-free-2 take responsibility for
; extending rw-cache-alist-new.  Note that rw-cache-alist-new contains only new
; entries, rather than extending rw-cache-alist.

  (declare (ignore obj geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   7
   (signed-byte 30)
   (cond
    ((null hyps)
     (mv step-limit t nil unify-subst ttree allp rw-cache-alist-new))
    (t
     (sl-let
      (relieve-hyp-ans failure-reason new-unify-subst new-ttree allp)
      (with-accumulated-persistence
       rune
       ((the (signed-byte 30) step-limit)
        relieve-hyp-ans failure-reason new-unify-subst new-ttree allp)

; Even in the "special case" for relieve-hyp, we can mark this as a success
; because it will ultimately be counted as a failure if the surrounding call of
; relieve-hyps fails.

       relieve-hyp-ans
       (rewrite-entry (relieve-hyp rune target (car hyps)
                                   unify-subst bkptr allp)
                      :backchain-limit
                      (new-backchain-limit (car backchain-limit-lst)
                                           backchain-limit
                                           ancestors)
                      :obj nil :geneqv nil :pequiv-info nil ; all ignored
                      )
       bkptr)
      (cond
       ((eq relieve-hyp-ans t)
        (rewrite-entry (relieve-hyps1 rune target (cdr hyps)
                                      (cdr backchain-limit-lst)
                                      new-unify-subst
                                      (1+ bkptr)
                                      unify-subst0 ttree0
                                      allp
                                      rw-cache-alist rw-cache-alist-new)
                       :obj nil :geneqv nil :pequiv-info nil ; all ignored
                       :ttree new-ttree))
       ((eq relieve-hyp-ans :unify-subst-list)

; The hypothesis (car hyps) is a call of bind-free that has produced a list of
; unify-substs.

        (sl-let (relieve-hyps-ans failure-reason-lst unify-subst
                                  ttree allp rw-cache-alist-new)
                (rewrite-entry (relieve-hyps1-unify-subst-lst
                                new-unify-subst ; a list of alists
                                rune target hyps
                                backchain-limit-lst
                                unify-subst bkptr
                                unify-subst0
                                ttree0
                                (activate-memo allp)
                                rw-cache-alist
                                rw-cache-alist-new)
                               :obj nil :geneqv nil :pequiv-info nil ; all ignored
                               )
                (mv step-limit relieve-hyps-ans
                    (and (null relieve-hyps-ans)
                         (cond ((null (f-get-global 'gstackp state))
                                nil) ; save some conses
                               (t    ; hence (consp failure-reason-lst)
                                (list* bkptr
                                       'free-vars

; Note that we use 'free-vars here for bind-free; the function
; tilde-@-failure-reason-phrase1 distinguishes between bind-free hypotheses and
; hypotheses that have free variables.

; Note that we reverse below even though we do not reverse in the analogous
; function, relieve-hyps1-free-1.  That is because in relieve-hyps1-free-1, the
; the failure-reason-lst is built by traversing a type-alist whose entries are
; in reverse order from the order of hypotheses encountered that created those
; entries; but here, the unify-subst-lst is processed in order.

                                       (reverse failure-reason-lst)))))
                    unify-subst ttree allp rw-cache-alist-new)))
       (relieve-hyp-ans

; As explained in the "SPECIAL CASE" comment in relieve-hyp, relieve-hyp
; returned (mv step-limit term typ unify-subst ttree allp).  We enter a loop in
; which we try to relieve the current hypothesis and subsequent hypotheses by
; instantiating the variables in term that are free with respect to
; unify-subst.

        (let* ((hyp (car hyps))
               (forcep1 (and (nvariablep hyp)
;                            (not (fquotep hyp))
                             (or (eq (ffn-symb hyp) 'force)
                                 (eq (ffn-symb hyp) 'case-split))))
               (forcer-fn (and forcep1 (ffn-symb hyp)))
               (hyp (if forcep1 (fargn hyp 1) (car hyps)))
               (force-flg (ok-to-force rcnst))
               (forcep (and forcep1 force-flg)))

; The following call of relieve-hyps1-free-1 will return an "activated" allp
; structure even if the current allp is t.  But if the current allp is t, then
; we are just now seeing our first free variable as we work our way through the
; hyps.  Since there is no search above us, there will be no further calls of
; relieve-hyps1 under the call of relieve-hyps that we are inside.  So, the
; returned value for allp is irrelevant if the current allp is t.

          (sl-let (relieve-hyps-ans failure-reason-lst unify-subst
                                    ttree allp rw-cache-alist-new)
                  (rewrite-entry
                   (relieve-hyps1-free-1 relieve-hyp-ans ; term
                                         failure-reason  ; typ
                                         hyp
                                         type-alist
                                         forcer-fn
                                         forcep
                                         force-flg
                                         rune target hyps
                                         backchain-limit-lst
                                         unify-subst bkptr
                                         unify-subst0
                                         ttree0
                                         (activate-memo allp)
                                         rw-cache-alist
                                         rw-cache-alist-new)
                   :obj nil :geneqv nil :pequiv-info nil ; all ignored
                   )
                  (mv step-limit relieve-hyps-ans
                      (and (null relieve-hyps-ans)
                           (cond ((null (f-get-global 'gstackp state))
                                  nil) ; save some conses
                                 (failure-reason-lst
                                  (list* bkptr
                                         'free-vars
                                         failure-reason-lst))
                                 (t ; There were no variable bindings.
                                  (list* bkptr 'free-vars 'hyp-vars
                                         (reverse
                                          (set-difference-assoc-eq
                                           (all-vars hyp)
                                           unify-subst))))))
                      unify-subst ttree allp rw-cache-alist-new))))
       (t (mv step-limit nil (cons bkptr failure-reason) unify-subst0
              (accumulate-rw-cache t new-ttree ttree0)
              allp rw-cache-alist-new))))))))

(defun relieve-hyps1-free-1
  (term typ hyp rest-type-alist forcer-fn forcep force-flg
        rune target hyps backchain-limit-lst
        unify-subst bkptr unify-subst0
        ttree0 allp rw-cache-alist rw-cache-alist-new ; &extra formals
        rdepth step-limit
        type-alist obj geneqv pequiv-info wrld state fnstack ancestors
        backchain-limit
        simplify-clause-pot-lst rcnst gstack
        ttree)

; WARNING: Keep this in sync with relieve-hyps1-unify-subst-lst.

; We search the type-alist in order to extend unify-subst so that a
; corresponding instance of term has type typ.  Then (with a call to
; relieve-hyps1-free-2) we search ground units in an attempt to extend
; unify-subst to make term true.

; We return seven values: a new step-limit, a relieve-hyps-ans, a
; failure-reason-lst that is a list of pairs (cons extended-unify-subst_i
; failure-reason_i), a unify-subst extending the given unify-subst, a ttree, a
; resulting allp, and an alist extending rw-cache-alist-new that will
; ultimately (in relieve-hyps) be merged into rw-cache-alist (and a
; corresponding alist for the "nil" cache).  Each failure-reason_i corresponds
; to the attempt to relieve hyps using extended-unify-subst_i, an extension of
; unify-subst.  The failure-reason-lst is used in
; tilde-@-failure-reason-free-phrase to explain why each attempt at extending
; the unify-subst failed to succeed, except if this list is empty, then a
; 'hyp-vars token is used in its place (see relieve-hyps1).

  (declare (ignore obj geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   7
   (signed-byte 30)
   (mv-let
    (ans new-unify-subst new-ttree new-rest-type-alist)
    (search-type-alist+ term typ rest-type-alist unify-subst ttree wrld)
    (cond
     (ans
      (mv-let
       (cached-failure-reason-free cached-failure-reason)
       (rw-cached-failure-pair new-unify-subst rw-cache-alist)
       (sl-let
        (relieve-hyps-ans failure-reason unify-subst1 ttree1 allp
                          inferior-rw-cache-alist-new)
        (cond
         (cached-failure-reason
          (mv step-limit nil
              (and (f-get-global 'gstackp state) ; cons optimization
                   (cons 'cached cached-failure-reason))
              unify-subst ttree allp nil))
         (t
          (rewrite-entry (relieve-hyps1 rune target (cdr hyps)
                                        (cdr backchain-limit-lst)
                                        new-unify-subst
                                        (1+ bkptr)
                                        unify-subst0 ttree0 allp
                                        (cdr cached-failure-reason-free)
                                        nil)
                         :obj nil :geneqv nil :pequiv-info nil ; all ignored
                         :ttree new-ttree)))
        (let ((rw-cache-alist-new
               (extend-rw-cache-alist-free rcnst
                                           new-unify-subst
                                           inferior-rw-cache-alist-new
                                           rw-cache-alist-new)))
          (cond
           (relieve-hyps-ans
            (mv step-limit relieve-hyps-ans nil unify-subst1 ttree1 allp
                rw-cache-alist-new))
           (t
            (let ((rw-cache-alist-new ; add normal-failure reason
                   (rw-cache-add-failure-reason rcnst
                                                new-unify-subst
                                                failure-reason
                                                rw-cache-alist-new)))
              (cond
               ((not allp) ; hence original allp is nil
                (mv step-limit nil
                    (and (f-get-global 'gstackp state) ; cons optimization
                         (list (cons new-unify-subst
                                     failure-reason)))
                    unify-subst0
                    (accumulate-rw-cache t ttree1 ttree0)
                    nil ; allp
                    rw-cache-alist-new))
               (t ; look for the next binding in the type-alist
                (rewrite-entry-extending-failure
                 new-unify-subst
                 failure-reason
                 (relieve-hyps1-free-1 term typ hyp new-rest-type-alist
                                       forcer-fn forcep force-flg
                                       rune target hyps
                                       backchain-limit-lst
                                       unify-subst
                                       bkptr
                                       unify-subst0 ttree0 allp
                                       rw-cache-alist rw-cache-alist-new)
                 :obj nil :geneqv nil :pequiv-info nil ; all ignored
                 :ttree (accumulate-rw-cache t ttree1 ttree)))))))))))
     (t ; failed to relieve hyp using rest-type-alist
      (rewrite-entry
       (relieve-hyps1-free-2 hyp
                             (relevant-ground-lemmas hyp wrld)
                             forcer-fn forcep
                             (access rewrite-constant rcnst
                                     :current-enabled-structure)
                             force-flg
                             rune target hyps
                             backchain-limit-lst
                             unify-subst
                             bkptr
                             unify-subst0 ttree0 allp
                             rw-cache-alist rw-cache-alist-new)
       :obj nil :geneqv nil :pequiv-info nil ; all ignored
       ))))))

(defun relieve-hyps1-free-2
    (hyp lemmas forcer-fn forcep ens force-flg
         rune target hyps backchain-limit-lst
         unify-subst bkptr unify-subst0
         ttree0 allp rw-cache-alist rw-cache-alist-new ; &extra formals
         rdepth step-limit
         type-alist obj geneqv pequiv-info wrld state fnstack ancestors
         backchain-limit
         simplify-clause-pot-lst rcnst gstack
         ttree)

; We search ground units in an attempt to extend unify-subst to make term true,
; As with relieve-hyps1-free-1, we return a relieve-hyps-ans, a
; failure-reason-lst that is a list of pairs (cons new-unify-subst
; failure-reason), a unify-subst extending the given unify-subst, a ttree, and
; a resulting allp.

  (declare (ignore obj geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

  (the-mv
   7
   (signed-byte 30)
   (cond
    ((endp lemmas)

; If we have to force this hyp, we make sure all its free vars are bound by
; fully-bound-unify-subst, an extension of unify-subst.

     (let ((fully-bound-unify-subst
            (if force-flg
                (bind-free-vars-to-unbound-free-vars
                 (all-vars hyp)
                 unify-subst)
              unify-subst)))
       (mv-let
         (force-flg ttree)
         (cond
          ((not forcep)
           (mv nil ttree))
          (t (force-assumption
              rune
              target
              (sublis-var fully-bound-unify-subst hyp)
              type-alist
              nil
              (immediate-forcep
               forcer-fn
               (access rewrite-constant rcnst
                       :current-enabled-structure))
              force-flg
              ttree)))
         (cond
          (force-flg
           (mv-let
             (cached-failure-reason-free cached-failure-reason)
             (rw-cached-failure-pair fully-bound-unify-subst rw-cache-alist)
             (cond
              (cached-failure-reason
               (mv step-limit nil
                   (and (f-get-global 'gstackp state) ; cons optimization
                        (list                         ; failure-reason-lst
                         (cons fully-bound-unify-subst
                               (cons 'cached cached-failure-reason))))
                   unify-subst0
                   (accumulate-rw-cache t ttree ttree0)
                   allp rw-cache-alist-new))
              (t
               (sl-let
                (relieve-hyps-ans failure-reason unify-subst1 ttree1 allp
                                  inferior-rw-cache-alist-new)
                (rewrite-entry
                 (relieve-hyps1 rune target (cdr hyps)
                                (cdr backchain-limit-lst)
                                fully-bound-unify-subst
                                (1+ bkptr)
                                unify-subst0 ttree0 allp
                                (cdr cached-failure-reason-free)
                                nil)
                 :obj nil :geneqv nil :pequiv-info nil ; all ignored
                 )
                (let ((rw-cache-alist-new
                       (extend-rw-cache-alist-free
                        rcnst
                        fully-bound-unify-subst
                        inferior-rw-cache-alist-new
                        rw-cache-alist-new)))
                  (cond (relieve-hyps-ans
                         (mv step-limit relieve-hyps-ans
                             nil ; failure-reason-lst
                             unify-subst1 ttree1 allp rw-cache-alist-new))
                        (t
                         (mv step-limit nil
                             (and (f-get-global 'gstackp state) ; cons optimization
                                  (list (cons fully-bound-unify-subst
                                              failure-reason)))
                             unify-subst0
                             (accumulate-rw-cache t ttree1 ttree0)
                             allp
                             (rw-cache-add-failure-reason
                              rcnst
                              fully-bound-unify-subst
                              failure-reason
                              rw-cache-alist-new))))))))))
          (t (mv step-limit nil
                 nil ; failure-reason-lst
                 unify-subst0
                 (accumulate-rw-cache t ttree ttree0)
                 allp rw-cache-alist-new))))))
    (t
     (mv-let
       (winp new-unify-subst new-ttree rest-lemmas)
       (search-ground-units1 hyp unify-subst lemmas type-alist ens force-flg
                             wrld ttree)
       (cond
        (winp
         (mv-let
           (cached-failure-reason-free cached-failure-reason)
           (rw-cached-failure-pair new-unify-subst rw-cache-alist)
           (sl-let
            (relieve-hyps-ans failure-reason unify-subst1 ttree1 allp
                              inferior-rw-cache-alist-new)
            (cond
             (cached-failure-reason
              (mv step-limit nil
                  (and (f-get-global 'gstackp state) ; cons optimization
                       (list                         ; failure-reason-lst
                        (cons new-unify-subst
                              (cons 'cached cached-failure-reason))))
                  unify-subst ttree allp nil))
             (t
              (rewrite-entry (relieve-hyps1 rune target (cdr hyps)
                                            (cdr backchain-limit-lst)
                                            new-unify-subst
                                            (1+ bkptr)
                                            unify-subst0 ttree0 allp
                                            (cdr cached-failure-reason-free)
                                            nil)
                             :obj nil :geneqv nil :pequiv-info nil ; all ignored
                             :ttree new-ttree)))
            (let ((rw-cache-alist-new
                   (extend-rw-cache-alist-free rcnst
                                               new-unify-subst
                                               inferior-rw-cache-alist-new
                                               rw-cache-alist-new)))
              (cond
               (relieve-hyps-ans
                (mv step-limit relieve-hyps-ans nil unify-subst1 ttree1 allp
                    rw-cache-alist-new))
               (t
                (let ((rw-cache-alist-new ; add normal-failure reason
                       (rw-cache-add-failure-reason rcnst
                                                    new-unify-subst
                                                    failure-reason
                                                    rw-cache-alist-new)))
                  (cond
                   ((not allp) ; hence original allp is nil
                    (mv step-limit nil
                        (and (f-get-global 'gstackp state) ; cons optimization
                             (list                         ; failure-reason-lst
                              (cons new-unify-subst
                                    failure-reason)))
                        unify-subst0
                        (accumulate-rw-cache t ttree1 ttree0)
                        nil rw-cache-alist-new))
                   (t
                    (rewrite-entry-extending-failure
                     new-unify-subst
                     failure-reason
                     (relieve-hyps1-free-2
                      hyp rest-lemmas forcer-fn forcep ens force-flg rune
                      target hyps backchain-limit-lst unify-subst bkptr
                      unify-subst0 ttree0 allp rw-cache-alist rw-cache-alist-new)
                     :obj nil :geneqv nil :pequiv-info nil ; all ignored
                     :ttree (accumulate-rw-cache t ttree1 ttree)))))))))))
        (t (rewrite-entry
            (relieve-hyps1-free-2
             hyp nil forcer-fn forcep ens force-flg rune
             target hyps backchain-limit-lst unify-subst bkptr
             unify-subst0 ttree0 allp rw-cache-alist rw-cache-alist-new)
            :obj nil :geneqv nil :pequiv-info nil ; all ignored
            ))))))))

(defun relieve-hyps (rune target hyps backchain-limit-lst
                          unify-subst allp ; &extra formals
                          rdepth step-limit
                          type-alist obj geneqv pequiv-info wrld state fnstack
                          ancestors backchain-limit
                          simplify-clause-pot-lst rcnst gstack ttree)

; We return t or nil indicating success, a token indicating why we failed (or
; nil if we succeeded), an extended unify-subst and a new ttree.  Allp is
; either t or nil, according to whether or not we are to attempt all free
; variable matches until we succeed.

; This function is a No-Change Loser modulo rw-cache: only the values of
; 'rw-cache-any-tag and 'rw-cache-nil-tag may differ between the input and
; output ttrees.

  (declare (ignore obj geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   5
   (signed-byte 30)
   (cond
    ((null hyps)

; For an empty list of hypotheses, there is no reason to consider the rw-cache
; at all, so we make a trivial successful return.  We rely on this in
; rewrite-with-lemma in the comment: "If hyps is nil, then relieve-hyps returns
; immediately with nil as the unifying substitution."

     (mv step-limit t nil unify-subst ttree))
    (t
     (let* ((ttree-saved ttree)
            (rw-cache-active-p (rw-cache-active-p rcnst))
            (cached-failure-entry
             (and rw-cache-active-p
                  (relieve-hyp-failure-entry rune unify-subst hyps ttree
                                             step-limit)))
            (cached-failure-reason-raw
             (and cached-failure-entry
                  (access rw-cache-entry cached-failure-entry :failure-reason)))
            (cached-failure-reason-free-p
             (and (consp cached-failure-reason-raw)
                  (free-failure-p cached-failure-reason-raw)))
            (cached-failure-reason-free
             (and cached-failure-reason-free-p
                  (equal (access rw-cache-entry cached-failure-entry
                                 :hyp-info)
                         hyps)
                  cached-failure-reason-raw))
            (cached-failure-reason
             (and (not cached-failure-reason-free-p)
                  cached-failure-reason-raw))
            (debug
             (and cached-failure-reason
                  (rw-cache-debug rune target unify-subst
                                  cached-failure-reason step-limit))))
       (cond
        ((and cached-failure-reason
              (not debug))
         (mv step-limit nil
             (and (f-get-global 'gstackp state) ; cons optimization
                  (cons 'cached cached-failure-reason))
             unify-subst ttree))
        (t (let ((step-limit-saved step-limit)
                 (unify-subst-saved unify-subst)
                 (old-rw-cache-alist (cdr cached-failure-reason-free)))
             (sl-let (relieve-hyps-ans failure-reason unify-subst ttree allp
                                       new-rw-cache-alist)
                     (rewrite-entry
                      (relieve-hyps1 rune target hyps backchain-limit-lst
                                     unify-subst 1 unify-subst ttree allp
                                     old-rw-cache-alist nil)
                      :obj nil :geneqv nil :pequiv-info nil ; all ignored

; If we are doing non-linear arithmetic, we will be rewriting linear
; terms under a different theory than the standard one.  However, when
; relieving hypotheses, we want to use the standard one, so we make
; sure that that is what we are using.

                      :rcnst
                      (if (eq (access rewrite-constant rcnst
                                      :active-theory)
                              :standard)
                          rcnst
                        (change rewrite-constant rcnst
                                :active-theory :standard)))
                     (declare (ignore allp))
                     (cond ((and debug relieve-hyps-ans)
                            (prog2$
                             (rw-cache-debug-action
                              rune target unify-subst-saved
                              cached-failure-reason step-limit-saved)
                             (mv step-limit nil cached-failure-reason
                                 unify-subst-saved ttree-saved)))
                           (t (mv step-limit relieve-hyps-ans failure-reason
                                  unify-subst
                                  (cond
                                   ((or relieve-hyps-ans
                                        backchain-limit
                                        (not rw-cache-active-p))
                                    ttree)
                                   (new-rw-cache-alist ; free vars case
                                    (note-relieve-hyps-failure-free
                                     rune unify-subst hyps
                                     ttree
                                     cached-failure-entry
                                     old-rw-cache-alist
                                     new-rw-cache-alist

; At one time we only saved the step-limit in debug mode, so that when we merge
; rw-caches after calls of cons-tag-trees, we avoid essentially duplicated
; rw-cache-entry records, differing only in their :step-limit fields.  However,
; we now save the step-limit unconditionally, because we may be calling
; merge-lexorder-fast a lot and the :step-limit field of a rw-cache-entry
; record can give a quick result.  The potential for rare duplication seems
; harmless.

                                     step-limit-saved))
                                   (t

; We cache the rewriting failure into the ttree.  It would be a mistake to
; extend the rw-cache if there is a backchain-limit, because a later lookup
; might be made with a different backchain-limit.  This may be why
; Prime-property-lemma, in community book
; workshops/2006/cowles-gamboa-euclid/Euclid/ed3.lisp, fails with
; :rw-cache-state :atom.

                                    (note-relieve-hyp-failure
                                     rune unify-subst failure-reason
                                     ttree hyps

; See comment above about regarding our formerly saving the step-limit only in
; debug mode.

                                     step-limit-saved)))))))))))))))

(defun rewrite-with-lemma (term lemma ; &extra formals
                                rdepth step-limit
                                type-alist obj geneqv pequiv-info wrld state
                                fnstack ancestors
                                backchain-limit
                                simplify-clause-pot-lst rcnst gstack
                                ttree)

; The four values returned by this function are: a new step-limit, t or nil
; indicating whether lemma was used to rewrite term, the rewritten version of
; term, and the final version of ttree.

; This function is a No-Change Loser modulo rw-cache: only the values of
; 'rw-cache-any-tag and 'rw-cache-nil-tag may differ between the input and
; output ttrees.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   4
   (signed-byte 30)
   (let ((gstack (push-gframe 'rewrite-with-lemma nil term lemma))
         (rdepth (adjust-rdepth rdepth)))
     (declare (type (unsigned-byte 29) rdepth))
     (cond ((zero-depthp rdepth)
            (rdepth-error
             (mv step-limit nil term ttree)))
           ((eq (access rewrite-rule lemma :subclass) 'meta)

; See the Essay on Correctness of Meta Reasoning, above, and :doc meta.

            (cond
             ((geneqv-refinementp (access rewrite-rule lemma :equiv)
                                  geneqv
                                  wrld)

; We assume that the meta function has defun-mode :logic.  How could it
; be :program if we proved it correct?

; Metafunctions come in two flavors.  Vanilla metafunctions take just
; one arg, the term to be rewritten.  Extended metafunctions take
; three args.  We cons up the args here and use this list of args
; twice below, once to eval the metafunction and once to eval the hyp
; fn.  The :rhs of the rewrite-rule is the special flag 'extended
; if we are in the extended case; otherwise, :rhs is nil.  We must
; manufacture a context in the former case.

              (let* ((meta-fn (access rewrite-rule lemma :lhs))
                     (args
                      (cond
                       ((eq (access rewrite-rule lemma :rhs)
                            'extended)
                        (list term
                              (make metafunction-context
                                    :rdepth rdepth
                                    :type-alist type-alist
                                    :obj obj
                                    :geneqv geneqv
                                    :wrld wrld
                                    :fnstack fnstack
                                    :ancestors ancestors
                                    :backchain-limit backchain-limit
                                    :simplify-clause-pot-lst
                                    simplify-clause-pot-lst
                                    :rcnst rcnst
                                    :gstack gstack
                                    :ttree ttree
                                    :unify-subst nil)
                              (coerce-state-to-object state)))
                       (t (list term))))
                     (rune (access rewrite-rule lemma :rune)))
                (with-accumulated-persistence
                 rune
                 ((the (signed-byte 30) step-limit) flg term ttree)
                 flg
                 (mv-let
                  (erp val latches)
                  (pstk
                   (ev-fncall-meta meta-fn args state))
                  (declare (ignore latches))
                  (cond
                   (erp
                    (mv step-limit nil term ttree))
                   ((equal term val)
                    (mv step-limit nil term ttree))
                   (t

; Skip logic-termp checks if either we're told to via skip-meta-termp-checks
; or they are unnecessary because of the meta fn (and its hyp-fn) have
; well-formedness guarantees.  If we skip the checks because of guarantees, we
; must check the arity assumptions.

                    (let* ((user-says-skip-termp-checkp
                            (skip-meta-termp-checks meta-fn wrld))
                           (well-formedness-guarantee
                            (access rewrite-rule lemma :heuristic-info))
                           (not-skipped
                            (and (not user-says-skip-termp-checkp)
                                 (not well-formedness-guarantee)))
                           (bad-arity-info
                            (if (and well-formedness-guarantee
                                     (not user-says-skip-termp-checkp))
                                (collect-bad-fn-arity-info
                                 (cdr well-formedness-guarantee)
                                 wrld nil nil)
                              nil)))
                      (cond
                       (bad-arity-info
                        (let ((name (nth 0 (car well-formedness-guarantee)))
                              (fn (nth 1 (car well-formedness-guarantee)))
                              (thm-name1
                               (nth 2 (car well-formedness-guarantee)))
                              (hyp-fn (nth 3 (car well-formedness-guarantee)))
                              (thm-name2
                               (nth 4 (car well-formedness-guarantee))))
                          (mv step-limit
                              (er hard 'rewrite-with-lemma
                                  "~@0"
                                  (bad-arities-msg name :META fn hyp-fn
                                                   thm-name1 thm-name2
                                                   bad-arity-info))
                              term ttree)))
; Check logic-termp by checking both termp and (not (program-termp)).
                       ((and not-skipped
                             (not (termp val wrld)))
                        (mv step-limit
                            (er hard 'rewrite-with-lemma
                                "The metafunction ~x0 produced the non-termp ~
                                 ~x1 on the input term ~x2. The proof of the ~
                                 correctness of ~x0 establishes that the ~
                                 quotations of these two s-expressions have ~
                                 the same value, but our implementation ~
                                 additionally requires that ~x0 produce a ~
                                 term.  See :DOC termp.  You might consider ~
                                 proving a well-formedness guarantee to avoid ~
                                 this runtime test altogether.  See :DOC ~
                                 well-formedness-guarantee."
                                meta-fn val term)
                            term ttree))
                       ((and not-skipped
                             (not (logic-termp val wrld)))
                        (mv step-limit
                            (er hard 'rewrite-with-lemma
                                "The metafunction ~x0 produced the termp ~x1 ~
                                 on the input term ~x2.  The proof of the ~
                                 correctness of ~x0 establishes that the ~
                                 quotations of these two s-expressions have ~
                                 the same value, but our implementation ~
                                 additionally requires that ~x0 produce a ~
                                 term with no :program mode function symbols. ~
                                 ~ The term produced has :program mode ~
                                 function symbol~#3~[~/s~] ~&3.  You might ~
                                 consider proving a well-formedness guarantee ~
                                 to avoid this runtime test altogether.  See ~
                                 :DOC well-formedness-guarantee."
                                meta-fn val term
                                (collect-programs (all-ffn-symbs val nil)
                                                  wrld))
                            term ttree))
                       ((and not-skipped
                             (forbidden-fns-in-term
                              val
                              (access rewrite-constant rcnst :forbidden-fns)))
                        (mv step-limit
                            (er hard 'rewrite-with-lemma
                                "The metafunction ~x0 produced the termp ~x1 ~
                                 on the input term ~x2.  The proof of the ~
                                 correctness of ~x0 establishes that the ~
                                 quotations of these two s-expressions have ~
                                 the same value, but our implementation ~
                                 additionally requires that certain forbidden ~
                                 function symbols not be called.  However, ~
                                 the forbidden function symbol~#3~[ ~&3 is~/s ~
                                 ~&3 are~] called in the term produced by ~
                                 ~x0.  See :DOC meta and :DOC ~
                                 set-skip-meta-termp-checks and :DOC ~
                                 well-formedness-guarantee."
                                meta-fn val term
                                (forbidden-fns-in-term
                                 val
                                 (access rewrite-constant rcnst :forbidden-fns)))
                            term ttree))
                       (t
                        (mv-let
                         (extra-evaled-hyp val)
                         (cond ((and (ffn-symb-p val 'if)
                                     (equal (fargn val 3) term))
                                (mv (fargn val 1) (fargn val 2)))
                               (t (mv *t* val)))
                         (let ((hyp-fn (access rewrite-rule lemma :hyps)))
                           (mv-let
                            (erp evaled-hyp latches)
                            (if (eq hyp-fn nil)
                                (mv nil *t* nil)
                              (pstk
                               (ev-fncall-meta hyp-fn args state)))
                            (declare (ignore latches))
                            (cond
                             (erp
                              (mv step-limit nil term ttree))
                             (t
                              (let* ((user-says-skip-termp-checkp
                                      (skip-meta-termp-checks hyp-fn wrld))
;                                    (well-formedness-guarantee  ; already bound
;                                     (access rewrite-rule lemma
;                                             :heuristic-info))
                                     (not-skipped
                                      (and (not user-says-skip-termp-checkp)
                                           (not well-formedness-guarantee)))

; It is easy to think that it is unnecessary to do this computation and binding
; because the non-nil result will be exactly the same as it was above
; (depending as it does only on the guarantee and the wrld) and we have already
; (above) checked and caused an error if it is non-nil.  But that reasoning is
; faulty.  Suppose the user told us to skip the termp check on metafn's output
; but to do the check on hyp-fn's output.  Then the earlier binding of
; bad-arity-info is nil but this binding may find something.

                                     (bad-arity-info
                                      (if (and
                                           well-formedness-guarantee
                                           (not user-says-skip-termp-checkp))
                                          (collect-bad-fn-arity-info
                                           (cdr well-formedness-guarantee)
                                           wrld nil nil)
                                        nil)))
                                (cond
                                 (bad-arity-info
                                  (let ((name
                                         (nth 0
                                              (car well-formedness-guarantee)))
                                        (hyp-fn
                                         (nth 3
                                              (car well-formedness-guarantee)))
                                        (thm-name2
                                         (nth 4
                                              (car well-formedness-guarantee))))
                                    (mv step-limit
                                        (er hard 'rewrite-with-lemma
                                            "~@0"
                                            (bad-arities-msg name
                                                             :META
                                                             nil ; fn
                                                             hyp-fn
                                                             thm-name2
                                                             nil
                                                             bad-arity-info))
                                        term ttree)))
                                 ((and not-skipped
                                       (not (termp evaled-hyp wrld)))
                                  (mv step-limit
                                      (er hard 'rewrite-with-lemma
                                          "The hypothesis metafunction ~x0 ~
                                           produced the non-termp ~x1 on the ~
                                           input term ~x2.  Our ~
                                           implementation requires that ~x0 ~
                                           produce a term.  See :DOC termp.  ~
                                           You might consider proving a ~
                                           well-formedness guarantee.  See ~
                                           :DOC well-formedness-guarantee to ~
                                           avoid this runtime check ~
                                           altogether.  See :DOC ~
                                           well-formedness-guarantee."
                                          hyp-fn evaled-hyp term)
                                      term ttree))
                                 ((and not-skipped
                                       (not (logic-termp evaled-hyp wrld)))
                                  (mv step-limit
                                      (er hard 'rewrite-with-lemma
                                          "The hypothesis metafunction ~x0 ~
                                           produced the termp ~x1 on the ~
                                           input term ~x2.  The proof of the ~
                                           correctness of ~x0 establishes ~
                                           that the quotations of these two ~
                                           s-expressions have the same value, ~
                                           but our implementation ~
                                           additionally requires that ~x0 ~
                                           produce a term with no :program ~
                                           mode function symbols.  The term ~
                                           produced has :program mode ~
                                           function symbol~#3~[~/s~] ~&3.  ~
                                           You might consider proving a ~
                                           well-formedness guarantee to avoid ~
                                           this runtime test altogether.  See ~
                                           :DOC well-formedness-guarantee."
                                          hyp-fn evaled-hyp term
                                          (collect-programs
                                           (all-ffn-symbs evaled-hyp nil)
                                           wrld))
                                      term ttree))
                                 ((and not-skipped
                                       (forbidden-fns-in-term
                                        evaled-hyp
                                        (access rewrite-constant rcnst
                                                :forbidden-fns)))
                                  (mv step-limit
                                      (er hard 'rewrite-with-lemma
                                          "The hypothesis metafunction ~x0 ~
                                           produced the termp ~x1 on the ~
                                           input term ~x2.  Our ~
                                           implementation additionally ~
                                           requires that certain forbidden ~
                                           function symbols not be called.  ~
                                           However, the forbidden function ~
                                           symbol~#3~[ ~&3 is~/s ~&3 are~] ~
                                           called in the term produced by ~
                                           ~x0.  See :DOC meta and :DOC ~
                                           set-skip-meta-termp-checks and ~
                                           :DOC well-formedness-guarantee."
                                          hyp-fn evaled-hyp term
                                          (forbidden-fns-in-term
                                           evaled-hyp
                                           (access rewrite-constant rcnst
                                                   :forbidden-fns)))
                                      term ttree))
                                 (t
                                  (let* ((hyps0 (flatten-ands-in-lit

; Note: The quote-normal-form call below normalizes the explicit constant
; constructors, e.g., (cons '1 '2) becomes '(1 . 2).  See the comment in
; extend-unify-subst.

                                                 (quote-normal-form
                                                  evaled-hyp)))
                                         (extra-hyps (flatten-ands-in-lit

; Note: The quote-normal-form call below normalizes the explicit constant
; constructors, e.g., (cons '1 '2) becomes '(1 . 2).  See the comment in
; extend-unify-subst.

                                                 (quote-normal-form
                                                  extra-evaled-hyp)))
                                         (hyps (append? hyps0 extra-hyps))
                                         (vars (and hyps

; We avoid the cost of computing (all-vars term) when there are no hypotheses
; (which is presumably a common case).  We have seen this reduce an event's
; processing time from 67 seconds to 19 seconds.

                                                    (all-vars term)))
                                         (rule-backchain-limit
                                          (access rewrite-rule lemma
                                                  :backchain-limit-lst))
                                         (bad-synp-hyp-msg
                                          (and hyps0

; Vars should be (all-vars term) if we call bad-synp-hyp-msg, but if hyps0 is
; nil then bad-synp-hyp-msg returns nil regardless of vars, so we avoid calling
; it.

                                               (bad-synp-hyp-msg hyps0 vars nil
                                                                 wrld)))
                                         (bad-synp-hyp-msg-extra
                                          (and extra-hyps ; optimize, as above
                                               (bad-synp-hyp-msg extra-hyps
                                                                 vars nil
                                                                 wrld))))
                                    (cond
                                     (bad-synp-hyp-msg
                                      (mv step-limit
                                          (er hard 'rewrite-with-lemma
                                              "The hypothesis metafunction ~
                                               ~x0, when applied to the input ~
                                               term ~x1, produced a term ~
                                               whose use of synp is illegal ~
                                               because ~@2"
                                              hyp-fn term bad-synp-hyp-msg)
                                          term ttree))
                                     (bad-synp-hyp-msg-extra
                                      (mv step-limit
                                          (er hard 'rewrite-with-lemma
                                              "The metafunction ~x0, when ~
                                               applied to the input term ~x1, ~
                                               produced a term with an ~
                                               implicit hypothesis (see :DOC ~
                                               meta-implicit-hypothesis), ~
                                               whose use of synp is illegal ~
                                               because ~@2"
                                              meta-fn term
                                              bad-synp-hyp-msg-extra)
                                          term ttree))
                                     (t
                                      (sl-let
                                       (relieve-hyps-ans failure-reason
                                                         unify-subst
                                                         ttree)
                                       (rewrite-entry
                                        (relieve-hyps

; The next argument of relieve-hyps is a rune on which to "blame" a
; possible force.  We could blame such a force on a lot of things, but
; we'll blame it on the metarule and the term that it's applied to.

                                         rune
                                         term
                                         hyps
                                         (and rule-backchain-limit
                                              (assert$
                                               (natp rule-backchain-limit)
                                               (make-list
                                                (length hyps)
                                                :initial-element
                                                rule-backchain-limit)))

; The meta function has rewritten term to val and has generated a
; hypothesis called evaled-hyp.  Now ignore the metafunction and just
; imagine that we have a rewrite rule (implies evaled-hyp (equiv term
; val)).  The unifying substitution just maps the vars of term to
; themselves.  There may be additional vars in both evaled-hyp and in
; val.  But they are free at the time we do this relieve-hyps.

; If hyps is nil, then relieve-hyps returns immediately with nil as the
; unifying substitution.  That's OK, as explained in a comment below ("At one
; point we ignored the unify-subst....").

                                         (and hyps
                                              (pairlis$ vars vars))
                                         nil ; allp=nil for meta rules
                                         )
                                        :obj nil         ; ignored
                                        :geneqv nil      ; ignored
                                        :pequiv-info nil ; ignored
                                        )

; If relieve hyps succeeds we get back a unifying substitution that extends
; the identity substitution above.  This substitution might bind free vars
; in the evaled-hyp.

; Why are we ignoring failure-reason?  Do we need to be calling one of the
; brkpt functions?  No, because we don't break on meta rules.  But perhaps we
; should consider allowing breaks on meta rules.

                                       (declare (ignore failure-reason))
                                       (cond
                                        (relieve-hyps-ans
                                         (sl-let
                                          (rewritten-rhs ttree)
                                          (with-accumulated-persistence
                                           rune
                                           ((the (signed-byte 30) step-limit)
                                            rewritten-rhs ttree)

; This rewrite of the body is considered a success unless the parent with-acc-p
; fails.

                                           t
                                           (rewrite-entry (rewrite

; Note: The quote-normal-form call below normalizes the explicit constant
; constructors, e.g., (cons '1 '2) becomes '(1 . 2).  See the comment in
; extend-unify-subst.

                                                 (quote-normal-form val)

; At one point we ignored the unify-subst constructed above and used a nil
; here.  That was unsound if val involved free vars bound by the relief of the
; evaled-hyp.  We must rewrite val under the extended substitution.  Often that
; is just the identity substitution.  If there are no hypotheses, however, then
; there are no such free vars, so it is fine to rewrite with nil as the
; unify-subst.

                                                           unify-subst
                                                           'meta))
                                           :conc
                                           hyps)
                                          (mv step-limit t rewritten-rhs

; Should we be pushing executable-counterparts into ttrees when we applying
; metafunctions on behalf of meta rules?  NO:  We should only do that if the
; meta-rule's use is sensitive to whether or not they're enabled, and it's not
; -- all that matters is if the rule itself is enabled.

                                              (push-lemma
                                               (geneqv-refinementp
                                                (access rewrite-rule lemma
                                                        :equiv)
                                                geneqv
                                                wrld)
                                               (push-lemma+ rune ttree rcnst ancestors
                                                            val rewritten-rhs)))))
                                        (t (mv step-limit nil term ttree))))))))))))))))))))))))
             (t (mv step-limit nil term ttree))))
           ((not (geneqv-refinementp (access rewrite-rule lemma :equiv)
                                     geneqv
                                     wrld))
            (mv step-limit nil term ttree))
           ((eq (access rewrite-rule lemma :subclass) 'definition)
            (sl-let (rewritten-term ttree)
                    (rewrite-entry (rewrite-fncall lemma term))
                    (mv step-limit
                        (not (equal term rewritten-term))
                        rewritten-term
                        ttree)))
           ((and (or (null (access rewrite-rule lemma :hyps))
                     (not (eq obj t))
                     (not (equal (access rewrite-rule lemma :rhs) *nil*)))
                 (or (flambdap (ffn-symb term)) ; hence not on fnstack
                     (not (being-openedp (ffn-symb term)
                                         fnstack
                                         (recursivep (ffn-symb term) t wrld)
                                         (eq (access rewrite-constant rcnst
                                                     :rewriter-state)
                                             'settled-down)))
                     (not (ffnnamep (ffn-symb term)
                                    (access rewrite-rule lemma :rhs)))))
            (let ((lhs (access rewrite-rule lemma :lhs))
                  (rune (access rewrite-rule lemma :rune)))
              (mv-let (unify-ans unify-subst)
                      (one-way-unify-restrictions
                       lhs
                       term
                       (cdr (assoc-equal
                             rune
                             (access rewrite-constant rcnst
                                     :restrictions-alist))))
                      (cond
                       ((and unify-ans
                             (null (brkpt1 lemma term unify-subst
                                           type-alist ancestors
                                           ttree
                                           gstack rcnst state)))
                        (cond
                         ((null (loop-stopperp
                                 (access rewrite-rule lemma :heuristic-info)
                                 unify-subst
                                 wrld))
                          (prog2$
                           (brkpt2 nil 'loop-stopper
                                   unify-subst gstack nil nil
                                   rcnst state)
                           (mv step-limit nil term ttree)))
                         (t
                          (with-accumulated-persistence
                           rune
                           ((the (signed-byte 30) step-limit) flg term ttree)
                           flg
                           (sl-let
                            (relieve-hyps-ans failure-reason unify-subst ttree)
                            (rewrite-entry
                             (relieve-hyps
                              rune
                              term
                              (access rewrite-rule lemma :hyps)
                              (access rewrite-rule lemma
                                      :backchain-limit-lst)
                              unify-subst
                              (not (oncep (access rewrite-constant
                                                  rcnst
                                                  :oncep-override)
                                          (access rewrite-rule
                                                  lemma
                                                  :match-free)
                                          rune
                                          (access rewrite-rule
                                                  lemma
                                                  :nume))))
                             :obj nil         ; ignored
                             :geneqv nil      ; ignored
                             :pequiv-info nil ; ignored
                             )
                            (cond
                             (relieve-hyps-ans
                              (sl-let
                               (rewritten-rhs ttree)
                               (with-accumulated-persistence
                                rune
                                ((the (signed-byte 30) step-limit)
                                 rewritten-rhs ttree)

; This rewrite of the body is considered a success unless the parent with-acc-p
; fails.

                                t
                                (rewrite-entry
                                 (rewrite
                                  (access rewrite-rule lemma :rhs)
                                  unify-subst
                                  'rhs))
                                :conc
                                (access rewrite-rule lemma :hyps))
                               (prog2$
                                (brkpt2 t nil unify-subst gstack rewritten-rhs
                                        ttree rcnst state)
                                (mv step-limit t rewritten-rhs
                                    (push-lemma
                                     (geneqv-refinementp
                                      (access rewrite-rule lemma
                                              :equiv)
                                      geneqv
                                      wrld)
                                     (push-lemma+ rune ttree rcnst ancestors
                                                  (access rewrite-rule lemma
                                                          :rhs)
                                                  rewritten-rhs))))))
                             (t (prog2$
                                 (brkpt2 nil failure-reason
                                         unify-subst gstack nil nil
                                         rcnst state)
                                 (mv step-limit nil term ttree)))))))))
                       (t (mv step-limit nil term ttree))))))
           (t (mv step-limit nil term ttree))))))

(defun rewrite-with-lemmas1 (term lemmas
                                  ;;; &extra formals
                                  rdepth step-limit
                                  type-alist obj geneqv pequiv-info wrld state
                                  fnstack ancestors
                                  backchain-limit
                                  simplify-clause-pot-lst rcnst gstack ttree)

; Try to rewrite term with the lemmas in lemmas.  Return t or nil indicating
; success, the rewritten term, and the final ttree.

; This function is a No-Change Loser modulo rw-cache: only the values of
; 'rw-cache-any-tag and 'rw-cache-nil-tag may differ between the input and
; output ttrees.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   4
   (signed-byte 30)
   (cond ((null lemmas) (mv step-limit nil term ttree))

; When we are doing non-linear we will be rewriting linear terms
; under a different theory than the standard one.  The :active-theory
; field of the rcnst keeps track of which theory we are using.

         ((if (eq (access rewrite-constant rcnst :active-theory)
                  :standard)
              (not (enabled-numep
                    (access rewrite-rule (car lemmas) :nume)
                    (access rewrite-constant rcnst
                            :current-enabled-structure)))
            (not (enabled-arith-numep
                  (access rewrite-rule (car lemmas) :nume)
                  (global-val 'global-arithmetic-enabled-structure wrld))))
          (rewrite-entry (rewrite-with-lemmas1 term (cdr lemmas))))
         (t (sl-let
             (rewrittenp rewritten-term ttree)
             (rewrite-entry (rewrite-with-lemma term (car lemmas)))
             (cond (rewrittenp
                    (mv step-limit t rewritten-term ttree))
                   (t (rewrite-entry
                       (rewrite-with-lemmas1 term (cdr lemmas))))))))))

(defun rewrite-fncall (rule term ; &extra formals
                       rdepth step-limit
                       type-alist obj geneqv pequiv-info wrld state fnstack
                       ancestors backchain-limit
                       simplify-clause-pot-lst rcnst gstack ttree)

; Rule is a :REWRITE rule of subclass DEFINITION or else it is nil.  Rule is
; nil iff term is a lambda application.  The three values returned by this
; function are the new step-limit, the (possibly) rewritten term, and the new
; ttree.  We assume rule is enabled.

; Term is of the form (fn . args).

; Nqthm Discrepancy: In nqthm, the caller of rewrite-fncall,
; rewrite-with-lemmas, would ask whether the result was different from term and
; whether it contained rewritable calls.  If so, it called the rewriter on the
; result.  We have changed that here so that rewrite-fncall, in the case that
; it is returning the expanded body, asks about rewritable calls and possibly
; calls rewrite again.  In the implementation below we ask about rewritable
; calls only for recursively defined fns.  The old code asked the question on
; all expansions.  It is possible the old code sometimes found a rewritable
; call of a non-recursive fn in the expansion of that fn's body because of uses
; of that fn in the arguments.  So this is a possible difference between ACL2
; and nqthm, although we have no reason to believe it is significant and we do
; it only for recursive fns simply because the non-recursive case seems
; unlikely.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   3
   (signed-byte 30)
   (let* ((fn (ffn-symb term))
          (args (fargs term))
          (body (if (null rule)
                    (or (lambda-body fn)
                        (er hard 'rewrite-fncall
                            "We had thought that a lambda function symbol ~
                             always has a non-nil lambda-body, but the ~
                             following lambda does not: ~x0"
                            fn))
                  (or (access rewrite-rule rule :rhs)
                      "We had thought that a rewrite-rule always has a non-nil ~
                      :rhs, but the following rewrite rule does not: ~x0")))
          (recursivep (and rule ; it's a don't-care if (flambdap fn)
                           (car (access rewrite-rule rule :heuristic-info)))))
     (cond ((and (not (flambdap fn))
                 (or (being-openedp fn fnstack recursivep
                                    (eq (access rewrite-constant rcnst
                                                :rewriter-state)
                                        'settled-down))
                     (fnstack-term-member term fnstack)
                     (and recursivep
                          (member-eq :rewrite-lambda-object fnstack))))
            (prepend-step-limit
             2
             (rewrite-solidify term type-alist obj geneqv
                               (access rewrite-constant rcnst
                                       :current-enabled-structure)
                               wrld ttree
                               simplify-clause-pot-lst
                               (access rewrite-constant rcnst :pt))))
           ((null rule) ; i.e., (flambdap fn)
            (cond
             ((and (not (recursive-fn-on-fnstackp fnstack))
                   (too-many-ifs-pre-rewrite args
                                             (var-counts (lambda-formals fn)
                                                         body)))
              (prepend-step-limit
               2
               (rewrite-solidify term type-alist obj geneqv
                                 (access rewrite-constant rcnst
                                         :current-enabled-structure)
                                 wrld ttree
                                 simplify-clause-pot-lst
                                 (access rewrite-constant rcnst :pt))))
             (t
              (sl-let
               (rewritten-body ttree1)
               (rewrite-entry (rewrite body
                                       (pairlis$ (lambda-formals fn) args)
                                       'lambda-body)
                              :fnstack fnstack)

; Observe that we do not put the lambda-expression onto the fnstack.
; We act just as though we were rewriting a term under a substitution.
; But we do decide on heuristic grounds whether to keep the expansion.
; See the handling of non-recursive functions below for some comments
; relating to the too-many-ifs code.

; Note: If the handling of lambda-applications is altered, consider
; their handling in both rewrite-fncallp (where we take advantage of
; the knowledge that lambda-expressions will not occur in rewritten
; bodies unless the user has explicitly prevented us from opening
; them) and contains-rewritable-callp.

               (cond
                ((and (not (recursive-fn-on-fnstackp fnstack))
                      (too-many-ifs-post-rewrite args rewritten-body))
                 (prepend-step-limit
                  2
                  (rewrite-solidify term type-alist obj geneqv
                                    (access rewrite-constant rcnst
                                            :current-enabled-structure)
                                    wrld
                                    (accumulate-rw-cache t ttree1 ttree)
                                    simplify-clause-pot-lst
                                    (access rewrite-constant rcnst :pt))))
                (t (mv step-limit rewritten-body ttree1)))))))
           (t
            (let* ((new-fnstack (cons (or recursivep fn) fnstack))
                   (rune (access rewrite-rule rule :rune)))
              (mv-let
               (unify-ans unify-subst)
               (one-way-unify-restrictions
                (access rewrite-rule rule :lhs)
                term
                (cdr (assoc-equal
                      rune
                      (access rewrite-constant rcnst
                              :restrictions-alist))))
               (cond
                ((and unify-ans
                      (null (brkpt1 rule term unify-subst type-alist ancestors
                                    ttree gstack rcnst state)))
                 (with-accumulated-persistence
                  (access rewrite-rule rule :rune)
                  ((the (signed-byte 30) step-limit) term-out ttree)

; The following mis-guarded use of eq instead of equal implies that we could be
; over-counting successes at the expense of failures.

                  (not (eq term term-out))
                  (cond
                   ((and (null recursivep)
                         (not (recursive-fn-on-fnstackp fnstack))
                         (too-many-ifs-pre-rewrite args
                                                   (access rewrite-rule rule
                                                           :var-info)))

; We are dealing with a nonrecursive fn.  If we are at the top-level of the
; clause but the expanded body has too many IFs in it compared to the number
; in the args, we do not use the expanded body.  We know the IFs in
; the args will be clausified out soon and then this will be permitted to
; open.

                    (prog2$
                     (brkpt2 nil 'too-many-ifs-pre-rewrite unify-subst gstack
                             :rewriten-rhs-avoided ttree rcnst state)
                     (prepend-step-limit
                      2
                      (rewrite-solidify term type-alist obj geneqv
                                        (access rewrite-constant rcnst
                                                :current-enabled-structure)
                                        wrld ttree
                                        simplify-clause-pot-lst
                                        (access rewrite-constant rcnst
                                                :pt)))))
                   (t
                    (sl-let
                     (relieve-hyps-ans failure-reason unify-subst ttree1)
                     (cond
                      ((and (eq fn (base-symbol rune))

; There may be alternative definitions of fn.  "The" definition is the one
; whose rune is of the form (:DEFINITION fn); its hyps is nil, at least in the
; standard case; but:

                            #+:non-standard-analysis

; In the non-standard case, we may be attempting to open up a call of a
; function defined by defun-std.  Hence, there may be one or more hypotheses.

                            (not (access rewrite-rule rule :hyps)))
                       (mv step-limit t nil unify-subst ttree))
                      (t (rewrite-entry
                          (relieve-hyps rune term
                                        (access rewrite-rule rule :hyps)
                                        nil ; backchain-limit-lst
                                        unify-subst
                                        nil ; allp=nil for definitions
                                        )
                          :obj nil :geneqv nil :pequiv-info nil ; all ignored
                          )))
                     (cond
                      (relieve-hyps-ans
                       (with-accumulated-persistence
                        rune
                        ((the (signed-byte 30) step-limit) term-out ttree)
                        t ; considered a success unless the parent with-acc-p fails
                        (sl-let
                         (rewritten-body new-ttree1)
                         (rewrite-entry (rewrite body unify-subst 'body)
                                        :fnstack new-fnstack
                                        :ttree ttree1)

; Again, we use ttree1 to accumulate the successful rewrites and we'll
; return it in our answer if we like our answer.

                         (let ((ttree1 (restore-rw-cache-any-tag new-ttree1
                                                                 ttree1)))
                           (cond
                            ((null recursivep)

; We are dealing with a nonrecursive fn.  If we are at the top-level of the
; clause but the expanded body has too many IFs in it compared to the number
; in the args, we do not use the expanded body.  We know the IFs in
; the args will be clausified out soon and then this will be permitted to
; open.

                             (cond
                              ((and (not (recursive-fn-on-fnstackp fnstack))
                                    (too-many-ifs-post-rewrite args
                                                               rewritten-body))
                               (prog2$
                                (brkpt2 nil 'too-many-ifs-post-rewrite
                                        unify-subst gstack rewritten-body
                                        ttree1 rcnst state)
                                (prepend-step-limit
                                 2
                                 (rewrite-solidify
                                  term type-alist obj geneqv
                                  (access rewrite-constant rcnst
                                          :current-enabled-structure)
                                  wrld
                                  (accumulate-rw-cache t ttree1 ttree)
                                  simplify-clause-pot-lst
                                  (access rewrite-constant rcnst :pt)))))
                              (t (prog2$
                                  (brkpt2 t nil unify-subst gstack
                                          rewritten-body ttree1 rcnst state)
                                  (mv step-limit
                                      rewritten-body
                                      (push-lemma+ rune ttree1 rcnst ancestors
                                                   body rewritten-body))))))
                            ((rewrite-fncallp
                              term rewritten-body
                              (if (cdr recursivep) recursivep nil)
                              (access rewrite-constant rcnst
                                      :top-clause)
                              (access rewrite-constant rcnst
                                      :current-clause)
                              (cdr (access rewrite-rule rule :heuristic-info)))
                             (cond

; Once upon a time, before we were heavily involved with ACL2 proofs, we had
; the following code here.  Roughly speaking this code forced recursive
; functions to open one step at a time if they introduced any IFs.

;                           ((ffnnamep 'if rewritten-body)

; Nqthm Discrepancy: This clause is new to ACL2.  Nqthm always rewrote the
; rewritten body if it contained rewritable calls.  This allows Nqthm to open
; up (member x '(a b c d e)) to a 5-way case split in "one" apparent rewrite.
; In an experiment I have added the proviso above, which avoids rewriting the
; rewritten body if it contains an IF.  This effectively slows down the opening
; of member, forcing the whole theorem back through the simplifier on each
; opening.  Eventually it will open completely, even under this rule.  The
; thought, though, is that often the case splits introduced by such openings
; seems to be irrelevant.  Under this new rule, (length (list a b c d e)) will
; expand in one step to '5, but the member expression above will expand more
; slowly because the expansion introduces a case split.  An experiment was done
; with Nqthm-1992 in which this change was introduced and examples/basic/
; proveall.events was replayed without any trouble and with no apparent
; performance change.  There are undoubtedly example files where this change
; will slow things down.  But it was motivated by an example in which it speeds
; things up by a factor of 10 because the opening is totally irrelevant to the
; proof.  The problem -- which was illustrated in the guard proofs for the
; function ascii-code-lst in the nqthm.lisp events -- is that (member x
; *standard-chars*) opens into a 96-way case split in a situation in which it
; could as well have been disabled.  This happens more in ACL2 than in Nqthm
; because of the presence of defconsts which permit big constants to be fed
; to recursive functions.  It is not clear whether this change is an improvement
; or not.

;                            (prog2$
;                             (brkpt2 t nil unify-subst gstack rewritten-body
;                                     ttree1 rcnst state)
;                             (mv rewritten-body
;                                 (push-lemma rune ttree1))))

; With further experience, I've decided it is clear that this change is not an
; improvement!  I really like Nqthm's behavior.  The example cited above is
; still a problem.  In particular,

;    (defun ascii-code-lst (lst)
;
;   ; This function converts a standard char list into the list of their
;   ; ascii codes, terminated by a 0.
;
;      (declare (xargs :guard (standard-char-listp lst)
;                      :hints (("Goal" :in-theory (disable member)))
;                      :guard-hints (("Goal" :in-theory (disable member)))))
;      (if (null lst)
;          0
;        (cons (ascii-code (car lst))
;              (ascii-code-lst (cdr lst)))))

; takes forever unless you give the two disable hints shown above.

                              ((contains-rewritable-callp
                                fn rewritten-body
                                (if (cdr recursivep)
                                    recursivep
                                  nil)
                                (access rewrite-constant
                                        rcnst :terms-to-be-ignored-by-rewrite))

; Ok, we are prepared to rewrite the once rewritten body.  But beware!  There
; is an infinite loop lurking here.  It can be broken by using :fnstack
; new-fnstack.  While the loop can be broken by using new-fnstack, that
; approach has a bad side-effect: (member x '(a b c)) is not runout.  It opens
; to (if (equal x 'a) (member x '(b c))) and because new-fnstack mentions
; member, we don't expand the inner call.  See the comment in
; fnstack-term-member for a discussion of loop avoidance (which involved code
; that was here before Version_2.9).

                               (sl-let (rewritten-body ttree2)
                                       (rewrite-entry (rewrite rewritten-body
                                                               nil
                                                               'rewritten-body)
                                                      :fnstack

; See the reference to fnstack in the comment above.

                                                      (cons (cons :TERM term)
                                                            fnstack)
                                                      :ttree ttree1)
                                       (let ((ttree2
                                              (restore-rw-cache-any-tag
                                               (push-lemma+ rune ttree2 rcnst
                                                            ancestors body
                                                            rewritten-body)
                                               ttree1)))
                                         (prog2$
                                          (brkpt2 t nil unify-subst gstack
                                                  rewritten-body ttree2 rcnst
                                                  state)
                                          (mv step-limit
                                              rewritten-body
                                              ttree2)))))
                              (t
                               (prog2$
                                (brkpt2 t nil unify-subst gstack rewritten-body
                                        ttree1 rcnst state)
                                (mv step-limit
                                    rewritten-body
                                    (push-lemma+ rune ttree1 rcnst
                                                 ancestors
                                                 body
                                                 rewritten-body))))))
                            (t (prog2$
                                (brkpt2 nil 'rewrite-fncallp unify-subst gstack
                                        rewritten-body ttree1 rcnst state)
                                (prepend-step-limit
                                 2
                                 (rewrite-solidify
                                  term type-alist obj geneqv
                                  (access rewrite-constant rcnst
                                          :current-enabled-structure)
                                  wrld
                                  (accumulate-rw-cache t ttree1 ttree)
                                  simplify-clause-pot-lst
                                  (access rewrite-constant rcnst
                                          :pt))))))))
                        :conc
                        (access rewrite-rule rule :hyps)))
                      (t (prog2$
                          (brkpt2 nil failure-reason unify-subst gstack nil
                                  nil rcnst state)
                          (prepend-step-limit
                           2
                           (rewrite-solidify term type-alist obj geneqv
                                             (access rewrite-constant rcnst
                                                     :current-enabled-structure)
                                             wrld
                                             (accumulate-rw-cache
                                              t ttree1 ttree)
                                             simplify-clause-pot-lst
                                             (access rewrite-constant rcnst
                                                     :pt)))))))))))
                (t (prepend-step-limit
                    2
                    (rewrite-solidify term type-alist obj geneqv
                                      (access rewrite-constant rcnst
                                              :current-enabled-structure)
                                      wrld ttree
                                      simplify-clause-pot-lst
                                      (access rewrite-constant rcnst
                                              :pt))))))))))))

(defun rewrite-with-lemmas (term ; &extra formals
                            rdepth step-limit
                            type-alist obj geneqv pequiv-info wrld state fnstack
                            ancestors backchain-limit
                            simplify-clause-pot-lst rcnst gstack ttree)
  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   3
   (signed-byte 30)
   (cond
    ((variablep term)
     (rewrite-entry (rewrite-solidify-plus term)))
    ((fquotep term)
     (mv step-limit term ttree))
    ((member-equal (ffn-symb term)
                   (access rewrite-constant rcnst
                           :fns-to-be-ignored-by-rewrite))
     (mv step-limit term ttree))
    ((flambda-applicationp term)
     (mv-let (new-term hyp unify-subst rune rcnst)
             (expand-permission-result term rcnst geneqv wrld)
             (cond (new-term
                    (assert$ (and (null rune) (null hyp))
                             (rewrite-entry (rewrite new-term unify-subst
                                                     'expansion))))
                   (t (rewrite-entry (rewrite-fncall nil term))))))
    (t (sl-let
        (rewrittenp rewritten-term ttree)
        (rewrite-entry (rewrite-with-linear term)
                       :geneqv nil :pequiv-info nil ; both ignored
                       )
        (cond
         (rewrittenp
          (mv step-limit rewritten-term ttree))
         (t
          (sl-let
           (rewrittenp rewritten-term ttree)
           (rewrite-entry
            (rewrite-with-lemmas1 term
                                  (getpropc (ffn-symb term) 'lemmas nil wrld)))
           (cond
            (rewrittenp (mv step-limit rewritten-term ttree))
            (t (mv-let
                (new-term hyp alist rune rcnst)
                (expand-permission-result term rcnst geneqv wrld)
                (cond
                 ((and hyp new-term)

; We want to rewrite something like (if hyp new-term term).  But hyp and
; new-term are to be understood (and rewritten) in the context of the unifying
; substitution, while term is to be understood in the context of the empty
; substitution.  So we lay down code customized to this situation, adapted from
; the definition of rewrite-if.

                  (with-accumulated-persistence
                   rune
                   ((the (signed-byte 30) step-limit) new-term ttree)
                   t
                   (sl-let
                    (rewritten-test ttree)

; We could save the original ttree to use below when we don't use
; rewritten-test.  But this way we record runes that participated even in a
; failed expansion, which could be of use for those who want to use that
; information for constructing a theory in which the proof may replay.

                    (rewrite-entry (rewrite hyp alist 'expansion)
                                   :geneqv *geneqv-iff*
                                   :pequiv-info nil
                                   :obj t
                                   :ttree (push-lemma? rune ttree))
                    (let ((ens (access rewrite-constant rcnst
                                       :current-enabled-structure)))
                      (mv-let
                        (must-be-true
                         must-be-false
                         true-type-alist false-type-alist ts-ttree)
                        (assume-true-false rewritten-test nil
                                           (ok-to-force rcnst)
                                           nil type-alist ens wrld
                                           nil nil :fta)
                        (declare (ignore false-type-alist))
                        (cond
                         (must-be-true
                          (sl-let
                           (rewritten-new-term ttree)
                           (rewrite-entry
                            (rewrite new-term alist 'expansion)
                            :type-alist true-type-alist
                            :ttree (cons-tag-trees ts-ttree ttree))
                           (mv step-limit
                               rewritten-new-term
                               (push-splitter? rune ttree rcnst ancestors
                                               new-term rewritten-new-term))))
                         (t
                          (let ((hide-reason
                                 (and rune
                                      (not (assoc-eq (car rune)
                                                     *fake-rune-alist*))
                                      (list* :expand
                                             rune
                                             (symbol-in-current-package-p
                                              (base-symbol rune) state)))))
                            (cond
                             (must-be-false
                              (mv step-limit
                                  (hide-with-comment hide-reason term wrld
                                                     state)
                                  (push-lemma (fn-rune-nume 'hide nil nil wrld)
                                              (cons-tag-trees ts-ttree ttree))))
                             (t

; We are tempted to bind ttree here to (normalize-rw-any-cache ttree), as we do
; in a similar situation in rewrite-if.  But limited experiments suggest that
; we may get better performance without doing so.

                              (sl-let
                               (rewritten-left ttree1)
                               (rewrite-entry (rewrite new-term alist 2)
                                              :type-alist true-type-alist
                                              :ttree
                                              (rw-cache-enter-context ttree))
                               (mv-let
                                 (final-term ttree)
                                 (rewrite-if11 (fcons-term* 'if
                                                            rewritten-test
                                                            rewritten-left
                                                            (hide-with-comment
                                                             hide-reason
                                                             term wrld state))
                                               type-alist geneqv wrld
                                               (push-lemma (fn-rune-nume 'hide nil
                                                                         nil wrld)
                                                           (rw-cache-exit-context
                                                            ttree ttree1)))
                                 (mv step-limit
                                     final-term

; We avoid push-lemma+ just below, because ttree already incorporates a call of
; push-lemma? on rune.

                                     (push-splitter? rune ttree rcnst ancestors
                                                     new-term
                                                     final-term))))))))))))))
                 (new-term
                  (with-accumulated-persistence
                   rune
                   ((the (signed-byte 30) step-limit) new-term ttree)
                   t
                   (sl-let (final-term ttree)
                           (rewrite-entry (rewrite new-term alist 'expansion)
                                          :ttree (push-lemma? rune ttree))
                           (mv step-limit
                               final-term
                               (push-splitter? rune ttree rcnst ancestors
                                               new-term final-term)))))
                 (t (prepend-step-limit
                     2
                     (rewrite-solidify term type-alist obj geneqv
                                       (access rewrite-constant rcnst
                                               :current-enabled-structure)
                                       wrld ttree
                                       simplify-clause-pot-lst
                                       (access rewrite-constant rcnst
                                               :pt))))))))))))))))

(defun rewrite-linear-term (term alist ; &extra formals
                                 rdepth step-limit
                                 type-alist obj geneqv pequiv-info wrld state
                                 fnstack ancestors
                                 backchain-limit
                                 simplify-clause-pot-lst rcnst gstack ttree)

; We desire to rewrite the instantiated conclusion of :LINEAR lemmas
; before adding them to the linear pot.  (We also rewrite with this
; function the hypotheses being added while building the initial pot
; list, when the non-linear package is turned on via set-non-linearp.)
; To avoid tail biting we adopted the policy of rewriting just the
; args of the conclusion.  It is not known whether this is still
; necessary.

; Historical Plaque from Nqthm:

; However, because all of the literals of the clause being proved are on the
; TYPE-ALIST as false, it is possible -- say when proving an instance of an
; already proved :LINEAR lemma -- to rewrite the conclusion to F!  We could
; avoid this by either not putting the linear-like literals on the type alist
; in the first place, or by not rewriting the entire conclusion, just the
; args.  We took the latter approach because it was simplest.  It does suffer
; from the possibility that the whole (< lhs rhs) of the conclusion might
; rewrite to something else, possibly a better <.

; End of Plaque.

; Note that it is not the case that all of the literals of the clause are on
; type-alist!  In rewrite-clause we do not put the current literal on.  During
; the computation of the initial pot-lst in setup-simplify-clause-pot-lst, the
; type-alist is nil.

; We return two things, the rewritten term and the new ttree.

  (declare (ignore obj geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (mv-let
    (not-flg atm)
    (strip-not term)
    (cond ((and (nvariablep atm)
;               (not (fquotep atm))
                (or (eq (ffn-symb atm) '<)
                    (eq (ffn-symb atm) 'equal)))
           (let ((rcnst1 (if (access rewrite-constant rcnst :nonlinearp)
                             (change rewrite-constant rcnst
                                     :active-theory :arithmetic)
                           rcnst)))
             (sl-let (lhs ttree)
                     (rewrite-entry (rewrite (fargn atm 1) alist 1)
                                    :obj '?
                                    :geneqv nil ; geneqv equal
                                    :pequiv-info nil

; If we have enabled non-linear arithmetic, we change theories here,
; so that we can have a different normal form for polys and linear- and
; non-linear-arithmetic than when rewriting.

                                    :rcnst rcnst1)
                     (sl-let (rhs ttree)
                             (rewrite-entry (rewrite (fargn atm 2) alist 2)
                                            :obj '?
                                            :geneqv nil ; geneqv equal
                                            :pequiv-info nil

; We change theories here also.

                                            :rcnst rcnst1)
                             (cond
                              (not-flg
                               (mv step-limit
                                   (mcons-term*
                                    'not
                                    (mcons-term* (ffn-symb atm) lhs rhs))
                                   ttree))
                              (t (mv step-limit
                                     (mcons-term* (ffn-symb atm) lhs rhs)
                                     ttree)))))))
          (t (mv step-limit (sublis-var alist term) ttree))))))

(defun rewrite-linear-term-lst (term-lst ttrees ; &extra formals
                                         rdepth step-limit
                                         type-alist obj geneqv pequiv-info
                                         wrld state fnstack ancestors
                                         backchain-limit
                                         simplify-clause-pot-lst
                                         rcnst gstack ttree)

; We wish to be able to have a different normal form when doing
; linear and non-linear arithmetic than when doing normal rewriting.
; Therefore, before seeding the linear pot with a poly, we rewrite it
; under the theory prevailing in rewrite-linear-term.

; Term-lst is a list of terms as received by add-terms-and-lemmas, and
; ttrees is its corresponding list of tag-trees.  We simply call
; rewrite-linear-term (nee rewrite-linear-concl in ACL2 Version_2.6)
; on each member of term-lst and return two lists --- the rewritten
; terms and their ttrees.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (if (null term-lst)
       (mv step-limit nil nil)
     (sl-let
      (term1 ttree1)
      (rewrite-entry (rewrite-linear-term (car term-lst) nil)
                     :obj nil ; ignored
                     :geneqv nil ; ignored
                     :pequiv-info nil ; ignored
                     :type-alist (cleanse-type-alist type-alist
                                                     (collect-parents
                                                      (car ttrees)))
                     :ttree (car ttrees))
      (sl-let (term-lst ttree-lst)
              (rewrite-entry (rewrite-linear-term-lst (cdr term-lst)
                                                      (cdr ttrees))
                             :obj nil ; ignored
                             :geneqv nil ; ignored
                             :pequiv-info nil ; ignored
                             :ttree nil ; ignored
                             )
              (mv step-limit
                  (cons term1 term-lst)
                  (cons ttree1 ttree-lst)))))))

(defun add-linear-lemma (term lemma ; &extra formals
                              rdepth step-limit
                              type-alist obj geneqv pequiv-info wrld state
                              fnstack ancestors backchain-limit
                              simplify-clause-pot-lst rcnst gstack ttree)

; We investigate the application of lemma to term and the
; simplify-clause-pot-lst.  If term unifies with the max-term of lemma and we
; can relieve the hypotheses, we add the polynomial produced from lemma's
; conclusion to the pot-lst.  We return three values.  The second is the
; standard contradictionp.  The third is a possibly modified
; simplify-clause-pot-lst.

; PATCH: We use a new field in the linear pots to catch potential loops.
; Loop-stopper-value is initially 0 in all the linear pots.  Let value be the
; loop-stopper-value associated with term in simplify-clause-pot-lst.  When we
; return a new linear-pot-list, we check to see if there are any new pots.  Let
; pot be such a new pot.  If the largest var in pot is term order greater than
; term, we set the loop-stopper-value of pot to value + 1.  Otherwise, we set
; it to value.

; Now, before we actually add any polys to simplify-clause-pot-lst, we call
; no-new-and-ugly-linear-varsp on the list of polys to be added.  This function
; (among other things) checks whether the new vars would have a
; loop-stopper-value which exceeds *max-linear-pot-loop-stopper-value*.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (let ((gstack (push-gframe 'add-linear-lemma nil term lemma))
         (rdepth (adjust-rdepth rdepth)))
     (mv-let
      (unify-ans unify-subst)
      (one-way-unify (access linear-lemma lemma :max-term)
                     term)
      (cond
       ((and unify-ans
             (null (brkpt1 lemma term unify-subst
                           type-alist ancestors
                           nil ; ttree
                           gstack rcnst state)))
        (let ((rune (access linear-lemma lemma :rune)))
          (with-accumulated-persistence
           rune
           ((the (signed-byte 30) step-limit) contradictionp pot-lst)
           (or contradictionp

; The following mis-guarded use of eq instead of equal implies that we could be
; over-counting successes at the expense of failures.

               (not (eq pot-lst simplify-clause-pot-lst)))
           (sl-let
            (relieve-hyps-ans failure-reason unify-subst ttree1)
            (rewrite-entry (relieve-hyps rune
                                         term
                                         (access linear-lemma lemma :hyps)
                                         (access linear-lemma lemma
                                                 :backchain-limit-lst)
                                         unify-subst
                                         (not (oncep (access rewrite-constant
                                                             rcnst
                                                             :oncep-override)
                                                     (access linear-lemma lemma
                                                             :match-free)
                                                     rune
                                                     (access linear-lemma lemma
                                                             :nume))))
                           :obj nil :geneqv nil :pequiv-info nil ; all ignored
                           :ttree nil)
            (cond
             (relieve-hyps-ans
              (sl-let
               (rewritten-concl ttree2)
               (with-accumulated-persistence
                rune
                ((the (signed-byte 30) step-limit) rewritten-concl ttree2)
                t ; considered a success unless the parent with-acc-p fails
                (rewrite-entry
                 (rewrite-linear-term
                  (access linear-lemma lemma :concl)
                  unify-subst)
                 :obj nil :geneqv nil :pequiv-info nil ; all ignored
                 :ttree ttree1)
                :conc
                (access linear-lemma lemma :hyps))

; Previous to Version_2.7, we just went ahead and used the result of
; (linearize rewritten-concl ...).  This had long been known to be
; problematic (see the comments in linearize1 beginning ``This is a
; strange one.'') but nothing had been done about it.  Then Eric Smith
; sent the following example to us and wanted to know what was going
; wrong.

;    (defstub bitn (x n) t)   ; extract bit n of x
;
;    (skip-proofs
;     (defthm bitn-non-negative-integer
;      (and (integerp (bitn x n))
;           (<= 0 (bitn x n)))
;      :rule-classes (:rewrite :type-prescription)))
;
;    (skip-proofs
;     (defthm bits-upper-bound-linear
;       (< (bits x i j) (expt 2 (+ i 1 (- j))))
;       :rule-classes ((:linear :trigger-terms ((bits x i j))))))
;
;    ;goes through (using the two :linear rules above)
;    (thm
;     (< (+ (BITN x 32)
;           (BITN x 58))
;        2))
;
;    ;the problem rule.
;    (skip-proofs
;     (defthm bitn-known-not-0-replace-with-1
;      (implies (not (equal (bitn x n) 0))
;               (equal (bitn x n)
;                      1))))
;
;    ;same thm; now fails --- the rule above causes linear arithmetic to fail.
;
;    (thm
;     (< (+ (BITN x 32)
;           (BITN x 58))
;        2))

; If one uses the following trace and replays the above script, one
; can see what was happening (In a nutshell, ACL2 rewrites the (BITN B
; Z) in the instantiated conclusion of bitn-upper-bound-linear, (<=
; (BITN B Z) 1), to 1 yielding (<= 1 1), which is trivially true but
; not very useful.

;    (defun show-type-alist (type-alist)
;      (cond ((endp type-alist) nil)
;            (t (cons (list (car (car type-alist))
;                           (decode-type-set (cadr (car type-alist))))
;                     (show-type-alist (cdr type-alist))))))
;    SHOW-TYPE-ALIST
;    ACL2(3): (trace (add-polys
;             :entry (list (list 'new-polys (show-poly-lst (nth 0 arglist)))
;                          (list 'pot-lst (show-pot-lst (nth 1 arglist)))
;                          (list 'type-alist (show-type-alist (nth 3 arglist))))
;             :exit (list (list 'contradictionp (nth 0 values))
;                         (list 'new-pot-lst (show-pot-lst (nth 1 values)))))
;           (add-linear-lemma
;             :entry (list (list 'term (nth 0 arglist))
;                          (list 'lemma (nth 1 arglist)))
;             :exit (list (list 'contradictionp (nth 0 values))
;                         (list 'new-pot-lst (show-pot-lst (nth 1 values)))))
;          (rewrite-linear-term
;             :entry (list (list 'term (sequential-subst-var-term (nth 1 arglist)
;                                                                 (nth 0 arglist))))
;             :exit (list (list 'rewritten-term (nth 0 values))
;                         (list 'ttree (nth 1 arglist)))))
;    (REWRITE-LINEAR-TERM ACL2_*1*_ACL2::REWRITE-LINEAR-TERM ADD-LINEAR-LEMMA
;                          ACL2_*1*_ACL2::ADD-LINEAR-LEMMA ADD-POLYS
;                          ACL2_*1*_ACL2::ADD-POLYS)

; The best solution would probably be to not rewrite the instantiated
; trigger term in rewrite-linear-term, but that has its own problems
; and is much more work to implement.  By just reverting to the
; un-rewritten concl we catch the ``obvious'' cases such as
; illustrated above.  Note that the un-rewritten concl may also
; linearize to nil, but a regression test using the community books
; actually shows a slight improvement in speed (about a
; minute and a half, out of 158 and a half minutes), so we conclude
; that this is not a problem in practice.

; We thank Robert Krug for providing this improvement.

               (let ((force-flg (ok-to-force rcnst)))
                 (mv-let
                  (contradictionp new-pot-lst failure-reason brr-result)
                  (add-linear-lemma-finish rewritten-concl force-flg rune t
                                           term type-alist wrld state
                                           simplify-clause-pot-lst rcnst ttree2)
                  (cond
                   (contradictionp
                    (prog2$ (brkpt2 t nil unify-subst gstack
                                    brr-result
                                    nil ; ttree, not used (see brkpt2)
                                    rcnst state)
                            (mv step-limit contradictionp nil)))
                   (t
                    (mv-let
                     (contradictionp new-pot-lst failure-reason brr-result)
                     (let ((unrewritten-concl-to-try
                            (and (or (eq new-pot-lst :null-lst)

; Simplify-clause arranges for the following term to be true immediately after
; the clause has settled down.  In that case, we are prepared to try any
; "desperation heuristics", such as (here) linearizing the unrewritten
; conclusion in cases when we would have stopped after linearizing the
; rewritten conclusion.  Below are two examples that motivated this change.

; Example 1.

; Consider the following theorem:
; (<= (len (cdr (cdr (nthcdr n stk))))
;      (len stk))

; A script is below that introduces two linear lemmas that one could reasonably
; expect to suffice for proving this theorem, given the following informal
; proof.

;   (len (cdr (cdr (nthcdr n stk))))
;   <=                                 ; by linear1
;   (len (cdr (nthcdr n stk)))
;   <=                                 ; by linear1
;   (len (nthcdr n stk))
;   <=                                 ; by linear2
;   (len stk)

; Here are the two linear lemmas.

;   (defthm linear1
;     (<= (len (cdr stk)) (len stk))
;     :rule-classes :linear)

;   (defthm linear2
;     (<= (len (nthcdr n stk)) (len stk))
;     :rule-classes :linear)

; The following theorem did not prove until after we added this "desperate
; heuristic" to linearize the unrewritten conclusion.

;   (thm (<= (len (cdr (cdr (nthcdr n stk))))
;            (len stk))
;        :hints (("Goal" :do-not-induct t)))

; Example 2.

; First evaluate these events:

;   (include-book "arithmetic-5/top" :dir :system)
;
;   (defthm mod-linear
;     (implies (and (natp x) (natp k)) (<= (mod x k) x))
;     :rule-classes :linear)
;
;   (encapsulate ((rd (x) t))
;                (local (defun rd (x) (nfix x)))
;                (defthm natp-rd (natp (rd x))
;                  :rule-classes :type-prescription))

; The following proves, and indeed proved (without induction) before the
; change.

;   (thm (<= (mod (rd x) 4)
;            (+ 1 (rd x))))

; But the following theorem only proved after the change.  Naively one wouldn't
; expect the hypothesis to get in the way.  (We are not using induction in this
; example.)  To make matters worse, the hypothesis is provable; the two
; theorems really are equivalent.

;   (thm (implies
;         (< (mod (rd x) 4) 5)
;         (<= (mod (rd x) 4)
;             (+ 1 (rd x)))))

                                     (eq (access rewrite-constant rcnst
                                                 :rewriter-state)
                                         'settled-down))
                                 (sublis-var unify-subst
                                             (access linear-lemma lemma
                                                     :concl)))))
                       (cond
                        ((and unrewritten-concl-to-try
                              (not (equal rewritten-concl
                                          unrewritten-concl-to-try)))
                         (add-linear-lemma-finish
                          unrewritten-concl-to-try
                          force-flg
                          rune nil
                          term type-alist wrld state
                          (if (eq new-pot-lst :null-lst)
                              simplify-clause-pot-lst
                            new-pot-lst)
                          rcnst
                          (push-lemma
                           rune
                           (accumulate-rw-cache t
                                                ttree2
                                                ttree1))))
                        (t (mv nil new-pot-lst failure-reason brr-result))))
                     (cond (contradictionp
                            (prog2$ (brkpt2 t nil unify-subst gstack
                                            brr-result
                                            nil ; ttree, not used (see brkpt2)
                                            rcnst state)
                                    (mv step-limit contradictionp nil)))
                           (failure-reason
                            (prog2$ (brkpt2 nil failure-reason unify-subst gstack
                                            brr-result
                                            nil ; ttree, not used (see brkpt2)
                                            rcnst state)
                                    (mv step-limit nil new-pot-lst)))
                           (t
                            (prog2$ (brkpt2 t nil unify-subst gstack
                                            brr-result
                                            nil ; ttree, not used (see brkpt2)
                                            rcnst state)
                                    (mv step-limit nil new-pot-lst)))))))))))
             (t (prog2$
                 (brkpt2 nil failure-reason
                         unify-subst gstack nil nil
                         rcnst state)
                 (mv step-limit nil simplify-clause-pot-lst))))))))
       (t (mv step-limit nil simplify-clause-pot-lst)))))))

(defun add-linear-lemmas (term linear-lemmas ; &extra formals
                               rdepth step-limit
                               type-alist obj geneqv pequiv-info wrld state
                               fnstack ancestors
                               backchain-limit
                               simplify-clause-pot-lst rcnst gstack ttree)

; Linear-lemmas is a list of linear-lemmas.  We look for those lemmas
; in linear-lemmas that match term and, if their hyps can be relieved
; and the resulting polys don't contain new and ugly vars, add them to
; the simplify-clause-pot-lst.

; We return two values.  The first is the standard contradictionp.
; The second is the possibly new pot-lst.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (cond
    ((null linear-lemmas)
     (mv step-limit nil simplify-clause-pot-lst))
    ((not (enabled-numep (access linear-lemma (car linear-lemmas) :nume)
                         (access rewrite-constant rcnst
                                 :current-enabled-structure)))
     (rewrite-entry (add-linear-lemmas term (cdr linear-lemmas))
                    :obj nil ; ignored
                    :geneqv nil ; ignored
                    :pequiv-info nil ; ignored
                    :ttree nil ; ignored
                    ))
    (t (sl-let
        (contradictionp new-pot-lst)
        (rewrite-entry (add-linear-lemma term
                                         (car linear-lemmas))
                       :obj nil ; ignored
                       :geneqv nil ; ignored
                       :pequiv-info nil ; ignored
                       :ttree nil ; ignored
                       )
        (cond (contradictionp (mv step-limit contradictionp nil))
              (t (rewrite-entry
                  (add-linear-lemmas term (cdr linear-lemmas))
                  :obj nil ; ignored
                  :geneqv nil ; ignored
                  :pequiv-info nil ; ignored
                  :ttree nil ; ignored
                  :simplify-clause-pot-lst new-pot-lst))))))))

(defun multiply-alists2 (alist-entry1 alist-entry2 poly ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv pequiv-info wrld
                                      state fnstack ancestors backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)

; We are in the middle of multiplying two polys.  Poly is the result
; so far.  Alist-entry1 is an alist entry from the first poly, and
; alist-entry2 is an alist entry from the second poly.  See multiply-alists.

; Here, we perform the actual multiplication of the two alist entries
; and add the result to poly.  Note that each entry is of the form
; (term . coeff).

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (let* ((leaves1 (binary-*-leaves (car alist-entry1)))
          (leaves2 (binary-*-leaves (car alist-entry2)))
          (leaves (merge-arith-term-order leaves1 leaves2))
          (tree (binary-*-tree leaves))
          (coeff (* (cdr alist-entry1)
                    (cdr alist-entry2)))
          (temp-entry (mcons-term* 'BINARY-*
                                   (kwote coeff)
                                   tree)))
     (sl-let
      (new-entry new-ttree)
      (rewrite-entry (rewrite temp-entry nil 'multiply-alists2)
                     :obj nil
                     :geneqv nil
                     :pequiv-info nil

; We change theories here, so that we can have a different normal form
; for the terms in polys than when rewriting in general.

                     :rcnst (change rewrite-constant rcnst
                                    :active-theory :arithmetic)
                     :ttree nil)
      (let ((new-poly (add-linear-term new-entry 'rhs poly)))
        (mv step-limit
            (change poly new-poly
                    :ttree (cons-tag-trees-rw-cache new-ttree
                                                    (access poly new-poly
                                                            :ttree))
                    :parents (marry-parents
                              (collect-parents new-ttree)
                              (access poly new-poly :parents)))))))))

(defun multiply-alists1 (alist-entry alist2 poly ; &extra formals
                                     rdepth step-limit
                                     type-alist obj geneqv pequiv-info
                                     wrld state
                                     fnstack ancestors backchain-limit
                                     simplify-clause-pot-lst
                                     rcnst gstack ttree)

; We are in the middle of multiplying two polys.  Poly is the result
; so far.  Alist-entry is an alist entry from the first poly, and
; alist2 is the alist from the second poly.  See multiply-alists.

; Here, we cdr down alist2 multiplying alist-entry by each entry in
; alist2 and adding the result to poly.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (cond
    ((null alist2)
     (mv step-limit poly))
    (t
     (sl-let
      (temp-poly)
      (rewrite-entry
       (multiply-alists2 alist-entry
                         (car alist2)
                         poly)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       )
      (rewrite-entry
       (multiply-alists1 alist-entry
                         (cdr alist2)
                         temp-poly)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       ))))))

(defun multiply-alists (alist1 alist2 poly ; &extra formals
                               rdepth step-limit
                               type-alist obj geneqv pequiv-info
                               wrld state fnstack ancestors backchain-limit
                               simplify-clause-pot-lst
                               rcnst gstack ttree)

; We are in the middle of multiplying two polys.  Poly is the result
; so far.  Initially, it has a partially filled alist and we need to
; finish filling it in.  Alist1 is the alist from the first poly,
; and alist2 is the alist from the second poly.

; If one thinks of the initial polys as

; 0 < const1 + alist1 and 0 < const2 + alist2,

; poly initially contains
; 0 < const1*const2 + const1*alist2 + const2*alist1 + ()
; and our job is to successively add things to the ().

; In particular, we wish to form alist1*alist2.  Here, we cdr down
; alist1 multiplying each entry by alist2 and adding the result to poly.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (cond
    ((null alist1)
     (mv step-limit poly))
    (t
     (sl-let
      (temp-poly)
      (rewrite-entry
       (multiply-alists1 (car alist1)
                         alist2
                         poly)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       )
      (rewrite-entry
       (multiply-alists (cdr alist1)
                        alist2
                        temp-poly)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       ))))))

(defun multiply-polys1 (alist1 const1 rel1 alist2 const2 rel2
                               poly ; &extra formals
                               rdepth step-limit
                               type-alist obj geneqv pequiv-info
                               wrld state fnstack ancestors backchain-limit
                               simplify-clause-pot-lst
                               rcnst gstack ttree)

; We are in the middle of multiplying two polys.  Poly is the result so far.
; Initially, it has an empty alist which we need to fill in.  Alist1 and const1
; are the alist and constant from the first poly, and alist2 and const2 are
; from the second poly.  We assume that at least one of these two polys is
; rational-poly-p.  Here we construct the alist for poly, finishing the process.

; If one thinks of the initial polys as

; 0 < const1 + alist1 and 0 < const2 + alist2,

; poly initially contains 0 < const1*const2 + () and our job is to successively
; add things to the ().  We wish to form const1*alist2 + const2*alist1 +
; alist1*alist2.  The first two steps are performed by the successive
; multiply-alist-and-consts in the let* below, accumulating their answers
; into the growing alist.  We finish with multiply-alists.

  (declare (ignore obj geneqv pequiv-info ttree rel1 rel2)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

; Warning: It may be tempting to add the following optimization, as was done up
; through Version_3.3.  Don't do it!  The optimization is that under suitable
; hypotheses (see optimization code below): when given 0 < a1 + b1x and 0 < a2
; + b2y, first let a1' = -a1 and b1' = -b1 and then multiply a1' < b1x by a2' <
; b2 y to get a1'a2' < b1b2xy.

; Consider the following example that illustrates the problem with this
; optimization.

; (set-non-linearp t)
; (thm (implies (and (rationalp x) (< 3 x)
;                    (rationalp y) (< 4 y))
;               (< 0 (+ 12 (* -4 x) (* -3 y) (* x y)))))

; With the optimization shown below, the proof fails, because the hypotheses
; only generate the weaker inequality (< 0 (+ -12 (* x y))).  This inequality,
; which we will name In0, is weaker than the thm's conclusion above because
; under the thm's hypotheses, we have (< (* -4 x) -12) and (< (* -3 x) -12),
; and adding these inequalities to the thm's conclusion yields In0.  In0 is
; strictly weaker than the thm's conclusion: consider x=13 and y=1, which makes
; In0 true but makes the thm's conclusion false.  Of course, that example
; doesn't take into account the hypotheses on x and y above, so the following
; example may be more persuasive.  Consider abstracting (* x y) to a new
; variable z, and consider whether the weaker inequality implies the stronger
; -- if so, then we would expect linear arithmetic reasoning to be able to
; derive the stronger from the weaker when necessary.

; (implies (and (rationalp x) (< 3 x)
;               (rationalp y) (< 4 y)
;               (rationalp z) (< 12 z))
;          (< 0 (+ 12 (* -4 x) (* -3 y) z)))

; But this is not a theorem -- consider x = y = z = 100.

; Here, then, is the optimization code to avoid:

; (if (and (rationalp const1)
;          (rationalp const2)
;          (< const1 0)
;          (< const2 0))
;     (let ((temp-poly (if (and (eq (access poly poly :relation) '<=)
;                               (or (eq rel1 '<)
;                                   (eq rel2 '<)))
;                          (change poly poly
;                                  :constant
;                                  (- (access poly poly :constant))
;                                  :relation
;                                  '<)
;                        (change poly poly
;                                :constant
;                                (- (access poly poly :constant))))))
;       (rewrite-entry
;        (multiply-alists alist1 alist2
;                         temp-poly)
;        :obj nil
;        :geneqv nil
;        :pequiv-info nil
;        :ttree nil))

; The following examples from Robert Krug illustrate issues pertaining to the
; above "optimization".  First note that the following fails with the
; optimization.  We have labeled interesting hypotheses for an explanation
; below.

; (set-non-linearp t)
; (thm
;  (implies (and (rationalp i)
;                (rationalp n)
;                (rationalp r)
;                (<= 1 i)      ; [1]
;                (<= 1 n)      ; [2]
;                (< r 0)       ; [3]
;                (< (- i) r))  ; [4]
;           (<= 0 (+ r (* i n)))))

; However, if in this formula we change r to a, and/or if we comment out the
; hypothesis (<= 1 i), then we succeed with or without the optimization,
; i.e. in Version_3.3 or beyond.

; First, consider how commenting out [1] can help.  ACL2 can add hypotheses [3]
; and [4] about r to generate 0 < i.  This can be multiplied by [2] (in the
; form 0 <= -1 + n) to generate an i*n term.  This product -- performed without
; the optimization, since 0 < i has a constant of zero -- is 0 < -i + i*n.
; This adds to [4] to yield the conclusion.  BUT if [1] is around, it subsumes
; generated inequality 0 < i, and then with the optimization, hypotheses [1]
; and [2] generate 1 <= i*n, and we claim that the conclusion no longer follows
; by linear reasoning.  To verify this claim, treat i*n as a variable by
; replacing it with z, and then notice that the following evaluates to NIL:

; (let ((i 10) (n 10) (r -5) (z 1))
;   (implies (and (rationalp i)
;                 (rationalp n)
;                 (rationalp r)
;                 (rationalp z)
;                 (<= 1 i)      ; [1]
;                 (<= 1 n)      ; [2]
;                 (< r 0)       ; [3]
;                 (< (- i) r)   ; [4]
;                 (<= 1 z))     ; generated, with i*n abstracted
;            (<= 0 (+ r z))))

; Second, consider how changing r to a can help.  We have the following.

; (thm
;  (implies (and (rationalp i)
;                (rationalp n)
;                (rationalp a)
;                (<= 1 i)      ; [1]
;                (<= 1 n)      ; [2]
;                (< a 0)       ; [3]
;                (< (- i) a))  ; [4]
;           (<= 0 (+ a (* i n)))))

; This time, [4] is about i, not r.  So in order to obtain an i*n term, we can
; multiply [4] (actually 0 < i + a) by [2] (actually 0 <= -1 + n), and what's
; more, there is no "optimization" since [4] has a constant of 0.
; Multiplication gives us: 0 < -i + i*n - a + a*n.  We add this to the negated
; conclusion, 0 < -a - i*n, to obtain 0 < -i - 2*a + a*n.  We combine this with
; [4] to obtain 0 < -a + a*n.  We then generate an inequality about a*n by
; multiplying [2] and [3] (without optimization, since [3] has a constant of 0)
; to obtain 0 < a - a*n.  Adding this to the previous result yields a
; contradiction.

  (the-mv
   2
   (signed-byte 30)
   (let* ((temp-poly1
           (if (eql const2 0)
               poly
             (multiply-alist-and-const alist1 const2 poly)))
          (temp-poly2
           (if (eql const1 0)
               temp-poly1
             (multiply-alist-and-const alist2 const1 temp-poly1))))
     (rewrite-entry
      (multiply-alists alist1 alist2 temp-poly2)
      :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
      ))))

(defun multiply-polys (poly1 poly2 ; &extra formals
                             rdepth step-limit
                             type-alist obj geneqv pequiv-info wrld state fnstack
                             ancestors backchain-limit
                             simplify-clause-pot-lst
                             rcnst gstack ttree)

; We are to multiply the two polys, poly1 and poly2.  Roughly speaking this
; function implements the lemma:

; (implies (and (rationalp terms1)
;               (< 0 terms1)
;               (< 0 terms2))
;          (< 0 (* terms1 terms2)))

; We assume that either poly1 or poly2 is rational-poly-p.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (let ((alist1 (access poly poly1 :alist))
         (ttree1 (access poly poly1 :ttree))
         (const1 (access poly poly1 :constant))
         (rel1 (access poly poly1 :relation))
         (parents1 (access poly poly1 :parents))
         (ratp1 (access poly poly1 :rational-poly-p))
         (alist2 (access poly poly2 :alist))
         (ttree2 (access poly poly2 :ttree))
         (const2 (access poly poly2 :constant))
         (rel2 (access poly poly2 :relation))
         (parents2 (access poly poly2 :parents))
         (ratp2 (access poly poly2 :rational-poly-p)))
     (let ((pre-poly (make poly
                           :alist nil
                           :ttree (cons-tag-trees-rw-cache ttree1 ttree2)
                           :parents (marry-parents parents1 parents2)
                           :constant (* const1 const2)
                           :relation (if (and (eq rel1 '<)
                                              (eq rel2 '<))
                                         '<
                                       '<=)
                           :rational-poly-p (and ratp1 ratp2))))
       (sl-let
        (poly)
        (rewrite-entry
         (multiply-polys1 alist1 const1 rel1
                          alist2 const2 rel2
                          pre-poly)
         :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
         )
        (mv step-limit (normalize-poly poly)))))))

(defun multiply-pots2 (poly big-poly-list new-poly-list ; &extra formals
                            rdepth step-limit
                            type-alist obj geneqv pequiv-info wrld state fnstack
                            ancestors backchain-limit
                            simplify-clause-pot-lst
                            rcnst gstack ttree)

; Poly is a poly and we are to multiply it by the polys in
; big-poly-list, accumulating the answer into new-poly-list.  We
; assume that poly is a rational-poly-p.  Every poly in big-poly-list
; is assumed to be a rational-poly-p.

; We return a list of polys.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (cond
    ((null big-poly-list)
     (mv step-limit new-poly-list))
    ((or (access poly poly :rational-poly-p)
         (access poly (car big-poly-list) :rational-poly-p))

; If at least one of poly and (car big-poly-list) are rational, multiplication
; preserves sign.  See the comments in multiply-polys.

     (sl-let (new-poly)
             (rewrite-entry
              (multiply-polys poly (car big-poly-list))
              :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
              )
             (rewrite-entry
              (multiply-pots2 poly
                              (cdr big-poly-list)
                              (cons new-poly new-poly-list))
              :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
              )))
    (t

; Since neither poly is known to be rational, we skip this multiplication.

     (rewrite-entry
      (multiply-pots2 poly
                      (cdr big-poly-list)
                      new-poly-list)
      :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
      )))))

(defun multiply-pots1 (poly-list big-poly-list new-poly-list ; &extra formals
                                 rdepth step-limit
                                 type-alist obj geneqv pequiv-info wrld state
                                 fnstack ancestors backchain-limit
                                 simplify-clause-pot-lst
                                 rcnst gstack ttree)

; Both poly-list and big-poly-list are lists of polys.  We are to
; multiply the polys in poly-list by those in big-poly-list.
; New-poly-list is initially nil, and is where we accumulate our
; answer.  We assume every element of big-poly-lst is a
; rational-poly-p.

; We return a list of polys.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (cond
    ((null poly-list)
     (mv step-limit new-poly-list))
    (t
     (sl-let
      (new-new-poly-list)
      (rewrite-entry
       (multiply-pots2 (car poly-list)
                       big-poly-list
                       new-poly-list)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       )
      (rewrite-entry
       (multiply-pots1 (cdr poly-list)
                       big-poly-list
                       new-new-poly-list)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       ))))))

(defun multiply-pots-super-filter (var-list pot-lst-to-look-in ; &extra formals
                                            rdepth step-limit
                                            type-alist obj geneqv pequiv-info
                                            wrld state fnstack
                                            ancestors
                                            backchain-limit
                                            simplify-clause-pot-lst
                                            rcnst gstack ttree)

; This function is similar to multiply-pots, which see, except that we
; only multiply the bounds polys of the pots labeled by the vars in var-list.

; We return a list of polys.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (cond
    ((null var-list)
     (mv step-limit nil))
    ((null (cdr var-list))
     (mv step-limit
         (shortest-polys-with-var (car var-list)
                                  pot-lst-to-look-in
                                  (access rewrite-constant rcnst :pt))))
    (t
     (sl-let
      (big-poly-list)
      (rewrite-entry
       (multiply-pots-super-filter (cdr var-list)
                                   pot-lst-to-look-in)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       )
      (rewrite-entry
       (multiply-pots1 (shortest-polys-with-var (car var-list)
                                                pot-lst-to-look-in
                                                (access rewrite-constant
                                                        rcnst
                                                        :pt))
                       big-poly-list
                       nil)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       ))))))

(defun multiply-pots-filter (var-list pot-lst-to-look-in ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv pequiv-info
                                      wrld state
                                      fnstack ancestors backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)

; This function is similar to multiply-pots except that we assume
; var-list is of length two, and we multiply only some of the polys.
; in particular, we multiply the bounds polys of one pot by the polys
; in the other pot, and vice-versa.

; We return a list of polys.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (sl-let
    (poly-list1)
    (rewrite-entry
     (multiply-pots1 (bounds-polys-with-var (car var-list)
                                            pot-lst-to-look-in
                                            (access rewrite-constant
                                                    rcnst
                                                    :pt))
                     (polys-with-var (cadr var-list)
                                     pot-lst-to-look-in)
                     nil)
     :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
     )
    (rewrite-entry
     (multiply-pots1 (bounds-polys-with-var (cadr var-list)
                                            pot-lst-to-look-in
                                            (access rewrite-constant
                                                    rcnst
                                                    :pt))
                     (polys-with-var (car var-list)
                                     pot-lst-to-look-in)
                     poly-list1)
     :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
     ))))

(defun multiply-pots (var-list pot-lst-to-look-in ; &extra formals
                               rdepth step-limit
                               type-alist obj geneqv pequiv-info
                               wrld state fnstack ancestors backchain-limit
                               simplify-clause-pot-lst
                               rcnst gstack ttree)

; Var-list is a list of pot-labels in pot-lst-to-look-in.  We are
; about to multiply the polys of the labeled pots.  We recur down
; var-list and as we unwind the recursion we multiply the polys
; corresponding to the first pot-label in var-list by the result
; of multiplying the polys corresponding to the rest of the pot-labels.
; Multiply-pots1 is responsible for carrying out the actual multiplication.

; We return a list of polys.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   2
   (signed-byte 30)
   (cond
    ((null var-list) ; How can we multiply 0 things?
     (mv step-limit nil))
    ((null (cdr var-list))
     (mv step-limit
         (polys-with-var (car var-list) pot-lst-to-look-in)))
    (t
     (sl-let
      (big-poly-list)
      (rewrite-entry
       (multiply-pots (cdr var-list)
                      pot-lst-to-look-in)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       )
      (rewrite-entry
       (multiply-pots1 (polys-with-var (car var-list)
                                       pot-lst-to-look-in)
                       big-poly-list
                       nil)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       ))))))

(defun add-multiplied-polys-filter (var-list products-already-tried
                                             pot-lst-to-look-in ; &extra formals
                                             rdepth step-limit
                                             type-alist obj geneqv pequiv-info
                                             wrld state fnstack
                                             ancestors backchain-limit
                                             simplify-clause-pot-lst
                                             rcnst gstack ttree)

; This function assumes that var-list is of length two.  It is similar to
; add-multiply-pots, which see, except that we only multiply some of the polys
; corresponding to the pots labeled by the vars in var-list.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   4
   (signed-byte 30)
   (cond
    ((product-already-triedp var-list products-already-tried)
     (mv step-limit nil simplify-clause-pot-lst products-already-tried))
    (t
     (sl-let
      (poly-list1)
      (rewrite-entry
       (multiply-pots-filter var-list
                             pot-lst-to-look-in)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       )

; By filtering the polys so that we avoid creating new pots, we can
; dramatically speed up proofs, for example the failure of the following.  (The
; result is reversed, but no matter.)  Robert Krug contributed this
; modification, and expresses the opinion that the extra consing done by
; polys-with-pots is quite likely less expensive in general than the effort it
; would take to see if any filtering actually occurs, especially since
; filtering probably does occur most of the time.

;    (include-book "arithmetic-3/bind-free/top" :dir :system)
;    (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
;                                                  hist pspv)))
;    (defstub f (x) t)
;    (thm
;     (implies (and (rationalp (f r))
;                   (integerp (f i))
;                   (< (f i) 0)
;                   (not (integerp (* (f r) (/ (f y)))))
;                   (< (f r) (f y))
;                   (< (/ (f r) (f y)) 1)
;                   (< 0 (f r))
;                   (< (+ (f r) (* (f i) (f y))) -1)
;                   (rationalp (f y))
;                   (<= 2 (f y)))
;              (< (+ (f r) (* (f i) (f y))) (f i))))

      (let ((poly-list2 (polys-with-pots poly-list1
                                         simplify-clause-pot-lst
                                         nil)))
        (mv-let (contradictionp new-pot-lst)
                (add-polys poly-list2
                           simplify-clause-pot-lst
                           (access rewrite-constant rcnst :pt)
                           (access rewrite-constant rcnst :nonlinearp)
                           type-alist
                           (access rewrite-constant rcnst
                                   :current-enabled-structure)
                           (ok-to-force rcnst)
                           wrld)
                (mv step-limit contradictionp new-pot-lst
                    (cons (sort-arith-term-order var-list)
                          products-already-tried)))))))))

(defun add-multiplied-polys (var-list products-already-tried
                                      pot-lst-to-look-in ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv pequiv-info
                                      wrld state
                                      fnstack ancestors backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)

; Var-list is a list of pot labels.  If we have not yet multiplied
; the polys corresponding to those labels, we do so and add them to the
; the simplify-clause-pot-lst.  Products-already-tried is a list of the
; factors we have already tried, and pot-lst-to-look-in is the pot-lst
; from which we get our polys.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   4
   (signed-byte 30)
   (cond
    ((null (cdr var-list))
     (mv step-limit nil simplify-clause-pot-lst products-already-tried))
    ((product-already-triedp var-list products-already-tried)
     (mv step-limit nil simplify-clause-pot-lst products-already-tried))
    ((or (too-many-polysp var-list pot-lst-to-look-in 1)
         (< 4 (length var-list)))


; If we went ahead and naively multiplied all the polys corresponding
; to the pot labels in var-list, we would get too many of them and
; be overwhelmed.  So, we will only multiply some of the polys.

     (sl-let
      (poly-list)
      (rewrite-entry
       (multiply-pots-super-filter var-list
                                   pot-lst-to-look-in)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       )
      (mv-let (contradictionp new-pot-lst)
              (add-polys poly-list
                         simplify-clause-pot-lst
                         (access rewrite-constant rcnst :pt)
                         (access rewrite-constant rcnst :nonlinearp)
                         type-alist
                         (access rewrite-constant rcnst
                                 :current-enabled-structure)
                         (ok-to-force rcnst)
                         wrld)
              (mv step-limit contradictionp new-pot-lst
                  (cons (sort-arith-term-order var-list)
                        products-already-tried)))))
    (t
     (sl-let
      (poly-list)
      (rewrite-entry
       (multiply-pots var-list
                      pot-lst-to-look-in)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       )
      (mv-let (contradictionp new-pot-lst)
              (add-polys poly-list
                         simplify-clause-pot-lst
                         (access rewrite-constant rcnst :pt)
                         (access rewrite-constant rcnst :nonlinearp)
                         type-alist
                         (access rewrite-constant rcnst
                                 :current-enabled-structure)
                         (ok-to-force rcnst)
                         wrld)
              (mv step-limit contradictionp new-pot-lst
                  (cons (sort-arith-term-order var-list)
                        products-already-tried))))))))

(defun deal-with-product1 (part-of-new-var var-list
                                           pot-lst-to-look-in
                                           pot-lst-to-step-down
                                           products-already-tried ; &extra formals
                                           rdepth step-limit
                                           type-alist obj geneqv pequiv-info
                                           wrld state fnstack
                                           ancestors backchain-limit
                                           simplify-clause-pot-lst
                                           rcnst gstack ttree)

; Pot-lst-to-look-in is the pot-lst we keep around to extract polys for
; multiplication from (see non-linear-arithmetic), and pot-lst-to-step-down
; is the pot-lst we cdr down as we recurse through this function.  They
; are initially the same.  Products-already-tried is an accumulator which
; keeps track of which pots we have already tried multiplying the polys from.

; We are here because we wish to find a set of polys to multiply together.
; Part-of-new-var is an ACL2-term and var-list is a list of pot-labels.
; If part-of-new-var is '1, we have found our set of polys, and we will
; proceed to multiply the polys corresponding to those pot-labels and add
; them to the simplify-clause-pot-lst.  Otherwise, we attempt to find
; some pot labels whose product will form part-of-new-var, adding them
; to var-list as we go.

; All the deal-with-xxx functions return four values: a new step-limit, the
; standard contradictionp, a potentially augmented pot-lst (or nil if
; contradictionp is true), and the accumulated list of products we have already
; tried.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   4
   (signed-byte 30)
   (cond
    ((equal part-of-new-var *1*)
     (if (null (cdr var-list))
         (mv step-limit nil simplify-clause-pot-lst products-already-tried)
       (rewrite-entry
        (add-multiplied-polys var-list
                              products-already-tried
                              pot-lst-to-look-in)
        :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
        )))
    ((null pot-lst-to-step-down)
     (mv step-limit nil simplify-clause-pot-lst products-already-tried))
    (t

; Is the label of the pot we are standing on a factor of part-of-new-var?
; If so, we proceed in two ways --- try using the factor, and try without
; using the factor.

     (let ((new-part-of-new-var (part-of (access linear-pot
                                                 (car pot-lst-to-step-down)
                                                 :var)
                                         part-of-new-var)))
       (cond (new-part-of-new-var
              (sl-let
               (contradictionp new-pot-list products-already-tried)
               (rewrite-entry
                (deal-with-product1 new-part-of-new-var
                                    (cons (access linear-pot
                                                  (car pot-lst-to-step-down)
                                                  :var)
                                          var-list)
                                    pot-lst-to-look-in

; Once upon a time, we used (cdr pot-lst-to-step-down) below.  But
; that introduces an asymmetry in handling (* a a) v (* a a a a) when
; one is new and the other is old.  For example, if (* a a) is a new
; var and (* a a a a) is an old pot label, deal-with-factor would
; recognize that we could square the former.  But if (* a a a a) is
; the new var and (* a a) is the old one -- and we use (cdr
; pot-lst-to-step-down) below -- then deal-with-product would not find
; an opportunity to square (* a a).  In particular, it would recognize
; (* a a) as a part of (* a a a a) and generate the subgoal of finding
; polys about (* a a), but it would do so in a shorter pot list in
; which the pot containing (* a a) was now cdr'd past.

                                    pot-lst-to-look-in
                                    products-already-tried)
                :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
                )
               (cond (contradictionp (mv step-limit
                                         contradictionp
                                         nil
                                         products-already-tried))
                     (t
                      (rewrite-entry
                       (deal-with-product1 part-of-new-var
                                           var-list
                                           pot-lst-to-look-in
                                           (cdr pot-lst-to-step-down)
                                           products-already-tried)
                       :obj nil ; ignored
                       :geneqv nil ; ignored
                       :pequiv-info nil ; ignored
                       :ttree nil ; ignored
                       :simplify-clause-pot-lst new-pot-list)))))
             (t
              (rewrite-entry
               (deal-with-product1 part-of-new-var
                                   var-list
                                   pot-lst-to-look-in
                                   (cdr pot-lst-to-step-down)
                                   products-already-tried)
               :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
               ))))))))

(defun deal-with-product (new-var pot-lst-to-look-in
                                  pot-lst-to-step-down
                                  products-already-tried ; &extra formals
                                  rdepth step-limit
                                  type-alist obj geneqv pequiv-info wrld state
                                  fnstack ancestors backchain-limit
                                  simplify-clause-pot-lst
                                  rcnst gstack ttree)

; If new-var is a product, we try to find a set of pots whose labels,
; when multiplied together, form new-var.  If we are successful at
; gathering such a set of pot labels, we will multiply the polys in those
; pots and add them to the simplify-clause-pot-lst.

; All the deal-with-xxx functions return four values: a new step-limit, the
; standard contradictionp, a potentially augmented pot-lst (or nil if
; contradictionp is true), and the accumulated list of products we have already
; tried.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   4
   (signed-byte 30)
   (cond
    ((eq (fn-symb new-var) 'BINARY-*)
     (rewrite-entry
      (deal-with-product1 new-var
                          nil
                          pot-lst-to-look-in
                          pot-lst-to-step-down
                          products-already-tried)
      :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
      ))
    (t
     (mv step-limit nil simplify-clause-pot-lst products-already-tried)))))

(defun deal-with-factor (new-var pot-lst-to-look-in
                                 pot-lst-to-step-down
                                 products-already-tried ; &extra formals
                                 rdepth step-limit
                                 type-alist obj geneqv pequiv-info
                                 wrld state
                                 fnstack ancestors backchain-limit
                                 simplify-clause-pot-lst
                                 rcnst gstack ttree)

; Pot-lst-to-look-in is the pot-lst we keep around to extract polys for
; multiplication from (see non-linear-arithmetic), and pot-lst-to-step-down
; is the pot-lst we cdr down as we recurse through this function.  They
; are initially the same.  Products-already-tried is an accumulator which
; keeps track of which pots we have already tried multiplying the polys from.

; In this function, we cdr down pot-lst-to-step-down to see whether
; new-var is a factor of any of its pot labels.  If so, we attempt to
; find a set of other pots (in pot-lst-to-look-in) whose labels are the
; remaining factors of the pot label found in pot-lst-to-step-down.
; If we are successful at gathering such a set of pot labels, we will
; multiply the polys in those pots and add them to the simplify-clause-pot-lst.

; All the deal-with-xxx functions return four values: a new step-limit, the
; standard contradictionp, a potentially augmented pot-lst (or nil if
; contradictionp is true), and the accumulated list of products we have already
; tried.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   4
   (signed-byte 30)
   (cond
    ((null pot-lst-to-step-down)
     (mv step-limit nil simplify-clause-pot-lst products-already-tried))
    (t
     (let ((part-of-pot-var (part-of new-var
                                     (access linear-pot
                                             (car pot-lst-to-step-down)
                                             :var))))
       (cond ((and part-of-pot-var
                   (not (equal new-var
                               (access linear-pot
                                       (car pot-lst-to-step-down)
                                       :var))))
              (sl-let
               (contradictionp new-pot-list products-already-tried)
               (rewrite-entry
                (deal-with-product1 part-of-pot-var
                                    (list new-var)
                                    pot-lst-to-look-in
                                    pot-lst-to-look-in
                                    products-already-tried)
                :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
                )
               (cond (contradictionp (mv step-limit
                                         contradictionp
                                         nil
                                         products-already-tried))
                     (t
                      (rewrite-entry
                       (deal-with-factor new-var
                                         pot-lst-to-look-in
                                         (cdr pot-lst-to-step-down)
                                         products-already-tried)
                       :obj nil ; ignored
                       :geneqv nil ; ignored
                       :pequiv-info nil ; ignored
                       :ttree nil ; ignored
                       :simplify-clause-pot-lst new-pot-list)))))
             (t
              (rewrite-entry
               (deal-with-factor new-var
                                 pot-lst-to-look-in
                                 (cdr pot-lst-to-step-down)
                                 products-already-tried)
               :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
               ))))))))

(defun deal-with-division (new-var inverse-var
                                   pot-lst-to-look-in
                                   pot-lst-to-step-down
                                   products-already-tried ; &extra formals
                                   rdepth step-limit
                                   type-alist obj geneqv pequiv-info
                                   wrld state
                                   fnstack ancestors backchain-limit
                                   simplify-clause-pot-lst
                                   rcnst gstack ttree)

; Inverse-var is the multiplicative inverse of new-var,
; pot-lst-to-look-in is the pot-lst we keep around to extract polys
; for multiplication from (see non-linear-arithmetic), and
; pot-lst-to-step-down is the pot-lst we cdr down as we recurse
; through this function.  They are initially the same pot
; list.  Products-already-tried is an accumulator which keeps track of
; which pots we have already tried multiplying the polys from.

; Division can cause problems.  For a simple example, consider:
; p1: 0 < b
; p2: b < a
; and imagine we are trying to prove
; p: 1 < a/b.
; by adding its negation and looking for a contradiction.
; The presence of the /b in the pot will cause inverse-polys to give us
; p3: 0 < 1/b
; But deal-with-factors and deal-with-products will not have a poly
; ``about'' a to multiply p3 by, because a is not the heaviest term in
; any poly.  Rather, what we want to do is multiply p3 and p2 since
; b/b = 1.  (Note that before we invoke deal-with-division, we insure
; that we have good bounds for b in the pot.  This insures that b/b
; disappears without a case split.)

; Another example is that
; p1: 0 < a
; p2: a < b
; imply
; p: 1 < b/a.
; The last will be stored as
; p3: b/a <= 1.
; If we multiply p1 and p3 and cancel we get
; p4: 0 <= a - b
; or
; p4: b <= a
; which contradicts p2.

; So, what we do here is see if there is a pot whose label has inverse-var
; as a factor, and, if so, multiply two sets of polys and add the
; resultant polys to the pot-lst.  The two sets of polys we multiply are:
; (1) The bounds polys of new-var with the polys of the found pot, and
; (2) the polys of new-var with the bounds polys of the found pot.

; All the deal-with-xxx functions return four values: a new step-limit, the
; standard contradictionp, a potentially augmented pot-lst (or nil if
; contradictionp is true), and the accumulated list of products we have already
; tried.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   4
   (signed-byte 30)
   (cond ((null pot-lst-to-step-down)
          (mv step-limit nil simplify-clause-pot-lst products-already-tried))
         (t

; The part-of expression asks the question, ``Is inverse-var a factor
; of the first pot label in pot-lst-to-step-down?''  It returns either
; nil, meaning no, or the naive result of dividing the pot label by
; inverse-var.

          (let ((part-of (part-of inverse-var (access linear-pot
                                                      (car pot-lst-to-step-down)
                                                      :var))))
            (cond (part-of
                   (sl-let
                    (contradictionp new-pot-lst products-already-tried)
                    (rewrite-entry
                     (add-multiplied-polys-filter
                      (list new-var
                            (access linear-pot
                                    (car pot-lst-to-step-down)
                                    :var))
                      products-already-tried
                      pot-lst-to-look-in)
                     :obj nil ; ignored
                     :geneqv nil ; ignored
                     :pequiv-info nil ; ignored
                     :ttree nil ; ignored
                     )
                    (cond (contradictionp
                           (mv step-limit contradictionp nil nil))
                          (t
                           (rewrite-entry
                            (deal-with-division new-var inverse-var
                                                pot-lst-to-look-in
                                                (cdr pot-lst-to-step-down)
                                                products-already-tried)
                            :obj nil ; ignored
                            :geneqv nil ; ignored
                            :pequiv-info nil ; ignored
                            :ttree nil ; ignored
                            :simplify-clause-pot-lst new-pot-lst)))))
                  (t
                   (rewrite-entry
                    (deal-with-division new-var inverse-var
                                        pot-lst-to-look-in
                                        (cdr pot-lst-to-step-down)
                                        products-already-tried)
                    :obj nil ; ignored
                    :geneqv nil ; ignored
                    :pequiv-info nil ; ignored
                    :ttree nil ; ignored
                    ))))))))

(defun non-linear-arithmetic1 (new-vars pot-lst ;;; to look-in/step-down
                                        products-already-tried ; &extra formals
                                        rdepth step-limit type-alist obj
                                        geneqv pequiv-info
                                        wrld state
                                        fnstack ancestors backchain-limit
                                        simplify-clause-pot-lst
                                        rcnst gstack ttree)

; This is the recursive version of function non-linear-arithmetic.  See the
; comments and documentation there.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (cond
    ((null new-vars)
     (mv step-limit nil simplify-clause-pot-lst))
    (t
     (let ((inverted-var (invert-var (car new-vars))))
       (sl-let
        (contradictionp new-pot-lst1 products-already-tried)

; Inverse-var is the multiplicative inverse of var.  Within deal-with-division
; we are going multiply var and inverse-var in order to cancel them with
; each other.  There are two cases in which this cancellation can occur:
; (1) We know that var and inverse-var are non-zero so their product is
; one.  (2) We know that var and inverse var are zero so their product is
; zero.  Good-bounds-in-pot determines this for us and allows us to avoid
; case-splits.

        (if (good-bounds-in-pot inverted-var
                                pot-lst
                                (access rewrite-constant rcnst :pt))
            (rewrite-entry
             (deal-with-division (car new-vars)
                                 inverted-var
                                 pot-lst ; to-look-in
                                 pot-lst ; to-step-down
                                 products-already-tried)
             :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
             )
          (mv step-limit nil simplify-clause-pot-lst products-already-tried))
        (cond (contradictionp (mv step-limit contradictionp nil))
              (t
               (sl-let (contradictionp new-pot-lst2 products-already-tried)
                       (rewrite-entry
                        (deal-with-product (car new-vars)
                                           pot-lst ; to-look-in
                                           pot-lst ; to-step-down
                                           products-already-tried)
                        :obj nil ; ignored
                        :geneqv nil ; ignored
                        :pequiv-info nil ; ignored
                        :ttree nil ; ignored
                        :simplify-clause-pot-lst new-pot-lst1)
                       (cond
                        (contradictionp (mv step-limit contradictionp nil))
                        (t
                         (sl-let
                          (contradictionp new-pot-lst3 products-already-tried)
                          (rewrite-entry
                           (deal-with-factor (car new-vars)
                                             pot-lst ; to-look-in
                                             pot-lst ; to-step-down
                                             products-already-tried)
                           :obj nil ; ignored
                           :geneqv nil ; ignored
                           :pequiv-info nil ; ignored
                           :ttree nil ; ignored
                           :simplify-clause-pot-lst new-pot-lst2)
                          (cond
                           (contradictionp (mv step-limit contradictionp nil))
                           (t
                            (rewrite-entry
                             (non-linear-arithmetic1
                              (cdr new-vars)
                              pot-lst ; to look-in/step-down
                              products-already-tried)
                             :obj nil ; ignored
                             :geneqv nil ; ignored
                             :pequiv-info nil ; ignored
                             :ttree nil ; ignored
                             :simplify-clause-pot-lst
                             new-pot-lst3)))))))))))))))

(defun non-linear-arithmetic (new-vars pot-lst ;;; to look-in/step-down
                                       products-already-tried ; &extra formals
                                       rdepth step-limit
                                       type-alist obj geneqv pequiv-info
                                       wrld state
                                       fnstack ancestors backchain-limit
                                       simplify-clause-pot-lst
                                       rcnst gstack ttree)

; New-vars is a list of pot labels or factors thereof.  We think of it
; as the labels of newly added pots, analogous to new-vars in
; add-polys-and-lemmas1.

; We cdr down the list of new-vars, calling the deal-with-xxx functions
; on the way.  The basic idea is that if a new var is a product and we have
; polys about both factors, then we can multiply those polys together to
; form polys about the new var.  We are thus using the lemma

; 0 < a & 0 < b -> 0 < a*b  (for rational a and b)

; We ``deal with'' new vars of the form a*b, a/b.  Analogously, if we
; have a new var of the form a we look to see whether we have an old
; pot about a*b and if so, look for a pot about b, etc.  That is, we try
; not to be sensitive to the order in which the pots a, b, and a*b are
; added.

; We do not handle terms like (* a (* a (* a a))) very well.  We
; anticipate that such terms will be normalized into expt expressions
; anyway.  So handling them here may not be too helpful.

; Unfortunately, we do not handle (expt a i) very well either.  We do
; know that (expt a -2) is the inverse of (expt a 2).  But we do not
; know that (expt a 2) is a*a or any of the analogous higher-order
; facts.  This is an obvious subject for future work.

; Note that we keep around the original pot-lst.  We have found this
; heuristic useful to prevent excessive effort on the part of
; non-linear arithmetic.  After running a large number of tests, we
; have found that the polys which we wished to multiply were almost
; always present in the original pot-lst and that much time can be
; saved this way.  Perhaps in a few more years when computers are even
; faster than they are now (2002) this should be revisited.

; Products-already-tried is an accumulator which keeps track of which pots
; we have already tried multiplying the polys from.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (cond
    ((null new-vars)
     (mv step-limit nil simplify-clause-pot-lst))
    (t
     (let ((gstack (push-gframe 'non-linear-arithmetic nil new-vars))
           (rdepth (adjust-rdepth rdepth)))
       (declare (type (unsigned-byte 29) rdepth))
       (rewrite-entry
        (non-linear-arithmetic1 new-vars pot-lst products-already-tried)
        :obj    nil      ; ignored
        :geneqv nil      ; ignored
        :pequiv-info nil ; ignored
        :ttree  nil      ; ignored
        ))))))

(defun add-polys-and-lemmas2-nl (new-vars old-pot-lst ; &extra formals
                                          rdepth step-limit
                                          type-alist obj geneqv pequiv-info
                                          wrld state
                                          fnstack ancestors backchain-limit
                                          simplify-clause-pot-lst
                                          rcnst gstack ttree)

; In add-polys-and-lemmas1, it is said that:

; To the simplify-clause-pot-lst, we add lemmas for every var
; in new-vars, generating a new pot-lst.  Then if that new pot-lst has
; new vars in it (relative to old-pot-lst) we repeat for those vars.
; We return the standard contradictionp and a new pot-lst.

; This is analogous to add-polys-and-lemmas1, but we also add
; polys gleaned from other sources than add-linear-lemmas, namely
; from the type-alist and ``inverse'' polys (which picks up facts about
; division).

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (cond
    ((null new-vars)
     (let ((new-vars (expanded-new-vars-in-pot-lst simplify-clause-pot-lst
                                                   old-pot-lst)))
       (cond ((null new-vars)
              (mv step-limit nil simplify-clause-pot-lst))
             (t (rewrite-entry
                 (add-polys-and-lemmas2-nl new-vars
                                           simplify-clause-pot-lst)
                 :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
                 )))))
    (t
     (mv-let
      (contradictionp new-pot-lst)
      (add-polys-from-type-set (car new-vars)
                               simplify-clause-pot-lst
                               type-alist
                               (access rewrite-constant rcnst :pt)
                               (ok-to-force rcnst)
                               (access rewrite-constant rcnst
                                       :current-enabled-structure)
                               wrld)
      (cond
       (contradictionp (mv step-limit contradictionp nil))
       (t
        (sl-let
         (contradictionp new-pot-lst)
         (if (and (nvariablep (car new-vars))
                  (not (flambda-applicationp (car new-vars)))
                  (not (access rewrite-constant rcnst :cheap-linearp)))
             (rewrite-entry
              (add-linear-lemmas (car new-vars)
                                 (getpropc (ffn-symb (car new-vars))
                                          'linear-lemmas nil wrld))
              :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
              :simplify-clause-pot-lst new-pot-lst)
           (mv step-limit nil new-pot-lst))
         (cond
          (contradictionp (mv step-limit contradictionp nil))
          (t
           (mv-let (contradictionp new-pot-lst)
                   (add-inverse-polys (car new-vars)
                                      type-alist wrld new-pot-lst
                                      (ok-to-force rcnst)
                                      (access rewrite-constant rcnst
                                              :current-enabled-structure)
                                      (access rewrite-constant rcnst :pt))
                   (cond (contradictionp (mv step-limit contradictionp nil))
                         (t (rewrite-entry
                             (add-polys-and-lemmas2-nl (cdr new-vars)
                                                       old-pot-lst)
                             :obj nil ; ignored
                             :geneqv nil ; ignored
                             :pequiv-info nil ; ignored
                             :ttree nil ; ignored
                             :simplify-clause-pot-lst new-pot-lst))))))))))))))

(defun add-polys-and-lemmas1-nl (old-pot-lst cnt ; &extra formals
                                             rdepth step-limit
                                             type-alist obj geneqv pequiv-info
                                             wrld state
                                             fnstack ancestors
                                             backchain-limit
                                             simplify-clause-pot-lst
                                             rcnst gstack ttree)

; When doing non-linear arithmetic, we use this function rather than
; the add-polys-and-lemmas1.  It is a wrapper for add-polys-and-lemmas2-nl
; which is similar in function to add-polys-and-lemmas1.

; We start by calling add-polys-and-lemmas2-nl with an expanded list of pot
; vars which are new to the simplify-clause-pot-lst (relative to old-pot-lst).
; Add-polys-and-lemmas2-nl augments simplify-clause-pot-lst, creating
; new-pot-lst1.

; We next call non-linear-arithmetic with a list of all the pot vars which are
; new to new-pot-lst1 (relative, again, to old-pot-lst).  Non-linear-arithmetic
; augments new-pot-lst1, creating new-pot-lst2.

; Finally, we recursively call ourselves, replacing the
; simplify-clause-pot-lst with new-pot-lst2 and old-pot-lst with new-pot-lst1.
; We thereby avoid calling add-polys-and-lemmas1 with any of the vars which
; it has already seen.

; When we recursively call ourselves we also increment the value of the
; variable cnt, and then check its value upon entry.  If it is greater than
; or equal to *non-linear-rounds-value*, we return rather than proceeding.
; This heuristic has proved an easy way to prevent excessive effort in
; non-linear arithmetic.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (cond
    ((<= *non-linear-rounds-value* cnt)
     (mv step-limit nil simplify-clause-pot-lst))
    (t

; Since we are doing non-linear arithmetic, we want to gather information not
; only on the new-vars, but also on the factors of any new-vars which are
; products.  Expanded-new-vars-in-pot-lst does this for us.  Note that the list
; of new-vars returned by expanded-new-vars-in-pot-lst may include variable
; symbols, unlike the list returned by new-vars-in-pot-lst with
; include-variableps = nil.

     (let ((new-vars (expanded-new-vars-in-pot-lst simplify-clause-pot-lst
                                                   old-pot-lst)))
       (sl-let
        (contradictionp new-pot-lst1)
        (cond
         ((null new-vars)
          (mv step-limit nil simplify-clause-pot-lst))

; We used to test for (null new-vars) in the outer cond, and simply return if
; it was true.  See also the comment following the call to new-vars-in-pot-lst
; below.

         (t

; This call to add-polys-and-lemmas2-nl is stronger than a corresponding call
; to add-polys-and-lemmas1, in the sense that it may add additional facts to
; simplify-clause-pot-lst.

          (rewrite-entry
           (add-polys-and-lemmas2-nl new-vars old-pot-lst)
           :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
           )))
        (cond
         (contradictionp (mv step-limit contradictionp nil))
         (t
          (let ((new-vars (new-vars-in-pot-lst new-pot-lst1 old-pot-lst t)))

; By using include-variableps = t in our call of new-vars-in-pot-lst, and
; moving the test above for (null new-vars) to its present location, we pick up
; theorems such as the following.

;    (include-book "arithmetic-3/bind-free/top" :dir :system)
;    (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
;                                                  hist pspv)))
;    (thm
;     (implies (and (rationalp a)
;                   (rationalp b)
;                   (rationalp c)
;                   (< 0 a)
;                   (< b 0)
;                   (< 0 (* a c))
;                   (< 0 (* b c)))
;              (equal c 0))
;     :hints (("Goal" :in-theory (disable |(< 0 (* x y))|))))

            (cond
             ((null new-vars)
              (mv step-limit nil new-pot-lst1))
             (t
              (sl-let (contradictionp new-pot-lst2)
                      (rewrite-entry
                       (non-linear-arithmetic new-vars new-pot-lst1 nil)
                       :obj nil ; ignored
                       :geneqv nil ; ignored
                       :pequiv-info nil ; ignored
                       :ttree nil ; ignored
                       :simplify-clause-pot-lst new-pot-lst1)
                      (cond
                       (contradictionp (mv step-limit contradictionp nil))
                       (t
                        (rewrite-entry
                         (add-polys-and-lemmas1-nl new-pot-lst1 (1+ cnt))
                         :obj nil ; ignored
                         :geneqv nil ; ignored
                         :pequiv-info nil ; ignored
                         :ttree nil ; ignored
                         :simplify-clause-pot-lst new-pot-lst2)))))))))))))))

(defun add-polys-and-lemmas1 (new-vars old-pot-lst ; &extra formals
                                       rdepth step-limit
                                       type-alist obj geneqv pequiv-info
                                       wrld state fnstack ancestors
                                       backchain-limit
                                       simplify-clause-pot-lst
                                       rcnst gstack ttree)

; To the simplify-clause-pot-lst, we add lemmas for every var
; in new-vars, generating a new pot-lst.  Then if that new pot-lst has
; new vars in it (relative to old-pot-lst) we repeat for those vars.
; We return the standard contradictionp and a new pot-lst.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (cond
    ((null new-vars)
     (let ((new-vars (new-vars-in-pot-lst simplify-clause-pot-lst
                                          old-pot-lst
                                          nil)))
       (cond ((null new-vars)
              (mv step-limit nil simplify-clause-pot-lst))
             (t (rewrite-entry
                 (add-polys-and-lemmas1 new-vars
                                        simplify-clause-pot-lst)
                 :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
                 )))))
    (t (sl-let
        (contradictionp new-pot-lst)
        (cond
         ((or (flambda-applicationp
               (car new-vars))
              (access rewrite-constant rcnst :cheap-linearp))
          (mv step-limit nil simplify-clause-pot-lst))
         (t
          (rewrite-entry
           (add-linear-lemmas (car new-vars)
                              (getpropc
                               (ffn-symb (car new-vars))
                               'linear-lemmas nil wrld))
           :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
           )))
        (cond
         (contradictionp (mv step-limit contradictionp nil))
         (t (rewrite-entry
             (add-polys-and-lemmas1 (cdr new-vars)
                                    old-pot-lst)
             :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
             :simplify-clause-pot-lst new-pot-lst))))))))

(defun add-polys-and-lemmas (lst disjunctsp ; &extra formals
                                 rdepth step-limit
                                 type-alist obj geneqv pequiv-info wrld state
                                 fnstack ancestors
                                 backchain-limit
                                 simplify-clause-pot-lst rcnst gstack ttree)

; We add all the polys in lst to the simplify-clause-pot-lst
; and then add the lemmas triggered by all the new variables.

; We return two results: the standard contradictionp and a new pot-lst.

; Important Observation about Applicative Programming: In nqthm, this
; function was called add-equations-to-pot-lst.  Isn't this a better
; name?  The advantage to rewriting a megabyte of code applicatively
; is that you get to think of better names for everything!

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (mv-let
    (contradictionp new-pot-lst)
    (add-polys lst simplify-clause-pot-lst
               (access rewrite-constant rcnst :pt)
               (access rewrite-constant rcnst :nonlinearp)
               type-alist
               (access rewrite-constant rcnst
                       :current-enabled-structure)
               (ok-to-force rcnst)
               wrld)
    (cond
     (contradictionp (mv step-limit contradictionp nil))

; The defthm below used to fail.  This failure was caused by our use of the
; test (and (access rewrite-constant rcnst :nonlinearp) (not disjunctsp)) to
; determine when to use nonlinear arithmetic.  This prevented the use of
; nonlinear arithmetic whenever there were disjunctive polys, but this was too
; restrictive.  We now use nonlinear arithmetic on disjunct polys that are
; derived from the goal, but not those that arise while backchaining.  Some
; type of limitation is needed as we have seen much thrashing in the arithmetic
; procedures when we were too liberal.  (Thanks to Robert Krug for providing
; this modification.)

;    ; This example was supplied by Julien Schmaltz.
;
;    (include-book "arithmetic-3/bind-free/top" :dir :system)
;    (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
;    (set-non-linearp t)
;    (defthm foo
;      (implies (and (integerp a) (integerp b)
;                    (< 0 a) (< 0 b)
;                    (equal (len l) (* a b)))
;               (equal (floor (len l) a)
;                      b))
;      :hints (("GOAL"
;               :do-not '(eliminate-destructors generalize fertilize)
;               :do-not-induct t))
;      :rule-classes nil)

; We can get here by two routes.  We could have been called by
; add-terms-and-lemmas or add-disjunct-polys-and-lemmas.  In the
; latter case we are "speculatively" trying to get a contradiction
; from one disjunct so we can simplify things to the other disjunct.
; But non-linear is very expensive.  We choose not to try it in this
; "speculative" case during backchaining even if non-linear is
; otherwise enabled.

     ((and (access rewrite-constant rcnst :nonlinearp)
           (or (not disjunctsp)
               (null ancestors)))
      (rewrite-entry
       (add-polys-and-lemmas1-nl simplify-clause-pot-lst 0)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       :simplify-clause-pot-lst new-pot-lst))
     (t
      (rewrite-entry
       (add-polys-and-lemmas1 (new-vars-in-pot-lst new-pot-lst
                                                   simplify-clause-pot-lst
                                                   nil)
                              new-pot-lst)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       :simplify-clause-pot-lst new-pot-lst))))))

(defun add-disjunct-polys-and-lemmas (lst1 lst2 ; &extra formals
                                           rdepth step-limit
                                           type-alist obj geneqv pequiv-info
                                           wrld state
                                           fnstack ancestors
                                           backchain-limit
                                           simplify-clause-pot-lst
                                           rcnst gstack ttree)

; We try to construct a pot-lst from the simplify-clause-pot-lst
; by assuming the disjunction of the polys in lst1 and lst2.  But since
; pot lists can only represent conjunctions, we are forced to take a weak
; approach:  we can assume lst1 if the assumption of lst2 produces a
; contradiction and vice versa.  If both are contradictory, we return
; the standard contradiction result.  Otherwise we return a (possibly) new
; pot-lst.

; The hard part of this procedure is keeping track of dependencies.
; If lst1 is contradictory, we must infect lst2 with the ttree of the
; contradiction, since the assumption of lst2 is dependent upon the
; proof that lst1 is contradictory.  We must do the symmetric thing if
; lst2 proves to be contradictory.  But here we are in an efficiency
; bind.  We have already created the assumption of
; simplify-clause-pot-lst and lst1 and do not want to re-create it
; after infecting lst1 with the ttree from the refutation of lst2.  So
; we visit the modified pot-lst after the fact, if lst2 is contradictory,
; and add the appropriate ttree.

; Historical Note: In nqthm we handled this problem by infecting the
; polys of lst1 with a special mark (a fresh cons) in the lemmas field
; of the poly before we added them to the pot-lst.  If lst2 gave a
; contradiction, we scanned the pot-lst produced by lst1 looking for
; all polys containing that (eq) cons.  During the initial attempts to
; code linear applicatively we tried to mimic this by using a 'mark
; tag in the tag-tree and inventing a "new" mark, such as an integer
; that was associated with the simplify-clause-pot-lst and was
; increased here when we obtained the mark.  We could not find a
; convincing way to generate a new mark.  The problem is due to the
; recursive rewriting done to add :LINEAR lemmas.  How do we know a
; mark generated now will still be new when it needs to be?  How do we
; know that a term rewritten in an extension of this pot-lst under us,
; doesn't have some marks in its tag-tree that will come back to haunt
; us?  These questions may have cut and dried answers that make marks
; viable.  But we decided not to pursue them and just identify the new
; polys as done here.  This exercise does point to the convenience of
; being able to use cons to generate a unique object.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (sl-let
    (contradictionp new-pot-lst1)
    (rewrite-entry
     (add-polys-and-lemmas lst1 t)
     :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
     )
    (cond
     (contradictionp

; So the first disjunct, lst1, has led to a contradiction.  We will
; infect the polys in lst2 with the ttree of that contradiction and
; and add them to the original pot list.

      (rewrite-entry
       (add-polys-and-lemmas (infect-polys lst2
                                           (access poly contradictionp
                                                   :ttree)
                                           (collect-parents
                                            (access poly contradictionp
                                                    :ttree)))
                             t)
       :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
       ))
     (t

; The first disjunct did not lead to a contradiction.  Perhaps the
; second one will...

      (sl-let
       (contradictionp new-pot-lst2)
       (rewrite-entry
        (add-polys-and-lemmas lst2 t)
        :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
        )
       (declare (ignore new-pot-lst2))
       (cond (contradictionp

; So the second disjunct, lst2, has led to a contradiction and we may
; use new-pot-lst1, the result of assuming lst1, as the result of
; assuming their disjunction.  But we must infect, with the ttree from
; the contradiction, all the polys in new-pot-lst1 derived from lst1.
; That set is just all the polys in new-pot-lst1 that are not in
; simplify-clause-pot-lst.

              (mv step-limit
                  nil
                  (infect-new-polys
                   new-pot-lst1
                   simplify-clause-pot-lst
                   (access poly contradictionp :ttree))))
             (t (mv step-limit nil simplify-clause-pot-lst)))))))))

(defun add-disjuncts-polys-and-lemmas (split-lst to-do-later
                                                 pot-lst0 ; &extra formals
                                                 rdepth step-limit
                                                 type-alist obj
                                                 geneqv pequiv-info wrld state
                                                 fnstack ancestors
                                                 backchain-limit
                                                 simplify-clause-pot-lst
                                                 rcnst gstack ttree)

; Each element of split-lst is a doublet, (lst1 lst2).  Logically, we wish to
; conjoin to the simplify-clause-pot-lst the conjunction across split-lst of
; the disjunctions of each lst1 and lst2.  I.e., we wish to assume (and ... (or
; lst1 lst2) ...) and we wish to express this assumption as a pot-lst.  No way
; Jose.  Pot-lsts represent conjunctions of assumptions.  So instead we'll
; conjoin lst1 into the pot list and lst2 into the pot list and hope one or the
; other gives a contradiction.  If not, we'll just discard that doublet and try
; the others.  But if one gives a contradiction, then we can go with the
; assumption of the other as the assumption of their disjunction.  There is a
; subtlety here however: the assumption of lst2 in place of (or lst1 lst2)
; depends upon the refutation of lst1 and hence we must infect the polys from
; lst2 with the ttree arising from the refutation of lst1.  And vice versa.
; See add-disjunct-polys-and-lemma.

; We return (mv sl contradictionp pot-lst changedp), where sl is the new
; step-limit, and contradictionp and pot-lst are the standard contradictionp
; and a new pot-lst.  When contradictionp is nil then, normally, changedp is t
; if and only if the input and output pot-lst differ; however, we do not insist
; on this, as changedp is to be used only heuristically.

; The to-do-later list was first present in Version 1.6, and represents an
; attempt to make the order of the split-lst irrelevant.  The idea is that if a
; doublet in the split-lst must be "discarded" as noted above, then we actually
; save that doublet on to-do-later and try it again after processing the
; others.  Here is a long message that explains the problem; the message was
; sent to Bishop Brock, who first reported the problem, on March 31, 1994,

; I have fixed the "bug" that prevented us from proving

; (thm
;  (IMPLIES
;   (AND (INTEGERP N)
;        (NOT (< N 0))
;        (NOT (< 4 N))
;        (NOT (EQUAL N 2))
;        (NOT (EQUAL N 0))
;        (NOT (EQUAL N 1))
;        (NOT (EQUAL N 3)))
;   (EQUAL N 4)))

; To understand what I did, consider a proof that works, e.g.,
;  (IMPLIES (AND (INTEGERP N)
;              (NOT (< N 0))
;              (NOT (< 4 N))
;              (NOT (EQUAL N 0))
;              (NOT (EQUAL N 1))
;              (NOT (EQUAL N 2))
;              (NOT (EQUAL N 3)))
;         (EQUAL N 4))

; The arithmetic hyps are stored in the linear inequalities database by the
; linear arithmetic package.  That database represents a conjunction of
; inequalities.  The first two inequalities give us

;  0 <= N <= 4

; Now we come to the hard part.  In general, we cannot represent (NOT (EQUAL x
; y)) as a conjunction of inequalities.  It turns into a DISjunction, namely,
; either x < y or y < x.  Thus, if we are asked to add (NOT (EQUAL x y)) to the
; linear database we try adding x < y.  If that gives us a contradiction, then
; we know y < x and we add that.  Alternatively, if x < y doesn't give us a
; contradiction, but y < x does, we can assume x < y.  If neither gives us a
; contradiction, we simply can't represent (NOT (EQUAL x y)) in the linear
; database.  Note that to get any linear information out of (NOT (EQUAL x y))
; we must get a contradiction from one of the two disjuncts.

; When you process the hypotheses in the "wrong" order, you don't always get a
; contradiction and so we effectively drop one or more of the inequalities and
; lose.

; Consider one of the many "right" orders first, in particular the proof that
; works above.  The first NOT EQUAL we process is (NOT (EQUAL N 0)).  Because N
; is an integer, this is equivalent to either N <= -1 or 1 <= N.  The linear
; database we have initially is

;  0 <= N <= 4.

; When we add N <= -1 we get a contradiction, by clashing 0 <= N with N <= -1
; and deriving 0 <= -1.  Since we got a contradiction on one disjunct we can
; assume the other.  Adding 1 <= N to the above database gives us

;  1 <= N <= 4.

; Note that we are now in a position to successfully process (NOT (EQUAL N 1)),
; because it becomes either N <= 0 (contradiction) or 2 <= N, and thus we get

;  2 <= N <= 4.

; As you can see, we can keep narrowing the known interval as long as the hyp
; we process is beyond the current known endpoints.  We can work at either
; endpoint and so there are many "right" orders.  (In the case of the 5-way
; case split on N=0,1,2,3,4, there are 90 right orders and 30 wrong ones out of
; the 120 permutations.)

; Now consider one of the "wrong" orders.  If we know

;  0 <= N <= 4

; and we first process (NOT (EQUAL N 1)) then we must get a contradiction from
; either N <= 0 or from 2 <f= N.  But neither of these is contradictory yet.
; So in Version 1.5 (and Nqthm!) we just ignore that NOT EQUAL hyp (as far as
; linear arithmetic is concerned).  Once we've ignored any one hyp, the game is
; lost.

; In Version 1.6 the success of linear is independent of the order in which the
; inequalities are presented.  I do this by keeping a list of the ones I had
; tried to add but couldn't, i.e., the ones that Version 1.5 decided to ignore.
; Call that list the "to-do-later list".  I process all the hyps and get a
; database and a to-do-later list.  Then I reprocess the to-do-later list and
; see if any can be added now.  I iterate until either I've added them all or
; no changes happen.

; In the case of inequalities about variable symbols this is very very fast.
; In the case of inequalities about arbitrary terms, e.g., (NOT (EQUAL (FOO
; (BAR X Y)) 2)), it can be slow because every time we add an inequality we go
; look in the :LINEAR lemmas database for more facts about that term.  But I
; think this problem doesn't arise too often and I think we'll find Version 1.6
; better than Version 1.5 and seldom any slower.

; Thank you very much Bishop for noticing this problem.  It is amazing to me
; that it survived all those years in Nqthm without coming to our attention.

  (declare (ignore obj geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   4
   (signed-byte 30)
   (cond
    ((null split-lst)
     (let ((eqp (equal pot-lst0 simplify-clause-pot-lst)))
       (cond
        ((or eqp
             (null to-do-later))
         (mv step-limit nil simplify-clause-pot-lst (not eqp)))
        (t (sl-let
            (contradictionp pot-lst changedp)
            (rewrite-entry
             (add-disjuncts-polys-and-lemmas to-do-later nil
                                             simplify-clause-pot-lst)
             :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored)
             )
            (declare (ignore changedp))
            (mv step-limit contradictionp pot-lst t))))))
    (t (sl-let (contradictionp new-pot-lst)
               (rewrite-entry
                (add-disjunct-polys-and-lemmas (car (car split-lst))
                                               (cadr (car split-lst)))
                :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
                )
               (cond (contradictionp (mv step-limit contradictionp nil nil))
                     (t (rewrite-entry
                         (add-disjuncts-polys-and-lemmas
                          (cdr split-lst)
                          (if (equal new-pot-lst simplify-clause-pot-lst)
                              (cons (car split-lst) to-do-later)
                            to-do-later)
                          pot-lst0)
                         :obj nil          ; ignored
                         :geneqv nil       ; ignored
                         :pequiv-info nil  ; ignored
                         :ttree nil        ; ignored
                         :simplify-clause-pot-lst new-pot-lst))))))))

(defun add-terms-and-lemmas (term-lst ttrees positivep
                                      ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv pequiv-info
                                      wrld state
                                      fnstack ancestors
                                      backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)

; Term-lst is a list of terms to be assumed true (if positivep) or false (if
; not positivep).  We linearize each term in term-lst and add the resulting
; polys and all lemmas we can to simplify-clause-pot-lst.  When we linearize a
; term we use the weakly corresponding element of ttrees as its tag-tree (if
; that element is non-nil).

; Only variables introduced by the addition of the new polys are considered
; new.

; This function returns 3 values.  The first is the new step-limit.  The second
; indicates that a linear contradiction arises from the assumption of term-lst
; as above.  When non-nil the second result is the impossible-poly generated.
; Its tag-tree contains all the necessary information.  In particular, if a
; contradiction is indicated then there is a proof of NIL from type-alist, the
; assumption of the terms in term-lst (as per positivep), the assumptions in
; the final tag-tree and some subset of the polys in the
; simplify-clause-pot-lst.

; If no contradiction is indicated then the third value is the new
; simplify-clause-pot-lst.  For each poly p in the new pot list there is a
; proof of p from type-alist, the assumption of the terms in term-lst (as per
; positivep) and the polys in the original pot list.

; Note that obj has an special use in this function.  Values t and nil for obj
; indicate, as usual, that we are in the process of trying to prove or falsify
; (respectively) the given terms; however, this function does not use obj for
; that purpose. (That said, obj is used in reports issued by cw-gframe and
; dmr-interp.)  The value '?, however, is a special mark that is used when
; setting up the pot-lst for a clause.  The desperation heuristic noted below,
; of making a second attempt to use linear lemmas after successfully using at
; least one disjunctive inequality, is invoked only when setting up the pot-lst
; (obj = '?).  We found it much too expensive in some cases without this
; restriction, as discussed in a comment in (deflabel note-8-4 ...) in the
; source documentation (see books/system/doc/acl2-doc.lisp).

  (declare (ignore geneqv pequiv-info ttree)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   3
   (signed-byte 30)
   (let ((gstack (push-gframe 'add-terms-and-lemmas nil term-lst obj))
         (rdepth (adjust-rdepth rdepth)))
     (declare (type (unsigned-byte 29) rdepth))
     (sl-let
      (term-lst ttree-lst)
      (if (and (access rewrite-constant rcnst :nonlinearp)
               (not (access rewrite-constant rcnst :cheap-linearp)))

; This call to rewrite-linear-term-lst is new to Version_2.7.
; We wish to be able to have a different normal form when doing
; linear and non-linear arithmetic than when doing normal rewriting.
; The terms in term-lst eventually get passed on to rewrite-linear-term
; where they are rewritten under a possibly changed current-enabled-structure.
; See the comments in cleanse-type-alist for a couple of oddities
; associated with this.

          (rewrite-entry
           (rewrite-linear-term-lst term-lst ttrees)
           :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
           )
        (mv step-limit term-lst ttrees))

; Back to the original show.

      (mv-let (poly-lst split-lst)
        (linearize-lst term-lst ttree-lst positivep
                       type-alist
                       (access rewrite-constant rcnst
                               :current-enabled-structure)
                       (ok-to-force rcnst)
                       wrld
                       state)
        (sl-let
         (contradictionp basic-pot-lst)
         (rewrite-entry
          (add-polys-and-lemmas poly-lst nil)
          :obj nil                ; ignored
          :geneqv nil             ; ignored
          :pequiv-info nil        ; ignored
          :ttree nil              ; ignored
          )
         (cond
          (contradictionp (mv step-limit contradictionp nil))
          (t
           (sl-let
            (contradictionp new-pot-lst changedp)
            (rewrite-entry
             (add-disjuncts-polys-and-lemmas
              split-lst
              nil
              basic-pot-lst)
             :obj nil                         ; ignored
             :geneqv nil                      ; ignored
             :pequiv-info nil                 ; ignored
             :ttree nil                       ; ignored
             :simplify-clause-pot-lst
             basic-pot-lst)
            (cond
             (contradictionp
              (mv step-limit contradictionp nil))
             ((and changedp
                   (eq obj '?) ; special mark for setting up the pot-lst

; The following test is what we use to enable so-called "desperation
; heuristics".

                   (eq (access rewrite-constant rcnst :rewriter-state)
                       'settled-down))
              (rewrite-entry

; We have seen an example where a proof fails unless we make one more pass at
; using linear lemmas after improving the pot-lst with
; add-disjuncts-polys-and-lemmas.  That same example fails when, instead of
; adding this call of add-polys-and-lemmas1 at the end, we add a call of
; add-disjuncts-polys-and-lemmas before the earlier call of
; add-polys-and-lemmas.

               (add-polys-and-lemmas1
                (new-vars-in-pot-lst new-pot-lst nil nil)
                new-pot-lst)
               :obj nil :geneqv nil :pequiv-info nil :ttree nil ; all ignored
               :simplify-clause-pot-lst new-pot-lst))
             (t (mv step-limit nil new-pot-lst))))))))))))

(defun rewrite-with-linear (term ; &extra formals
                            rdepth step-limit
                            type-alist obj geneqv pequiv-info wrld state
                            fnstack ancestors backchain-limit
                            simplify-clause-pot-lst rcnst gstack ttree)

; If term is an (in)equality, and obj is either 'T or 'NIL, we try
; to rewrite term using the arithmetic package.  If obj is 'T, we
; add the negation of term and hope for a contradictionp;
; otherwise we add term.  We thus pass (eq obj nil) for the
; positivep flag to add-terms-and-lemmas and thence linearize.

; We return 3 values, whether we rewrote term, the (possibly) new term,
; and the (possibly) new ttree.  If we rewrote term using the linear
; package we add the *fake-rune-for-linear* to the ttree.

; Historical Plaque from Nqthm:

;    We tried rewriting with linear under the objective ?, and it cost
;    us 4 million conses over a proveall, so we stopped rewriting with
;    linear under the objective ?.  We found that too restrictive, and
;    experimented with the idea of only rewriting with linear under ?
;    when ANCESTORS is nonNIL, i.e., when we are working on a term
;    that may appear as part of the simplification of the theorem as
;    opposed to a term that appears while rewriting the hypothesis of
;    a :REWRITE rule.  That cost us 5 times more conses on the theorem
;    it was designed to prove!  So we have abandoned linear under ?
;    altogether, again.  Here, however is the most recent experimental
;    code:

;    (COND ((AND (NULL ANCESTORS)
;                (EQ (ADD-TERM-TO-POT-LST TERM
;                                         SIMPLIFY-CLAUSE-POT-LST NIL NIL)
;                    (QUOTE CONTRADICTION)))
;           (SETQ ANS TRUE)
;           (GO WIN)))

;    (COND ((AND (NULL ANCESTORS)
;                (EQ (ADD-TERM-TO-POT-LST TERM SIMPLIFY-CLAUSE-POT-LST T NIL)
;                    (QUOTE CONTRADICTION)))
;           (SETQ ANS FALSE)
;           (GO WIN)))

; On a somewhat related note, we have briefly considered the possibility of
; supporting some weak kind of forward chaining when we enter the true and
; false branches of an IF, generalizing what we support with compound
; recognizer rules.

; (implies (unsigned-byte-p 4 x)
;          (< x 16))

; We have come up with at least the following reasons not to provide such
; support.

; - To take full advantage of such a rule we'd need assume-true-false to extend
;   the linear pot, which would likely be expensive, as discussed above.

; - IF calls generally work their way up to top-level case splits anyhow, with
;   two exceptions: backchaining and the tentative opening of recursive
;   functions.  Such a rule would only provide marginal help for these cases.
;   Note that recursive function calls can be forced open anyhow, using :expand
;   hints.

  (declare (ignore geneqv pequiv-info)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))

; Convention: It is our convention to pass nils into ignored &extra formals.
; Do not change the (ignore ...) declaration above without looking at the
; callers.  That is, if you change this function so that it uses the formals
; declared ignored above, you are making a mistake because all callers of this
; function pass nils into them.

  (the-mv
   4
   (signed-byte 30)
   (let ((positivep (eq obj nil)))
     (cond
      ((and (not (eq obj '?))
            (mv-let (not-flg atm)
                    (strip-not term)
                    (declare (ignore not-flg))
                    (or (equalityp atm)
                        (inequalityp atm))))
       (sl-let (contradictionp irrelevant-pot-lst)
               (rewrite-entry (add-terms-and-lemmas (list term)
                                                    nil ; pts
                                                    positivep)
                              :geneqv nil ; ignored
                              :pequiv-info nil ; ignored
                              :ttree nil ; ignored
                              )
               (declare (ignore irrelevant-pot-lst))
               (cond (contradictionp
                      (mv step-limit
                          t
                          (if positivep
                              *nil*
                            *t*)
                          (push-lemma
                           *fake-rune-for-linear*
                           (cons-tag-trees-rw-cache
                            (access poly contradictionp :ttree)
                            ttree))))
                     (t (mv step-limit nil term ttree)))))
      (t
       (mv step-limit nil term ttree))))))

(defun rewrite-quoted-constant-with-lemma
  (term lemma ; &extra formals
        rdepth step-limit
        type-alist obj geneqv pequiv-info wrld state
        fnstack ancestors
        backchain-limit
        simplify-clause-pot-lst rcnst gstack
        ttree)

; The structure of this function and its immediate,
; rewrite-quoted-constant-with-lemmas, is based on rewrite-with-lemma and
; rewrite-with-lemmas.  Term is a quoted evg, i.e., 'evg, and lemma is an
; enabled :rewrite-quoted-constant rule whose :heuristic-info field contains (n
; . loop-stopper), where n is the form number as per the Essay on Rewriting
; Quoted Constants:

; [1] (IMPLIES hyps (equiv 'lhs-evg 'rhs-evg))
; [2] (IMPLIES hyps (equiv (fn x) x)), where x is a variable.
; [3] (IMPLIES hyps (equiv lhs-term rhs-term))

; In all cases below, we check that equiv is a refinement of geneqv.  Roughly
; speaking, if n is 1 and evg is lhs-evg, we backchain to establish the hyps
; and if successful replace term by 'rhs-evg.  If n is 2 and backchaining
; succeeds and (fn 'evg) returns a non-erroneous result, we replace term with
; the quoted result.  If n is 3, we unify lhs-term with 'evg and if successful
; backchain and rewrite as with an ordinary rewrite rule.

; The four values returned by this function are: a new step-limit, t or nil
; indicating whether lemma was used to rewrite term, the rewritten version of
; term, and the final version of ttree.

; This function is a No-Change Loser modulo rw-cache: only the values of
; 'rw-cache-any-tag and 'rw-cache-nil-tag may differ between the input and
; output ttrees.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   4
   (signed-byte 30)
   (let* ((gstack (push-gframe 'rewrite-quoted-constant-with-lemma nil term lemma))
          (rdepth (adjust-rdepth rdepth))
          (temp (access rewrite-rule lemma :heuristic-info))
          (n (car temp))
          (loop-stopper (cdr temp)))
     (declare (type (unsigned-byte 29) rdepth)
              (type integer n))
     (cond ((zero-depthp rdepth)
            (rdepth-error
             (mv step-limit nil term ttree)))
           ((not (geneqv-refinementp (access rewrite-rule lemma :equiv)
                                     geneqv
                                     wrld))
            (mv step-limit nil term ttree))
           (t
; Note below we swap the lhs and rhs of form [2] rules!  The rule is written
; and stored as (equiv (fn var) var), but actually used as though it were
; (equiv var (fn var)), so in this code we actually let lhs be the var and rhs
; be the normalizer expression.

            (let ((lhs (if (eql n 2)
                           (access rewrite-rule lemma :rhs)
                           (access rewrite-rule lemma :lhs)))
                  (rhs (if (eql n 2)
                           (access rewrite-rule lemma :lhs)
                           (access rewrite-rule lemma :rhs)))
                  (rune (access rewrite-rule lemma :rune)))
              (mv-let (unify-ans unify-subst)
                (cond
                 ((eql n 1)
                  (mv (equal term lhs) nil))
                 ((eql n 2)
                  (mv t (list (cons lhs term))))
                 ((eql n 3)
                  (one-way-unify-restrictions
                   lhs
                   term
                   (cdr (assoc-equal
                         rune
                         (access rewrite-constant rcnst
                                 :restrictions-alist)))))
                 (t (mv nil
                        (er hard 'rewrite-quoted-constant-with-lemma
                            "We've encountered a :rewrite-quoted-constant ~
                             rule, namely ~x0, with an unrecognized form ~
                             number, ~x1."
                            rune
                            n))))
                (cond
                 ((and unify-ans
                       (null (brkpt1 lemma term unify-subst
                                     type-alist ancestors
                                     ttree
                                     gstack rcnst state)))
                  (cond
                   ((null (loop-stopperp loop-stopper unify-subst wrld))
                    (prog2$
                     (brkpt2 nil 'loop-stopper
                             unify-subst gstack nil nil
                             rcnst state)
                     (mv step-limit nil term ttree)))
                   (t
                    (with-accumulated-persistence
                     rune
                     ((the (signed-byte 30) step-limit) flg term ttree)
                     flg
                     (sl-let
                      (relieve-hyps-ans failure-reason unify-subst ttree)
                      (rewrite-entry
                       (relieve-hyps
                        rune
                        term
                        (access rewrite-rule lemma :hyps)
                        (access rewrite-rule lemma
                                :backchain-limit-lst)
                        unify-subst
                        (not (oncep (access rewrite-constant
                                            rcnst
                                            :oncep-override)
                                    (access rewrite-rule
                                            lemma
                                            :match-free)
                                    rune
                                    (access rewrite-rule
                                            lemma
                                            :nume))))
                       :obj nil         ; ignored
                       :geneqv nil      ; ignored
                       :pequiv-info nil ; ignored
                       )
                      (cond
                       (relieve-hyps-ans
                        (sl-let
                         (rewritten-rhs ttree)
                         (with-accumulated-persistence
                          rune
                          ((the (signed-byte 30) step-limit)
                           rewritten-rhs ttree)

; This rewrite of the body is considered a success unless the parent with-acc-p
; fails.

                          t
                          (rewrite-entry
                           (rewrite
                            rhs
                            unify-subst
                            'rhs))
                          :conc
                          (access rewrite-rule lemma :hyps))
                         (cond
                          ((or (eql n 1)
                               (and (eql n 2)
                                    (quotep rewritten-rhs)
                                    (not (equal term rewritten-rhs)))
                               (eql n 3))
                           (prog2$
                            (brkpt2 t nil unify-subst gstack rewritten-rhs
                                    ttree rcnst state)
                            (mv step-limit
                                t
                                rewritten-rhs
                                (push-lemma
                                 (geneqv-refinementp
                                  (access rewrite-rule lemma
                                          :equiv)
                                  geneqv
                                  wrld)
                                 (push-lemma+ rune ttree rcnst ancestors
                                              rhs
                                              rewritten-rhs)))))
                          (t (prog2$
; We can only get here if n is 2 but either rewritten-rhs is not a quote or
; it is equal to term.
                              (brkpt2 nil
                                      (list
                                       (if (quotep rewritten-rhs)
                                           'normalizer-returned-same-constant
                                           'normalizer-failed-to-evaluate)
                                       (sublis-var unify-subst rhs)
                                       rewritten-rhs)
                                      unify-subst gstack nil nil
                                      rcnst state)
                              (mv step-limit nil term ttree))))))
                       (t (prog2$
                           (brkpt2 nil failure-reason
                                   unify-subst gstack nil nil
                                   rcnst state)
                           (mv step-limit nil term ttree)))))))))
                 (t (mv step-limit nil term ttree))))))))))

(defun rewrite-quoted-constant-with-lemmas
  (term lemmas ; &extra formals
        rdepth step-limit
        type-alist obj geneqv pequiv-info wrld state
        fnstack ancestors backchain-limit
        simplify-clause-pot-lst rcnst gstack ttree)
; Term is a quoted evg.
  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   4
   (signed-byte 30)
   (cond
    ((null lemmas) (mv step-limit nil term ttree))
    ((not (enabled-numep
           (access rewrite-rule (car lemmas) :nume)
           (access rewrite-constant rcnst
                   :current-enabled-structure)))
     (rewrite-entry
      (rewrite-quoted-constant-with-lemmas term (cdr lemmas))))
    (t (sl-let
        (rewrittenp rewritten-term ttree)
        (rewrite-entry (rewrite-quoted-constant-with-lemma term (car lemmas)))
        (cond
         (rewrittenp
          (mv step-limit t rewritten-term ttree))
         (t (rewrite-entry
             (rewrite-quoted-constant-with-lemmas term (cdr lemmas))))))))))

(defun rewrite-quoted-constant (term ; &extra formals
                                rdepth step-limit
                                type-alist obj geneqv pequiv-info wrld state
                                fnstack ancestors backchain-limit
                                simplify-clause-pot-lst rcnst gstack ttree)

  (sl-let (rewrittenp rewritten-term ttree1)
          (rewrite-entry
           (rewrite-quoted-constant-with-lemmas
            term
            (global-val 'rewrite-quoted-constant-rules wrld)))
          (cond
           (rewrittenp
            (mv step-limit rewritten-term ttree1))
           ((fn-slot-from-geneqvp geneqv)
            (sl-let
             (evg1 ttree1)
             (rewrite-entry
              (rewrite-lambda-object (unquote term)))

; Rewrite-lambda-object is insensitive to the incoming ttree.  So ttree1
; does not include that tree and if we use evg1 above we have to cons
; ttree1 onto the existing ttree.

             (cond ((equal evg1 (unquote term))
                    (mv step-limit term ttree))
                   (t (mv step-limit
                          (kwote evg1)
                          (cons-tag-trees ttree1 ttree))))))
           (t (mv step-limit term ttree)))))

(defun rewrite-lambda-object (evg ; &extra formals
                              rdepth step-limit
                              type-alist obj geneqv pequiv-info wrld state
                              fnstack ancestors backchain-limit
                              simplify-clause-pot-lst rcnst gstack ttree)

; Evg is some evg and rewrite has been called on 'evg.  Furthermore, we know
; from geneqv that 'evg is in a :FN slot.  If evg is in fact a well-formed
; lambda object we attempt to rewrite its body, in a context-free way, carrying
; no external assumptions in and expanding no recursive functions in it.  (The
; last restriction is accomplished by pushing :rewrite-lambda-object on the
; fnstack, which signals rewrite-fncall not to open any recursive function.
; See the explanation of a simplify loop below.)  If the rewritten body is
; different, contains no free variables and is tame, we return a new lambda
; object with the rewritten body.  Coincidentally, we drop the optional DECLARE
; form permitted in lambda objects; we take no special action to eliminate
; RETURN-LAST because there is an abbreviation-style rewrite rule that will do
; that.  But if evg is not well-formed or its rewritten body is equal to the
; original body (and there is no DECLARE form) or it contains free variables,
; or it is not tame, we return evg unchanged.  In the case that a well-formed
; lambda object is rewritten but the rewritten body is rejected on the grounds
; of free variables or tameness, we print a "rewrite-lambda-object" warning,
; which can be inhibited if it gets annoying.  To inhibit the warning but leave
; all other warnings on, do (set-inhibit-warnings "rewrite-lambda-object").

; Explanation of an infinite simplify loop:

; Prior to using the :rewrite-lambda-object fnstack marker to shut off the
; expansion of recursive functions in rewrite-lambda-object we rewrote the body
; using the pre-existing fnstack.  This caused an infinite loop in the presence
; of loop$-recursive functions, at least in those whose only recursions were
; within loop$ although we didn't look for other infinite loops.  The simplest
; example involves the nonsensical defun and non-theorem below:

; (defun foo (x)
;   (declare (xargs :loop$-recursion t :measure (acl2-count x)))
;   (loop$ for e in x collect (foo e)))

; (thm (foo x))

; Goal (foo x) simplifies to Goal' (collect$ (lambda$ (iv)(foo iv)) x). But
; then the lambda object is rewritten with fnstack nil (because we're in a
; top-level goal) to produce Goal'' (collect$ (lambda$ (iv) (collect$ (lambda$
; (iv) (foo iv)) iv)) x), etc.

; To solve this we adopted the most radical solution: never open a recursive
; function while rewriting a lambda object.  This is accomplished in
; rewrite-fncall, by checking to see whether :rewrite-lambda-object is an
; element of the fnstack.  Less radical would be the idea of rewriting the call
; and deciding whether to keep it.  But since lambda bodies are simplified
; without any of the external context in which the lambda object occurs, the
; context of the call never changes.  So one has to ask why didn't the user
; just write what the recursive function would simplify to?  We may eventually
; see why a more sophisticated solution is needed.  But as a first cut we just
; don't open recursive functions in lambda bodies.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit)
           (ignore obj geneqv pequiv-info
                   ancestors simplify-clause-pot-lst))

  (the-mv
   3
   (signed-byte 30)
   (cond ((symbolp evg)

; We don't mess with evg if it is a symbol.  If we did, it would fail the first
; test below and report that the symbol was an ill-formed lambda object.  If
; the user wants to rewrite a quoted symbol occurring in a :FN position that is
; possible but he or she should prove a :rewrite-quoted-constant rule.

          (mv step-limit evg ttree))
         ((well-formed-lambda-objectp evg wrld)
          (let* ((formals (lambda-object-formals evg))
                 (dcl (lambda-object-dcl evg))
                 (body (lambda-object-body evg))
                 (type-alist1 (collect-0-ary-hyps type-alist))
                 (fns (all-fnnames body))
                 (progs (collect-programs fns wrld)))
            (mv-let (pre-have-warrants pre-have-no-warrants)
              (partition-userfns-by-warrantp fns wrld nil nil)

; Fns is the list of fns in body.  It does not include fns buried in quoted
; objects; they are handled by recursion.  Progs is the list of :program mode
; functions in fns, pre-have-warrants are the symbols in fns that have warrants
; (whether they're assumed in the current context or not), and
; pre-have-no-warrants are the symbols in fns for which no warrants exist but
; which would require a warrant to be apply$d.  (Primitives and apply$
; primitives don't have warrants but don't need them.)

              (cond
               ((and (null progs)
                     (null pre-have-no-warrants))

; So body is in :logic mode and every function symbol occurring in it has a
; warrant or doesn't need one.

                (sl-let
                 (rewritten-body ttree1)
                 (rewrite-entry (rewrite body
                                         nil
                                         'lambda-object-body)
                                :fnstack (cons :rewrite-lambda-object fnstack)
                                :type-alist type-alist1
                                :obj '?
                                :geneqv nil ; maintain EQUAL
                                :pequiv-info nil
                                :ancestors nil
                                :simplify-clause-pot-lst nil
                                :ttree nil)
                 (mv-let (rewritten-body1 ttree1)
                   (normalize rewritten-body
                              nil ; iff-flg
                              nil ; type-alist
                              (access rewrite-constant
                                      rcnst
                                      :current-enabled-structure)
                              wrld
                              ttree1
                              (backchain-limit wrld :ts))
                   (cond
                    ((equal rewritten-body1 body)
                     (cond
                      ((null dcl)
                       (mv step-limit evg ttree))
                      (t (mv step-limit
                             `(lambda ,formals ,body) ; Just drop the dcl
                             ttree))))
                    ((or (not (subsetp-eq (all-vars rewritten-body1) formals))
                         (not (executable-tamep rewritten-body1 wrld)))

; If the rewritten body contains free variables or is not tame, we reject this
; whole rewrite, after possibly printing a warning.

                     (prog2$ (rewrite-lambda-object-post-warning
                              evg rewritten-body nil ttree1 wrld)
                             (mv step-limit evg ttree)))
                    (t

; The replacement of body by rewritten-body (or, actually, by the normalized
; rewritten-body) inside a quoted lambda object depends on the equivalence of
; the ev$ of the quotations of those two terms.  We know that body is equal to
; rewritten-body, by the correctness of rewrite.  So the equivalence of the
; ev$s of their quotations is just analogous to the theorem justifying meta
; rules, except we need to know that (ev$ '(fn a1 ... an) env) = (fn (ev$ 'a1
; env) ... (ev$ 'an env)), for every function in either term.  (Note: here
; ``ev$'' is used where a suitable evaluator is used in metafunction
; correctness theorems.)  But we have that theorem for every apply$ primitive
; and for every apply$ boot function (provided the two terms are both tame),
; but we warrants for every userfn in either term.  (The tameness hypotheses
; required in the warrants are already assured by the tameness checks here, so
; we know we have badges, but not necessarily warrants.  We know all fns in
; rewritten-body1 are in :logic mode because it was produced by rewriting a
; :logic mode term and the rewriter never introduces a :program mode fn.)
; Furthermore, we don't just need the userfns to be warranted, we need to have
; each warrant hypothesis.  We ensure that by collecting all the warranted
; userfns functions occurring in either term and then calling push-warrants.

                     (mv-let (post-have-warrants post-have-no-warrants)
                       (partition-userfns-by-warrantp
                        (all-fnnames rewritten-body1)
                        wrld nil nil)
                       (cond
                        (post-have-no-warrants
                         (prog2$
                          (rewrite-lambda-object-post-warning
                           evg rewritten-body post-have-no-warrants ttree1
                           wrld)
                          (mv step-limit evg ttree)))
                        (t
                         (mv-let (erp ttree2)
                           (push-warrants (union-eq pre-have-warrants
                                                    post-have-warrants)
                                          body
                                          type-alist1
                                          (access rewrite-constant rcnst
                                                  :current-enabled-structure)
                                          wrld
                                          (ok-to-force rcnst)
                                          ttree1 ttree)

; Body, above, is passed in as the ``target'' for push-warrants.  The target is
; only used in commentary about the forcing.  The :target of a forced rewerite
; rule is generally the term to which the rule was applied, but here we're
; talking about function symbols that must (probably) be apply$'d during the
; rewriting of :target.
                           (cond
                            (erp

; A warrant is assumed false, the apply$ rule for a fn is disabled, or forcing
; is not allowed.

                             (prog2$
                              (rewrite-lambda-object-post-warning
                               evg rewritten-body nil ttree1 wrld)
                              (mv step-limit
                                  evg
                                  ttree)))
                            (t (mv step-limit
                                   `(lambda ,formals ,rewritten-body1)
                                   (cons-tag-trees ttree2 ttree)))))))))))))
               (t (prog2$
                   (rewrite-lambda-object-pre-warning
                    evg nil progs pre-have-no-warrants wrld)
                   (mv step-limit evg ttree)))))))
         (t (prog2$
             (rewrite-lambda-object-pre-warning evg t nil nil wrld)
             (mv step-limit evg ttree))))))
)
