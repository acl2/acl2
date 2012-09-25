; ACL2 Version 5.0 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2012  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of Version 2 of the GNU General Public License as
; published by the Free Software Foundation.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

(in-package "ACL2")

; We start our development of the rewriter by coding one-way-unify and the
; substitution fns.

; Essay on Equivalence, Refinements, and Congruence-based Rewriting

; (Note: At the moment, the fact that fn is an equivalence relation is
; encoded merely by existence of a non-nil 'coarsenings property.  No
; :equivalence rune explaining why fn is an equivalence relation is to
; be found there -- though such a rune does exist and is indeed found
; among the 'congruences of fn itself.  We do not track the use of
; equivalence relations, we just use them anonymously.  It would be
; good to track them and report them.  When we do that, read the Note
; on Tracking Equivalence Runes in subst-type-alist1.)

; (Note: Some of the parenthetical remarks in this code are extremely
; trite observations -- to the ACL2 afficionado -- added when I sent
; this commented code off to friends to read.)

; We will allow the user to introduce new equivalence relations.
; At the moment, they must be functions of two arguments only.
; Parameterized equivlence relations, e.g., x == y (mod n), are
; interesting and may eventually be implemented.  But in the spirit of
; getting something done right and working, we start simple.

; An equivalence relation here is any two argument function that has
; been proved to be Boolean, symmetric, reflexive, and transitive.
; The rule-class :EQUIVALENCE indicates that a given theorem
; establishes that equiv is an equivalence relation.  (In the
; tradition of Nqthm, the ACL2 user tells the system how to use a
; theorem when the theorem is submitted by the user.  These instructions
; are called "rule classes".  A typical "event" might therefore be:
; (defthm set-equal-is-an-equivalence-rel
;   (and (booleanp (set-equal x y))
;        (set-equal x x)
;        (implies (set-equal x y) (set-equal y x))
;        (implies (and (set-equal x y)
;                      (set-equal y z))
;                 (set-equal x z)))
;   :rule-classes :EQUIVALENCE)
; The rule class :EQUIVALENCE just alerts the system that this
; formula states that something is an equivalence relation.  If
; the formula is proved, the system identifies set-equal as the
; relation and adds to the data base certain information that
; enables the processing described here.)

; The Boolean requirement is imposed for coding convenience.  In
; assume-true-false, for example, when we assume (equiv x y) true, we
; simply give it the type-set *ts-t*, rather than something
; complicated like its full type-set take away *ts-nil*.  In addition,
; the Boolean requirement means that (equiv x y) is equal to (equiv y
; x) (not just propositionally) and hence we can commute it at will.
; The other three requirements are the classic ones for an equivalence
; relation.  All three are exploited.  Symmetry is used to justify
; commutativity, which currently shows up in assume-true-false when we
; put either (equiv x y) or (equiv y x) on the type-alist -- depending
; on term-order -- and rely on it to assign the value of either.
; Reflexivity is used to eliminate (equiv x term) as a hypothesis when
; x does not occur in term or elsewhere in the clause.  Transitivity
; is used throughout the rewriting process.  These are not guaranteed
; to be all the places these properties are used!

; Note:  Some thought has been given to the idea of generalizing our
; work to non-symmetric reflexive and transitive relations.  We have
; seen occasional utility for the idea of rewriting with such a monotonic
; relation, replacing a term by a stronger or more defined one.  But to
; implement that we feel it should be done in a completely independent
; second pass in which monotonic relations are considered.  Equivalence
; relations are of such importance that we did not want to risk doing them
; weakly just to allow this esoteric variant.

; Note: We explicitly check that an equivalence relation has no guard
; because we never otherwise consider their guards.  (The
; "guard" on an ACL2 function definition is a predicate that must be
; true of the actuals in order for the defining equation to hold.  It
; can be thought of as a "precondition" or a characterization of the
; domain of the function definition.  In Common Lisp (and ACL2 is just
; a subset of Common Lisp) many functions, e.g., car and cdr, are not
; defined everywhere and guards are our way of taking note of this.
; Equivalence relations have "no" guard, meaning their guard is t,
; i.e., they are defined everywhere.)

; The motivation behind equivalence relations is to allow their use
; as :REWRITE rules.  For example, after set-equal has been proved to be
; an equivalence relation and union-eq, say, has been proved to be
; commutative (wrt set-equal),

; (implies (and (symbol-listp a)
;               (true-listp a)
;               (symbol-listp b)
;               (true-listp b))
;          (set-equal (union-eq a b) (union-eq b a)))

; then we would like to be able to use the above rule as a rewrite
; rule to commute union-eq expressions.  Of course, this is only
; allowed in situations in which it is sufficient to maintain
; set-equality as we rewrite.  Implicit in this remark is the idea
; that the rewriter is given an equivalence relation to maintain as it
; rewrites.  This is a generalization of id/iff flag in Nqthm's
; rewriter; that flag indicates whether the rewriter is maintaining
; identity or propositional equivalence.  :CONGRUENCE lemmas,
; discussed later, inform the rewriter of the appropriate relations to
; maintain as it steps from (fn a1 ... an) to the ai.  But given a
; relation to maintain and a term to rewrite, the rewriter looks at
; all the :REWRITE rules available and applies those that maintain the
; given relation.

; For example, suppose the rewriter is working on (memb x (union-eq b
; a)), where memb is a function that returns t or nil according to
; whether its first argument is an element of its second.  Suppose the
; rewriter is to maintain identity during this rewrite, i.e., it is to
; maintain the equivalence relation equal.  Suppose a :CONGRUENCE rule
; informs us that equal can be preserved on memb expressions by
; maintaining set-equal on the second argument.  Then when rewriting
; the second argument to the memb, rewrite shifts from maintaining
; equal to maintaining set-equal.  This enables it to use the above
; theorem as a rewrite rule, replacing (union-eq b a) by (union-eq a
; b), just as Nqthm would had the connecting relation been equal
; instead of set-equal.

; This raises the problem of refinements.  For example, we may have
; some rules about union-eq that are expressed with equal rather than
; set-equal.  For example, the definition of union-eq is an equality!
; It is clear that a rule may be tried if its connecting equivalence
; relation is a refinement of the one we wish to maintain.  By
; ``equiv1 is a refinement of equiv2'' we mean

; (implies (equiv1 x y) (equiv2 x y)).

; Such rules are called :REFINEMENT rules and are a distinguished
; rule-class, named :REFINEMENT.  Every equivalence relation is a
; refinement of itself.  Equal is a refinement of every equivalence
; relation and no other relation is a refinement of equal.

; Every equivalence relation, fn, has a non-nil value for the property
; 'coarsenings.  The value of the property is a list of all
; equivalence relations (including fn itself) known to admit fn as a
; refinement.  This list is always closed under the transitivity of
; refinement.  That is, if e1 is a refinement of e2 and e2 is a
; refinement of e3, then the 'coarsenings for e1 includes e1 (itself),
; e2 (of course), and e3 (surprise!).  This makes it easier to answer
; quickly the question of who is a refinement of whom.

; Equivalence relations are the only symbols with non-nil 'coarsenings
; properties, thus this is the way they are recognized.  Furthermore,
; the 'coarsenings property of 'equal will always list all known
; equivalence relations.

; When we are rewriting to maintain equiv we use any rule that is a known
; refinement of equiv.  Thus, while rewriting to maintain set-equal we can
; use both set-equal rules and equal rules.

; Now we move on to the heart of the matter: knowing what relation to maintain
; at each step.  This is where :CONGRUENCE rules come in.

; The key idea in congruence-based rewriting is that lemmas of the form:
; (implies (equiv1 x y)
;          (equiv2 (fn a1 ... x ... an)
;                  (fn a1 ... y ... an))),

; where equiv1 and equiv2 are equivalence relations, the ai, x, and y
; are distinct variables and x and y occur in the kth argument
; position of the n-ary function fn, can be used to rewrite
; fn-expressions, maintaining equiv2, by rewriting the kth argument
; position maintaining equiv1.

; We call such a lemma a ``congruence lemma'' and say that it
; establishes that ``equiv2 is maintained by equiv1 in the kth
; argument of fn.''  The rule-class :CONGRUENCE indicates when a lemma
; is to be so used.  

; An example :CONGRUENCE lemma is

; (implies (set-equal a b) (iff (member x a) (member x b))).

; (In my previous example I used memb.  Here I use member, the Common
; Lisp function.  When member succeeds, it returns the tail of its
; second arg that starts with its first.  Thus, (member x a) is not
; necessary equal to (member x b), even when a and b are set-equal.
; But they are propositionally equivalent, i.e., mutually nil or
; non-nil.  Iff is just another equivalence relation.)

; That is, iff is maintained by set-equal in the second argument of
; member.  Thus, when rewriting a member expression while trying to
; maintain iff it is sufficient merely to maintain set-equivalence on
; the second argument of member.  In general we will sweep across the
; arguments of a function maintaining an appropriate equivalence
; relation for each argument as a function of the relation we wish to
; maintain outside.

; A literal interpretation of the lemma above suggests that one
; must maintain identity on the first argument of member in order to
; rely on the lemma in the second argument.  What then justifies our
; independent use of :CONGRUENCE lemmas in distict argument positions?

; Congruence Theorem 1.  :CONGRUENCE lemmas for different argument
; positions of the same function can be used independently.  In
; particular, suppose equiv is maintained by e1 in the kth argument of
; fn and equiv is maintained by e2 in the jth argument of fn, where j
; is not k.  Suppose a is e1 to a' and b is e2 to b'.  Then (fn
; ...a...b...) is equiv to (fn ...a'...b'...), where a and b occur in
; the kth and jth arguments, respectively.

; Proof.  By the :CONGRUENCE lemma for equiv and e1 we know that
; (fn ...a...b...) is equiv (fn ...a'...b...).  By the :CONGRUENCE 
; lemma for equiv and e2 we know that (fn ...a'...b...) is equiv to
; (fn ...a'...b'...).  The desired result is then obtained via the
; transitivity of equiv.  Q.E.D.

; While we require the user to formulate :CONGRUENCE lemmas as shown
; above we actually store them in a data structure, called the
; 'congruences property of fn, in which lemmas for different slots
; have been combined.  Indeed, we ``generalize'' still further and
; allow for more than one way to rewrite a given argument position.  If fn
; has arity n, then the 'congruences property of fn is a list of tuples,
; each of which is of the form (equiv slot1 slot2 ... slotn), where equiv
; is some equivalence relation and each slotk summarizes our knowledge
; of what is allowed in each argument slot of fn while maintaining
; equiv.  The entire n+1 tuple is assembled from many different
; :CONGRUENCE lemmas.  Indeed, it is modified each time a new
; :CONGRUENCE lemma is proved about fn and equiv.  Without discussing
; yet the structure of slotk, such a tuple means:

; (implies (and (or (equiv1.1 x1 y1)
;                   ...
;                   (equiv1.i x1 y1))
;               ...
;               (or (equivn.1 xn yn)
;                   ...
;                   (equivn.j xn yn)))
;          (equiv (fn x1 ... xn)
;                 (fn y1 ... yn))).

; Thus, to rewrite (fn x1 ... xn) maintaining equiv we sweep across
; the arguments rewriting each in turn, maintaining any one of the
; corresponding equivk,l's, which are encoded in the structure of
; slotk.

; Note that each equivk,l above is attributable to one and only one
; :CONGRUENCE lemma.  Since the ors cause searching, we allow the user
; to control the search by disabling :CONGRUENCE lemmas.  We only
; pursue paths introduced by enabled lemmas.

; The structure of slotk is a list of ``congruence-rules'', which are
; instances of the record

(defrec congruence-rule (nume equiv . rune) t)

; The :equiv field is the function symbol of an equivalence relation
; which, if maintained in argument k, is sufficient to maintain equiv
; for the fn-expression, :rune (it stands for "rule name") is the name
; of the :CONGRUENCE lemma that established this link between equiv,
; :equiv, fn, and k, and :nume is the nume of the rune (a "nume" is a
; unique natural number corresponding to a rune, used only to speed up
; the answer to the question: "is the named rule enabled -- i.e.,
; among those the user permits us to apply automatically?")  allowing
; us to query the enabled structure directly.

; Because we allow more than one :CONGRUENCE rule per argument, we
; have a problem.  If we are trying to maintain equiv for fn and are
; rewriting an argument whose slot contains (equivk.1 ... equivk.l),
; what equivalence relation do we try to maintain while rewriting the
; argument?  We could iteratively try them each, rewriting the
; argument l times.  This suffers because some rules would be tried
; many times due to our use of refinements.  For example, all of the
; equality rules would be tried for each equivk.i tried.

; It is desirable to eliminate the need for more than one pass through
; rewrite.  We would like to rewrite once.  But if we pass the whole
; set in, with the understanding that any refinement of any of them
; can be used, we are not assured that the result of rewrite is
; equivalent in any of those senses to the input.  The reason is that
; rewrite may recursively rewrite its intermediate answer.  (If our
; rewriter simplifies a to a' it may then rewrite a' to a''.)  Thus, a
; may rewrite to a' maintaining equivk.1 and then a' may rewrite to
; a'' maintaining equivk.2 and it may be that a is not equivalent to
; a'' in either the equivk.1 or equivk.2 sense.  However, note that
; there exists an equivalence relation of which equivk.1 and equivk.2
; are refinements, and that is the relation being maintained.  Call
; that the ``generated relation.''  Numerous questions arise.  Is the
; generated relation definable in the logic, for if so, perhaps we
; could allow only one equivalence relation per slot per fn and equiv
; and force the user to invent the necessary generalization of the
; several relations he wants to use.  Furthermore, if both equivk.1
; and equivk.2 maintain equiv in the kth slot of fn, does their
; generated relation maintain it?  We need to know that the answer is
; ``yes'' if we are going to replace a by a'' (which are equivalent
; only in the generated sense) and still maintain the goal relation.

; We have taken the tack of allowing more than one :CONGRUENCE rule per
; slot by automatically (indeed, implicitly) dealing with the generated
; equivalence relations.  To justify our code, we need a variety of
; theorems about generated relations.  We state and prove those now.

; Let e1 and e2 be two binary relations.  We define the relation s
; ``generated by e1 and e2,'' denoted {e1 e2}, as follows.  Because
; order is unimportant below, our set notation {e1 e2} is acceptable.

; (s x y) iff there exists a finite sequence x1, x2, ..., xn such that
; x = x1, y = xn, and for all i, ((e1 xi xi+1) or (e2 xi xi+1)).  We
; read this as saying ``(s x y) iff there is a chain connecting x to y
; composed entirely of e1 and/or e2 links.''

; Congruence Theorem 2. If e1 and e2 are equivalence relations, so is
; {e1 e2}.

; Proof.  Let s be {e1 e2}.  Then s is reflexive, symmetric, and
; transitive, as shown below.

; Reflexive.  To show that (s x x) holds we must exhibit a sequence
; linking x to x via e1 and/or e2.  The sequence x,x suffices.

; Symmetric.  If (s x y) holds, then there exists a sequence linking x
; to y via e1 and/or e2 steps.  Let that sequence be x, x2, ..., xk,
; y.  By definition, either e1 or e2 links each pair.  Since e1 is
; symmetric, if a pair, xi, xj, is linked by e1 then the pair xj, xi
; is also linked by e1.  Similarly for e2.  Thus, the sequence
; obtained by reversing that above, y, xk, ..., x2, x, has the desired
; property: each pair is linked by e1 or e2.  Therefore, (s y x).

; Transitive.  If (s x y) holds, then there exists a sequence linking x
; to y, say x, x2, ..., xk, y.  If (s y z) holds, there exists a
; sequence linking y to z, say, y, y1, ..., yk, z.  Consider the
; concatenation of those two sequences, x, x2, ..., xk, y, y, y1, ...,
; yk, z.  It links x and z and every pair is linked by either e1 or
; e2.  Thus, (s x z).

; Q.E.D.

; Thus, the relation generated by two equivalence relations is an
; equivalence relation.

; Congruence Theorem 3. If e1 and e2 are equivalence relations, they
; are both refinements of {e1 e2}.

; Proof.  Let s be {e1 e2}.  We wish to prove
; (implies (e1 x y) (s x y)) and (implies (e2 x y) (s x y)).
; We consider the first goal only.  The second is symmetric.
; But clearly, if x is linked to y by e1 then (s x y) holds,
; as witnessed by the sequence x,y.  Q.E.D.

; Congruence Theorem 4.  Let equiv, e1 and e2 be equivalence
; relations.  Suppose equiv is preserved by e1 in the kth argument of
; fn.  Suppose equiv is also preserved by e2 in the kth argument of
; fn.  Then equiv is preserved by {e1 e2} in the kth argument of fn.

; Proof.  Let s be {e1 e2}.  Without loss of generality we restrict our
; attention to a function, fn, of one argument.  We have

; (implies (e1 x y) (equiv (fn x) (fn y)))
; and
; (implies (e2 x y) (equiv (fn x) (fn y)))

; We wish to prove
; (implies (s x y) (equiv (fn x) (fn y)))

; The hypothesis (s x y) establishes that there is a chain linking
; x to y via e1 and/or e2.  Let that chain be x, x2, ..., xk, y.
; Since each adjacent pair is linked via e1 or e2, and both preserve
; equiv, we get that (equiv (fn x) (fn x2)), (equiv (fn x2) (fn x3)),
; ... (equiv (fn xk) (fn y)).  By the transitivity of equiv, therefore,
; (equiv (fn x) (fn y)).  Q.E.D.

; Lemma.  If e1 is preserved by e in the kth argument of fn then
; so is {e1 e2}, for any relation e2.

; Proof.  We have that (e a b) implies (e1 (f ...a...) (f ...b...)).
; Let s be {e1 e2}.  We wish to prove that (e a b) implies 
; (s (f ...a...) (f ...b...)).  But by Congruence Theorem 3 above,
; e1 is a refinement of s.  Hence, (e1 (f ...a...) (f ...b...))
; implies (s (f ...a...) (f ...b...)).  Q.E.D.

; Congruence Theorem 5.  Let e1, ..., e4 be equivalence relations.
; Then if e2 is preserved by e1 in the kth argument of fn and e4 is
; preserved by e3 in the kth argument of fn, then {e2 e4} is preserved
; by {e1 e3} in the kth argument of fn.

; Proof.  By the above lemma, we know {e2 e4} is preserved by e1 in
; the kth argument of fn.  Similarly, {e2 e4} is preserved by e3 in
; the kth argument of fn.  Thus, the hypotheses of Theorem 4 are
; satisfied and we have that {e2 e4} is preserved by {e1 e3} in the
; kth argument of fn.  Q.E.D.

; We generalize the notion of the relation generated by two relations
; to that generated by n relations, {e1, e2, ..., en}.  By the above
; results, {e1, ..., en} is an equivalence relation if each ei is,
; each ei is a refinement of it, and it supports any congruence that
; all ei support.  We adopt the convention that the relation generated
; by {} is EQUAL and the relation denoted by {e1} is e1.

; In our code, generated equivalence relations are represented by
; lists of congruence-rules.  Thus, if cr1 and cr2 are two
; instances of the congruence-rule record having :equivs e1 and e2
; respectively, then {e1 e2} can be represented by '(cr1 cr2).

; The equivalence relation to be maintained by rewrite is always
; represented as a generated equivalence relation.  In our code we
; follow the convention of always using a variant of the name
; ``geneqv'' for such an equivalence relation.  When a variable
; contains (or is expected to contain) the name of an equivalence
; relation rather than a :CONGRUENCE rule or geneqv, we use a variant
; of the name ``equiv'' or even ``fn''.

; The geneqv denoting EQUAL is nil.  The geneqv denoting IFF is:

(defconst *geneqv-iff*
  (list (make congruence-rule
              :rune *fake-rune-for-anonymous-enabled-rule*
              :nume nil
              :equiv 'iff)))

; This completes our general essay on the subject.  The theorems
; proved above are mentioned by name elsewhere in our code.  In
; addition, various details are discussed elsewhere.  For a simple
; example of how all of this works together, see the function
; subst-equiv-expr which implements substitution of new for old in
; term to produce term', where it is given tha new is equiv1 old and
; term is to be equiv2 term'.

; We now turn to the most primitive functions for manipulating
; equivalences and generated equivalences.  We deal with refinements
; first and then with the question of congruences.

(defun refinementp (equiv1 equiv2 wrld)

; Note: Keep this function in sync with refinementp below.

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
; The data base must be kept so that the transitive property of
; refinement is manifested explicitly.  This function is called very
; often and we do not want to go searching through the transitive
; closure of refinementhood or coarseninghood.  So if e1 is a known
; refinement of e2 and e2 is a known refinement of e3, then the
; 'coarsenings property of e1 must include not just e2 but also e3.
; We know the first element in the 'coarsenings of equiv1 is equiv1
; -- which isn't equiv2 -- so we skip it.

         (member-eq equiv2
                    (cdr (getprop equiv1 'coarsenings nil
                                  'current-acl2-world wrld))))))

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
; form new geneqvs from those in the data base.  In any case, this
; function does not get the enabled structure and takes no note of the
; status of any rule.

  (cond ((eq equiv 'equal) *fake-rune-for-anonymous-enabled-rule*)
        ((null geneqv) nil)
        (t (geneqv-refinementp1 (getprop equiv 'coarsenings nil
                                         'current-acl2-world wrld)
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
                  (cdr (getprop (access congruence-rule (car geneqv) :equiv)
                                'coarsenings nil 'current-acl2-world wrld)))
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
          (car new-cr-coarsenings)            ; new-equiv
          (cdr new-cr-coarsenings)            ; new-equiv's non-id coarsenings
          (cadr (car (car old-crs-and-coarsenings))))) ; first old-equiv

; The new equiv is a refinement of the first old one.  Nothing to do.

    old-crs-and-coarsenings)
   ((refinementp1
     (cadr (car (car old-crs-and-coarsenings)))     ; first old-equiv
     (cdr (car old-crs-and-coarsenings))            ; first old-equiv's 
                                                    ; non-id coarsenings
     (car new-cr-coarsenings))                      ; new-equiv

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
; of the form (congurence-rule . coarsenings), where the coarsenings
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
                                                (getprop
                                                 (access congruence-rule
                                                         (car geneqv1)
                                                         :equiv)
                                                 'coarsenings nil
                                                 'current-acl2-world wrld)
                                                old-crs-and-coarsenings
                                                t)
                     wrld))))

(defun union-geneqv (geneqv1 geneqv2 wrld)

; We union together the congruence rules in the two geneqv's, forming
; a set with the property that no element in it is a refinement of any
; other.  Roughly speaking we simply add the equivs of geneqv1 into
; those of geneqv2, not adding any that is a refinement and deleting
; any that is refined by a new one.  To make this process faster we
; first annotate genquv2 by pairing each congruence rule in it with
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
; generated equivlence relation for the fn-expression itself.  Because
; we form new geneqvs from stored ones in the data base, we have to
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
;   ; (setq genquv-cnt (1+ genquv-cnt))
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
        (t (let ((congruences (getprop fn 'congruences nil
                                       'current-acl2-world wrld)))
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
; are trying to maintain is a generated equivalencd, i.e., a set of
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

(defun scons-term (fn args ens wrld state ttree)

; This function is (cons-term fn args) except that we evaluate any enabled
; fn on quoted arguments and may do any other replacements that preserve
; equality (e.g., (equal x x) = t).  In addition, we report the executable
; counterparts we use by adding them to ttree.  We return (mv hitp term
; ttree'), hitp is t iff term is something different than (fn . args), term is
; equal to (fn .  args) and ttree' is an extension of ttree.

  (cond
   ((and (all-quoteps args)
         (or (flambdap fn)
             (and (enabled-xfnp fn ens wrld)

; We don't mind disallowing constrained functions that have attachments,
; because the call of ev-fncall below disallows the use of attachments (last
; parameter, aok, is nil).

                  (not (getprop fn 'constrainedp nil
                                'current-acl2-world wrld)))))

; Note: This code is supposed to be the same as in rewrite.  Keep them in sync
; and see the comment there for explanations.

    (cond ((flambdap fn)

; This is a problematic case.  At first sight, we could just create the term
; (fn . args) and then evaluate it with ev.  (We can't use ev-fncall as we do
; below because it doesn't handle lambdas.)  But this ignores some problems.
; How do we avoid evaluating :program fns that occur in the body?  How do
; we avoid evaluating disabled fns in the body?  How do we report the
; executable counterparts we use?  Problems, problems.  We punt.

           (mv nil (cons-term fn args) ttree))
          ((eq fn 'if)
           (mv t
               (if (cadr (car args))
                   (cadr args)
                   (caddr args))
               ttree))
          ((programp fn wrld) ; this test is needed; see the comment in rewrite
           (mv t (cons-term fn args) ttree))
          (t
           (mv-let
            (erp val latches)
            (pstk
             (ev-fncall fn (strip-cadrs args) state nil t nil))
            (declare (ignore latches))
            (cond
             (erp

; There is a guard violation, probably -- or perhaps there's some other kind of
; error.  We'll just hide this term so we don't see it again.

              (mv t (fcons-term* 'hide (cons-term fn args)) ttree))
             (t (mv t
                    (kwote val)
                    (push-lemma (fn-rune-nume fn nil t wrld)
                                ttree))))))))
   ((and (eq fn 'equal)
         (equal (car args) (cadr args)))
    (mv t *t* ttree))
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
; executable counterparts used are reported in the ttree.

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

; Next we develop clausify, the function that reduces a term to a set
; of clauses.

(mutual-recursion

(defun ffnnamesp (fns term)

; We determine whether some function fn (possibly a lambda-expression)
; in fns is used as a function in term.  So this function is:
; (exists fn in fns s.t. (ffnamep fn term)).

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

(defun complementaryp (lit1 lit2)
  (declare (xargs :guard (and (pseudo-termp lit1)
                              (pseudo-termp lit2))))

; Suppose lit1 and lit2 are terms and neither is of the form (NOT (NOT &)).
; Then we determine whether one is the complement of the other, i.e., one
; is (NOT lit) where lit is the other.  Note that we do not use any
; commuativity knowledge.  Thus, 

; WARNING:  (EQUAL A B) and (NOT (EQUAL B A)) are *not* complementaryp, by
; this definition!

  (or (and (nvariablep lit1)
           (not (fquotep lit1))
           (eq (ffn-symb lit1) 'not)
           (equal (fargn lit1 1) lit2))
      (and (nvariablep lit2)
           (not (fquotep lit2))
           (eq (ffn-symb lit2) 'not)
           (equal (fargn lit2 1) lit1))))

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
        ((and (nvariablep (car cl))
              (not (fquotep (car cl)))
              (eq (ffn-symb (car cl)) 'not)
              (comm-equal fn lhs rhs (fargn (car cl) 1)))
         cl)
        (t (member-complement-term2 fn lhs rhs (cdr cl)))))

(defun member-complement-term1 (lit cl)

; Lit is known not to begin with not and not to be an equality or iff.
; This fn is equivalent to (member-equal `(not ,lit) cl).

  (cond ((null cl) nil)
        ((and (nvariablep (car cl))
              (not (fquotep (car cl)))
              (eq (ffn-symb (car cl)) 'not)
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
        ((eq (ffn-symb lit) 'not)
         (member-term (fargn lit 1) cl))
        (t (member-complement-term1 lit cl))))

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
; (go . n)           transfer control to the instruction labelled n
; (test . n)         pop and test the top of the stack and if nil,
;                    transfer control to the instruction labelled n,
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
        ((and (not (variablep (car assumptions)))
              (eq (ffn-symb (car assumptions)) 'INTEGERP)
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
               ((and (not (variablep (cadr assumptions)))
                     (eq (ffn-symb (cadr assumptions)) 'RATIONALP)
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

           (cond ((and (nvariablep test)
                       (eq (ffn-symb test) 'equal)
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
           (cond ((and (nvariablep test)
                       (eq (ffn-symb test) 'equal)
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

; N is a natural number.  If cons-term/alist is of the form
; (cons v0 ... (cons vn ...)), we return (mv vn alist'), where alist' is the
; alist under which to interpret vi.  Cons-term may, of course, be
; a variable or may contain variables, bound in alist.  We return
; (mv nil nil) if we do not like what we see.

  (cond ((variablep cons-term)
         (let ((temp (assoc-eq cons-term alist)))
           (cond (temp (simplifiable-mv-nth1 n (cdr temp) nil))
                 (t (mv nil nil)))))
        ((fquotep cons-term)

; If the guts of this quote is a true-list of sufficient length, we
; return the correct answer.  Otherwise, we indicate that we cannot
; determine the value.  We could, always, determine the value in this
; case, but we are lazy and there seems little point.

         (cond ((and (true-listp (cadr cons-term))
                     (> (length (cadr cons-term)) n))
                (mv (kwote (nth n (cadr cons-term))) nil))
               (t (mv nil nil))))
        ((eq (ffn-symb cons-term) 'cons)
         (if (= n 0)
             (mv (fargn cons-term 1) alist)
           (simplifiable-mv-nth1 (1- n) (fargn cons-term 2) alist)))
        (t (mv nil nil))))

(defun simplifiable-mv-nth (term alist)

; Term/alist must be a term of the form (mv-nth & &), i.e., the
; ffn-symb of term is known to be 'mv-nth.  We determine whether we
; can simplify this and is so return (mv term' alist') as the
; simplification.  If we cannot, we return (mv nil nil).  We look for
; (mv-nth 'i (cons v1 ... (cons vi ...))), but we allow the two
; arguments of term to be variable symbols that are looked up.  That
; is, we allow (MV-NTH I V) where I is bound in alist to a quoted
; constant and V is bound to a CONS term.

  (let ((arg1 (cond ((variablep (fargn term 1))
                     (let ((temp (assoc-eq (fargn term 1) alist)))
                       (cond (temp (cdr temp))
                             (t (fargn term 1)))))
                    (t (fargn term 1)))))
    (cond ((and (quotep arg1)
                (integerp (cadr arg1))
                (>= (cadr arg1) 0))
           (mv-let (term1 alist1)
                   (simplifiable-mv-nth1 (cadr arg1) (fargn term 2) alist)
                   (cond
                    (term1
                     (mv term1 alist1))
                    (t (mv nil nil)))))
          (t (mv nil nil)))))

(defun simplifiable-mv-nthp (term alist)

; Here is a predicate version of the above.  

  (mv-let (term alist)
          (simplifiable-mv-nth term alist)
          (declare (ignore alist))
          (if term t nil)))

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
                        (nvariablep (cadr ac))
;                       (not (fquotep (cadr ac)))
                        (eq (ffn-symb (cadr ac)) 'equal))

; Note:  (equal t (equal a b)) = (equal a b).

                   (cadr ac))
                  ((and (equal (cadr ac) *t*)
                        (nvariablep (car ac))
                        (eq (ffn-symb (car ac)) 'equal))
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
                   (if (simplifiable-mv-nthp term nil)

; Alist1 below must be nil since we used nil above.

                       (mv-let (term1 alist1)
                               (simplifiable-mv-nth term nil)
                               (declare (ignore alist1))
                               term1)
                     term)))
                (t (cons-term fn ac)))
               stack))
        (t (call-stack fn (cdr lst) (cdr stack)
                       assumptions
                       (cons (car stack) ac)))))

(defun ret-stack (lst stack)
  (cond ((null lst) stack)
        (t (ret-stack (cdr lst) (cdr stack)))))

(defun extra-info-lit-p (lit)
  (and (nvariablep lit)
;      (not (fquotep lit))
       (eq (ffn-symb lit) 'not)
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
; boringly repetitive and "slow."  A fairly decent guitar solo at 2:02 doesn`t
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

(defun if-interp-add-clause (assumptions cl ac pflg)

; This is how we add a new clause to if-interp's accumulator, ac.  The clause
; we add is the one recovered from the current assumptions, starting with the
; clause cl.  If pflg is t then the caller is not interested in the set of
; clauses but just whether the set is empty or not.  In that case, we return t
; if the set of clauses is non-empty and nil if it is empty.

  (cond
   (pflg t)
   (t (let* ((cl1 (convert-assumptions-to-clause-segment assumptions cl nil))
             (ans (quick-and-dirty-subsumption-replacement-step cl1 ac)))
        (cond ((eq ans 'subsumed1) ac)
              (t (cons cl1 ans)))))))

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
   ((and (nvariablep term)
         (not (fquotep term))
         (eq (ffn-symb term) 'if)
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
; On the otherhand, if x is true, then -x is false, so the
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

(defun find-subsumer-replacement (cl l)
  (declare (xargs :guard (and (pseudo-term-listp cl)
                              (pseudo-term-list-listp l))))

; We return (mv val cl0), where val is nil to indicate that no subsumer or
; replacer was found, or 'subsumed to indicate cl is subsumed by clause cl0 in
; l, or if neither of these cases applies, then a pair (indicating that the
; complement of the car of the pair may be removed from cl).  The last case
; means that somewhere in l we found a clause that when resolved with cl
; produces a resolvent that subsumes cl.

  (cond ((null l) (mv nil nil))
        (t (let ((here (arg1-almost-subsumes-arg2 (car l) cl)))
             (cond ((eq here 'subsumed) (mv here (car l)))
                   (t (mv-let (rst cl0)
                              (find-subsumer-replacement cl (cdr l))
                              (cond ((eq rst 'subsumed) (mv rst cl0))
                                    (t (mv (or here rst) nil))))))))))

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
                           (declare (ignore without-lst))
                           (equal (sweep-clauses (caddr x))
                                  with-lst))
                   (mv-let (with-lst without-lst)
                           (filter-with-and-without (cadr x)
                                                    (sweep-clauses (cadddr x))
                                                    nil nil)
                           (declare (ignore with-lst))
                           (equal (sweep-clauses (cadddr x))
                                  without-lst))))
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
    (cond (lits (replace-clause cl0 (revappend lits cl0) tree))
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
; many of its callers have great difficulty accomodating it.  For example, in
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
; (verify-guards exec-send ...) in
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

; This function is (mv term' ttree'), where term' is equivalent modulo
; geneqv (see the essay on Equivalence, Refinements and Congruence-
; based Rewriting) to term and ttree' includes ttree and may include
; additional stuff.  Depending on ts, the type-set of term (which is
; supported by the ts-ttree), we may coerce term to 0, t, or nil.

; Note: This function used to depend on the objective, obj, of the
; rewrite.  When obj was nil, that dependency prevented obj-table from
; reducing term to t when term was known to have non-nil type-set.
; That, in turn, caused relieve-hyp to force (not term), even though
; (not term) was known nil.  We now reduce term to t, nil or 0 as
; appropriate by the geneqv and ts, regardless of obj.  However, we have
; left the obj parameter in place, in case we someday want to restore
; dependency on it.

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
   ((and (nvariablep term)
         (eq (ffn-symb term) 'if))

; Is this case important?  It doesn't seem so, and we were tempted to delete it
; when we modified find-rewriting-equivalence after Version_3.0.1 to look for
; calls of (hide ('rewrite-equiv ..)).  But at one time, deletion caused
; failure of lemma lop3-34 in books/rtl/rel5/support/lop3-proofs.lisp, so we
; leave this case for backward compatibility.

    (mv term ttree))
   ((and (nvariablep term)
         (eq (ffn-symb term) 'hide)
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
; However, then Rich Cohen observed that if we are trying to relieve a hypothesis
; in a lemma and the hyp rewrites to an explicit cons expression we fail to
; recognize that it is non-nil!  Here is a thm that fails for that reason:
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
; 

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

(defun rewrite-if1
  (test left right type-alist geneqv ens ok-to-force wrld ttree)

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
                   (t (rewrite-if11 (mcons-term* 'if test left right)
                                    type-alist geneqv wrld ttree)))))
          (t (rewrite-if11 (mcons-term* 'if test left right)
                           type-alist geneqv wrld ttree))))
        (t (rewrite-if11 (mcons-term* 'if test left right)
                         type-alist geneqv wrld ttree))))

; Rockwell Addition: In the not-to-be-rewritten test below, we used to
; create an instantiation with sublis-var.  Now we chase var bindings.
; But there is a subtlety with constants created by sublis-var.

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

; The backchain-limit-lst must be nil, a natp, or a list of these of the same
; length as hyps.  For subclass 'meta, only the first two of these is legal.
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
  nil)

; There are four subclasses of rewrite rule, distinguished by the :subclass slot.
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
;   the metafunction symbol to be applied, and hyps is a function of one (term)
;   argument that generates a hypothesis for the metatheorem.

; Rockwell Addition: The recursivep property used to be the fn name if the
; fn in question was singly recursive.  Now it is a singleton list (fn).

; 'definition - a rule implementing a non-abbreviational definitional equation.
; In this case :heuristic-info is the pair (recursivep . controller-alist)
; where recursivep is nil (if this is a nonrec definition) or a truelist of
; symbols naming all the fns in the ``clique'' (singly recursive functions have
; a singleton list as their recursivep property); and controller-alist is an
; alist pairing each fn named in recursivep to a mask of t's and nil's in 1:1
; correspondence with the formals of the fn and indicating with t's which
; arguments control the recursion for this definition.

(defun relevant-ground-lemmas (hyp wrld)
  (mv-let (not-flg hyp)
          (strip-not hyp)
          (declare (ignore not-flg))
          (cond
           ((variablep hyp) nil)
           ((fquotep hyp) nil)
           ((flambda-applicationp hyp) nil)
           (t (getprop (ffn-symb hyp) 'lemmas nil 'current-acl2-world wrld)))))

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
                           (mv t
                               unify-subst
                               (push-lemma (geneqv-refinementp
                                            (access rewrite-rule (car lemmas) :equiv)
                                            *geneqv-iff*
                                            wrld)
                                           (push-lemma
                                            (access rewrite-rule (car lemmas) :rune)
                                            nilp-ttree))
                               (cdr lemmas)))
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
; *definition-minimal-theory*.  See the error related to
; *definition-minimal-theory* in chk-acceptable-definition-install-body.

(defun expand-some-non-rec-fns (fns term wrld)

; We forcibly expand all calls in term of the fns in fns.  They better
; all be non-recursive or this may take a while.

  (cond ((variablep term) term)
        ((fquotep term) term)
        (t (let ((args (expand-some-non-rec-fns-lst fns (fargs term) wrld)))
             (cond ((member-equal (ffn-symb term) fns)
                    (subcor-var (formals (ffn-symb term) wrld)
                                args
                                (body (ffn-symb term) t wrld)))
                   (t (cons-term (ffn-symb term) args)))))))

(defun expand-some-non-rec-fns-lst (fns lst wrld)
  (cond ((null lst) nil)
        (t (cons (expand-some-non-rec-fns fns (car lst) wrld)
                 (expand-some-non-rec-fns-lst fns (cdr lst) wrld)))))

)

(defun tautologyp (term wrld)

; If this function returns t, then term is a theorem.  With the intended
; application in mind, namely the recognition of "trivial corollaries" while
; processing rule classes, we check for the "most common" tautology, (implies p
; p).  Otherwise, we expand certain non-recursive fns and see if the result is
; an if-tautology.  This function can be made as fancy as you want, as long as
; it recognizes theorems.

  (cond ((and (nvariablep term)
              (not (fquotep term))
              (eq (ffn-symb term) 'implies)
              (equal (fargn term 1) (fargn term 2)))
         t)
        (t (if-tautologyp
            (expand-some-non-rec-fns

; The list of functions expanded is arbitrary, but they must all be
; non-recursively defined.  Guards are permitted but of course it is the
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

               zerop synp return-last plusp minusp listp mv-list wormhole-eval
               force case-split double-rewrite)
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

; The fnstack used by the rewriter is a list.  Each element is a
; function symbol, a list of function symbols, or of the form (:term
; . term) for some term, term.  The first case means we are expanding
; a definition of that symbol and the symbol is non-recursively
; defined.  The second means we are expanding a singly or mutually
; recursive function.  (In fact, the fnstack element is the recursivep
; flag of the function we're expanding.)  The third means that we are
; rewriting the indicated term (through the recursive dive in the
; rewriter that rewrites the just-rewritten term).  Lambda-expressions
; are not pushed onto the fnstack, though fn may be a
; lambda-expression.  We determine whether fn is on fnstack (including
; being a member of a mutually recursive clique).

  (cond ((null fnstack) nil)
        ((consp (car fnstack))
         (or (eq fn (caar fnstack)) ; and hence (not (eq (caar fnstack) :term))
             (being-openedp-rec fn (cdr fnstack))))
        (t (or (eq fn (car fnstack))
               (being-openedp-rec fn (cdr fnstack))))))

(defmacro being-openedp (fn fnstack clique)

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
          (being-openedp-rec (if clique
                                 (car clique)
                               ,fn)
                             ,fnstack))))

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
; Because it contains a rewriteable call we rewrite it again.  If we do so with
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

; where the OCCUR-CNT counted the number of times ARG occured in VAL.  The
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

; Lemma make-shared-variables-dag-as-term-l-lemma in
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
; too-many-ifs0 and too-many-ifs-pre-rewrite, but several books had conflicts
; with this definition of nat-listp, as follows:

; workshops/2004/ruiz-et-al/support/terms-as-dag.lisp
; workshops/2003/sumners/support/n2n.lisp
; workshops/2009/kaufmann-kornerup-reitblatt/support/preliminaries.lisp
; concurrent-programs/bakery/measures.lisp
; unicode/nat-listp.lisp
; defexec/dag-unification/terms-as-dag.lisp

; So we have commented out this definition.  If we decide to use it after all,
; change integer-listp to nat-listp in the two guards mentioned above and also
; in books/system/too-many-ifs.lisp, as indicated there.

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

(defun cons-count-bounded-ac (x i)

; We accumulate into i the number of conses in x, bounding our result by
; (fn-count-evg-max-val), which should not be less than i.  We choose
; (fn-count-evg-max-val) as our bound simply because that bound is used in the
; similar computation of fn-count-evg.

  (declare (type (signed-byte 30) i))
  (the (signed-byte 30)
    (cond ((atom x) i)
          (t (let ((i (cons-count-bounded-ac (cdr x) i)))
               (declare (type (signed-byte 30) i))
               (cond ((>= i (fn-count-evg-max-val))
                      (fn-count-evg-max-val))
                     (t
                      (cons-count-bounded-ac (car x) (1+f i)))))))))

(defun cons-count-bounded (x)
  (the (signed-byte 30)
    (cons-count-bounded-ac x 0)))

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
; books/arithmetic-3/bind-free/integerp-meta.lisp.  We have extracted the
; following from that failure: This succeeded when using (cons-count (cadr
; term)) in the case (fquotep term) below, but not when using 0 in that case
; instead.

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
; mutually recursive clique.  Controller-alist is an alistthat assigns
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

(defun contains-rewriteable-callp
  (fn term cliquep terms-to-be-ignored-by-rewrite)

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

         (contains-rewriteable-callp-lst fn (fargs term)
                                         cliquep
                                         terms-to-be-ignored-by-rewrite))
        ((and (if cliquep
                  (member-eq (ffn-symb term) cliquep)
                (eq (ffn-symb term) fn))
              (not (member-equal term terms-to-be-ignored-by-rewrite)))
         t)
        (t (contains-rewriteable-callp-lst fn (fargs term)
                                           cliquep
                                           terms-to-be-ignored-by-rewrite))))

(defun contains-rewriteable-callp-lst
  (fn lst cliquep terms-to-be-ignored-by-rewrite)
  (cond ((null lst) nil)
        (t (or (contains-rewriteable-callp fn (car lst)
                                           cliquep
                                           terms-to-be-ignored-by-rewrite)
               (contains-rewriteable-callp-lst
                fn (cdr lst)
                cliquep
                terms-to-be-ignored-by-rewrite)))))

)

(defun pairlis-x1 (x1 lst)

; Cons x1 onto the front of each element of lst.

  (cond ((null lst) nil)
        (t (cons (cons x1 (car lst))
                 (pairlis-x1 x1 (cdr lst))))))

(defun pairlis-x2 (lst x2)

; Make an alist pairing each element of lst with x2.

  (cond ((null lst) nil)
        (t (cons (cons (car lst) x2)
                 (pairlis-x2 (cdr lst) x2)))))

(defrec linear-lemma ((nume . hyps) max-term concl
                      backchain-limit-lst rune
                      .

; The match-free field should be :all or :once if there are free variables in
; the hypotheses, else nil.

                      match-free)
  nil)

; Finally the Rewriter

(defrec current-literal (not-flg . atm) t)

(defrec rewrite-constant

; WARNING: If you change the layout of the rewrite-constant in a way that
; affects the position of :current-clause -- e.g., add a field -- you MUST
; change the definition in axioms.lisp of the function |Access REWRITE-CONSTANT
; record field CURRENT-CLAUSE|.  If you don't, however, the build will fail
; loudly (via a redefinition error).

; WARNING: The name "rewrite-constant" is a misnomer because it is not
; really constant during rewriting.  The active-theory is frequently
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

; The fields marked with *'s are involved in the soundness of the result
; of rewriting.  The rest are of heuristic use only.

; The current-literal not-flg and atm are always used together so we bundle
; them so we can extract them both at once:

  ((active-theory . (backchain-limit-rw . rw-cache-state))
   current-enabled-structure
   (pt restrictions-alist . expand-lst)
   (force-info fns-to-be-ignored-by-rewrite . terms-to-be-ignored-by-rewrite)
   (top-clause . current-clause)
   .
   ((current-literal . oncep-override) . (nonlinearp . case-split-limitations)))
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
; which rewrite-clause is currently working.  It is used to avoid biting our
; tail (see below).  When we are adding a term to the pot-lst, we refuse to add
; the negation of the current literal.

; Nonlinearp -- A boolean indicating whether nonlinear arithmetic should be
; considered to be active.

; We always obtain our rewrite-constant by loading relevant information into
; the following empty constant.  Warning: The constant below is dangerously
; useless less the current-enabled-structure is set to an enabled-structure.

(defconst *default-rw-cache-state*
  :atom)

(defconst *empty-rewrite-constant*
  (make rewrite-constant
        :active-theory :standard
        :backchain-limit-rw nil
        :case-split-limitations nil
        :current-clause nil
        :current-enabled-structure nil
        :current-literal nil
        :expand-lst nil
        :fns-to-be-ignored-by-rewrite nil
        :force-info nil
        :nonlinearp nil
        :oncep-override :clear
        :pt nil
        :restrictions-alist nil
        :rw-cache-state *default-rw-cache-state*
        :terms-to-be-ignored-by-rewrite nil
        :top-clause nil))

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
          simplify-clause-pot-lst rcnst gstack ttree)
  t)

(defun ok-to-force (rcnst)

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

; Return true if in the present context, we are to cause an error if the
; step-limit is exceeded.  See defrec step-limit-record.

  (let ((rec (f-get-global 'step-limit-record state)))
    (cond (rec (access step-limit-record rec :strictp))
          (t nil))))

(defun initial-step-limit (wrld state)

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
                                      type-alist obj geneqv wrld state
                                      fnstack ancestors
                                      backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)
                                    '( ; &extra formals -- keyword versions
                                      :rdepth :step-limit
                                      :type-alist :obj :geneqv :wrld :state
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
                   '(rewrite rewrite-with-lemma add-terms-and-lemmas
                             non-linear-arithmetic))

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
; call is used.  So we manage the GCL case ourselves.

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

(deflabel free-variables
  :doc
  ":Doc-Section Rule-Classes

  free variables in rules~/

  As described elsewhere (~pl[rule-classes]), ACL2 rules are treated as
  implications for which there are zero or more hypotheses ~c[hj] to prove.  In
  particular, rules of class ~c[:]~ilc[rewrite] may look like this:
  ~bv[]
  (implies (and h1 ... hn)
           (fn lhs rhs))
  ~ev[]
  Variables of ~c[hi] are said to occur ~em[free] in the above ~c[:rewrite]
  rule if they do not occur in ~c[lhs] or in any ~c[hj] with ~c[j<i].  (To be
  precise, here we are only discussing those variables that are not in the
  scope of a ~ilc[let]/~ilc[let*]/~c[lambda] that binds them.)  We also refer
  to these as the ~em[free variables] of the rule.  ACL2 may issue a warning or
  error when there are free variables in a rule, as described below.
  (Variables of ~c[rhs] may be considered free if they do not occur in ~c[lhs]
  or in any ~c[hj].  But we do not consider those in this discussion.)

  In general, the ~em[free variables] of rules are those variables occurring in
  their hypotheses (not ~ilc[let]/~ilc[let*]/~c[lambda]-bound) that are not
  bound when the rule is applied.  For rules of class ~c[:]~ilc[linear] and
  ~c[:]~ilc[forward-chaining], variables are bound by a trigger term.
  (~l[rule-classes] for a discussion of the ~c[:trigger-terms] field).  For
  rules of class ~c[:]~ilc[type-prescription], variables are bound by the
  ~c[:typed-term] field.

  Let us discuss the method for relieving hypotheses of ~il[rewrite] rules with
  free variables.  Similar considerations apply to ~il[linear] and
  ~il[forward-chaining] rules, and ~il[type-prescription] rules.

  ~l[free-variables-examples] for more examples of how this all works,
  including illustration of how the user can exercise some control over it.  In
  particular, ~pl[free-variables-examples-rewrite] for an explanation of output
  from the ~il[break-rewrite] facility in the presence of rewriting failures
  involving free variables, as well as an example exploring ``binding
  hypotheses'' as described below.

  Note that the ~c[:match-free] mechanism discussed below does not apply to
  ~il[type-prescription] rules.  ~l[free-variables-type-prescription] for a
  discussion of how to control free-variable matchng for ~il[type-prescription]
  rules.~/

  We begin with an example.  Does the proof of the ~ilc[thm] below succeed?
  ~bv[]
  (defstub p2 (x y) t)

  (defaxiom p2-trans
    (implies (and (p2 x y)
                  (p2 y z))
             (equal (p2 x z) t))
    :rule-classes ((:rewrite :match-free :all)))

  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))
  ~ev[]
  Consider what happens when the proof of the ~c[thm] is attempted.  The ACL2
  rewriter attempts to apply rule ~c[p2-trans] to the conclusion, ~c[(p2 a d)].
  So, it binds variables ~c[x] and ~c[z] from the left-hand side of the
  conclusion of ~c[p2-trans] to terms ~c[a] and ~c[d], respectively, and then
  attempts to relieve the hypotheses of ~c[p2-trans].  The first hypothesis of
  ~c[p2-trans], ~c[(p2 x y)], is considered first.  Variable ~c[y] is free in
  that hypothesis, i.e., it has not yet been bound.  Since ~c[x] is bound to
  ~c[a], the rewriter looks through the context for a binding of ~c[y] such
  that ~c[(p2 a y)] is true, and it so happens that it first finds the term
  ~c[(p2 a b)], thus binding ~c[y] to ~c[b].  Now it goes on to the next
  hypothesis, ~c[(p2 y z)].  At this point ~c[y] and ~c[z] have already been
  bound to ~c[b] and ~c[d]; but ~c[(p2 b d)] cannot be proved.

  So, in order for the proof of the ~ilc[thm] to succeed, the rewriter needs to
  backtrack and look for another way to instantiate the first hypothesis of
  ~c[p2-trans].  Because ~c[:match-free :all] has been specified, backtracking
  does take place.  This time ~c[y] is bound to ~c[c], and the subsequent
  instantiated hypothesis becomes ~c[(p2 c d)], which is true.  The application
  of rule ~c[(p2-trans)] succeeds and the theorem is proved.

  If instead ~c[:match-free :all] had been replaced by ~c[:match-free :once] in
  rule ~c[p2-trans], then backtracking would not occur, and the proof of the
  ~ilc[thm] would fail.

  Next we describe in detail the steps used by the rewriter in dealing with
  free variables.

  ACL2 uses the following sequence of steps to relieve a hypothesis with free
  variables, except that steps (1) and (3) are skipped for
  ~c[:forward-chaining] rules and step (3) is skipped for
  ~c[:type-prescription] rules.  First, if the hypothesis is of the form
  ~c[(force hyp0)] or ~c[(case-split hyp0)], then replace it with ~c[hyp0].
  ~bq[]
  (1) Suppose the hypothesis has the form ~c[(equiv var term)] where ~c[var] is
  free and no variable of ~c[term] is free, and either ~c[equiv] is ~ilc[equal]
  or else ~c[equiv] is a known ~il[equivalence] relation and ~c[term] is a call
  of ~ilc[double-rewrite].  We call this a ``binding hypothesis.''  Then bind
  ~c[var] to the result of rewriting ~c[term] in the current context.

  (2) Look for a binding of the free variables of the hypothesis so that the
  corresponding instance of the hypothesis is known to be true in the current
  context.

  (3) Search all ~ilc[enable]d, hypothesis-free rewrite rules of the form
  ~c[(equiv lhs rhs)], where ~c[lhs] has no variables (other than those bound
  by ~ilc[let], ~ilc[let*], or ~c[lambda]), ~c[rhs] is known to be true in the
  current context, and ~c[equiv] is typically ~c[equal] but can be any
  equivalence relation appropriate for the current context (~pl[congruence]);
  then attempt to bind the free variables so that the instantiated hypothesis
  is ~c[lhs].~eq[]
  If all attempts fail and the original hypothesis is a call of ~ilc[force] or
  ~ilc[case-split], where forcing is enabled (~pl[force]) then the hypothesis
  is relieved, but in the split-off goals, all free variables are bound to
  unusual names that call attention to this odd situation.

  When a ~il[rewrite] or ~il[linear] rule has free variables in the hypotheses,
  the user generally needs to specify whether to consider only the first
  instance found in steps (2) and (3) above, or instead to consider them all.
  Below we discuss how to specify these two options as ``~c[:once]'' or
  ``~c[:all]'' (the default), respectively.

  Is it better to specify ~c[:once] or ~c[:all]?  We believe that ~c[:all] is
  generally the better choice because of its greater power, provided the user
  does not introduce a large number of rules with free variables, which has
  been known to slow down the prover due to combinatorial explosion in the
  search (Steps (2) and (3) above).

  Either way, it is good practice to put the ``more substantial'' hypotheses
  first, so that the most likely bindings of free variables will be found first
  (in the case of ~c[:all]) or found at all (in the case of ~c[:once]).  For
  example, a rewrite rule like
  ~bv[]
  (implies (and (p1 x y)
                (p2 x y))
           (equal (bar x) (bar-prime x)))
  ~ev[]
  may never succeed if ~c[p1] is nonrecursive and enabled, since we may well
  not find calls of ~c[p1] in the current context.  If however ~c[p2] is
  disabled or recursive, then the above rule may apply if the two hypotheses
  are switched.  For in that case, we can hope for a match of ~c[(p2 x y)] in
  the current context that therefore binds ~c[x] and ~c[y]; then the rewriter's
  full power may be brought to bear to prove ~c[(p1 x y)] for that ~c[x] and
  ~c[y].

  Moreover, the ordering of hypotheses can affect the efficiency of the
  rewriter.  For example, the rule
  ~bv[]
  (implies (and (rationalp y)
                (foo x y))
           (equal (bar x) (bar-prime x)))
  ~ev[]
  may well be sub-optimal.  Presumably the intention is to rewrite ~c[(bar x)]
  to ~c[(bar-prime x)] in a context where ~c[(foo x y)] is explicitly known to
  be true for some rational number ~c[y].  But ~c[y] will be bound first to the
  first term found in the current context that is known to represent a rational
  number.  If the 100th such ~c[y] that is found is the first one for which
  ~c[(foo x y)] is known to be true, then wasted work will have been done on
  behalf of the first 99 such terms ~c[y] ~-[] unless ~c[:once] has been
  specified, in which case the rule will simply fail after the first binding of
  ~c[y] for which ~c[(rationalp y)] is known to be true.  Thus, a better form
  of the above rule is almost certainly the following.
  ~bv[]
  (implies (and (foo x y)
                (rationalp y))
           (equal (bar x) (bar-prime x)))
  ~ev[]

  ~em[Specifying `once' or `all'.]

  As noted above, the following discussion applies only to ~il[rewrite],
  ~il[linear], and ~il[forward-chaining] rules.
  ~l[free-variables-type-prescription] for a discussion of analogous
  considerations for ~il[type-prescription] rules.

  One method for specifying ~c[:once] or ~c[:all] for free-variable matching is
  to provide the ~c[:match-free] field of the ~c[:rule-classes] of the rule,
  for example, ~c[(:rewrite :match-free :all)].  ~l[rule-classes].  However,
  there are global events that can be used to specify ~c[:once] or ~c[:all];
  ~pl[set-match-free-default] and ~pl[add-match-free-override].  Here are some
  examples.
  ~bv[]
  (set-match-free-default :once)    ; future rules without a :match-free field
                                    ; are stored as :match-free :once (but this
                                    ; behavior is local to a book)
  (add-match-free-override :once t) ; existing rules are treated as
                                    ; :match-free :once regardless of their
                                    ; original :match-free fields
  (add-match-free-override :once (:rewrite foo) (:rewrite bar . 2))
                                    ; the two indicated rules are treated as
                                    ; :match-free :once regardless of their
                                    ; original :match-free fields
  ~ev[]

  ~em[Some history.] Before Version  2.7 the ACL2 rewriter performed Step (2)
  above first.  More significantly, it always acted as though ~c[:once] had
  been specified.  That is, if Step (2) did not apply, then the rewriter took
  the first binding it found using either Steps (1) or (3), in that order, and
  proceeded to relieve the remaining hypotheses without trying any other
  bindings of the free variables of that hypothesis.~/

  :cited-by rule-classes"

; :cited-by set-match-free
  )

(deflabel free-variables-type-prescription
  :doc
  ":Doc-Section Free-Variables

  matching for free variable in ~il[type-prescription] rules~/

  We assume familiarity with the issue of dealing with free variables in
  hypotheses; ~pl[free-variables].

  By default, starting with Version  4.3, ACL2 attempts all possible matches
  for free variables.  Consider the following example.

  ~bv[]
  (defstub f1 (x) t)
  (defstub f2 (x y) t)
  (defstub f3 (y) t)

  (defaxiom f1-prop
    (implies (and (f2 x y) ; <-- y is free in this hypothesis
                  (f3 y))
             (f1 x))       ; <-- (f1 x) is the type-term (type is `non-nil')
    :rule-classes :type-prescription)

  ; Succeeds:
  (thm (implies (and (f2 a b)
                     (f3 b))
                (f1 a)))

  ; The following fails unless we try more than one match for free variables in
  ; hypotheses.
  (thm (implies (and (f2 a b)
                     (f2 a c)
                     (f2 a d)
                     (f3 b))
                (f1 a)))
  ~ev[]

  There may be times when you want to match only the first free variable.  In
  that case, you can write a function of two arguments, the
  ~i[type-prescription] ~il[rune] being applied and the current ACL2 world,
  that prohibits multiple matching for those times.  Your function is then
  `attached' to the built-in constrained function, ~c[oncep-ts].  The following
  examples are intended to explain how this works.

  First, let us disallow all mutliple matching of free variables (i.e.,
  implement the behavior often referred to as ``~c[:match-free :once]'';
  ~pl[free-variables]).
  ~bv[]
  (defun oncep-tp-always (rune wrld)
    (declare (ignore rune wrld)
             (xargs :mode :logic :guard t))
    t)

  (defattach oncep-tp oncep-tp-always)
  ~ev[]
  The second ~c[thm] form above will now fail, because only one free-variable
  match is permitted for the first hypothesis of rule ~c[f1-prop] above.

  Now suppose that instead, we want to disallow multiple matches for free variables
  in hypotheses of type-prescription rules ~em[except] for the rule ~c[f1-prop]
  above.  With the following events, the second ~c[thm] form above once again
  succeeds.
  ~bv[]
  (defun oncep-tp-always-except-f1-prop (rune wrld)
    (declare (ignore wrld)
             (xargs :mode :logic :guard (and (consp rune)
                                             (consp (cdr rune))
                                             (symbolp (cadr rune)))))
    (not (eq (base-symbol rune) 'f1-prop)))

  (defattach oncep-tp oncep-tp-always-except-f1-prop)
  ~ev[]

  In general, your ~ilc[defattach] event will attach a function symbol to
  ~c[oncep-tp].  The ~il[guard] of that function symbol must be implied by the
  tuard of ~c[oncep-tp]:
  ~bv[]
  ACL2 !>:args oncep-tp

  Function         ONCEP-TP
  Formals:         (RUNE WRLD)
  Signature:       (ONCEP-TP * *)
                   => *
  Guard:           (AND (PLIST-WORLDP WRLD)
                        (CONSP RUNE)
                        (CONSP (CDR RUNE))
                        (SYMBOLP (CADR RUNE)))
  Guards Verified: T
  Defun-Mode:      :logic
  Type:            built-in (or unrestricted)

   ONCEP-TP
  ACL2 !>
  ~ev[]~/~/")

(deflabel free-variables-examples
  :doc
  ":Doc-Section Free-Variables

  examples pertaining to free variables in rules~/

  The examples in the two sub-topics of this topic illustrate the handling of
  free variables in rules of class ~c[:]~ilc[rewrite]
  (~pl[free-variables-examples-rewrite]) and of class
  ~c[:]~ilc[forward-chaining] (~pl[free-variables-examples-forward-chaining]),
  respectively.  These implicitly illustrate ~il[free-variables] handling in
  rules of class ~c[:]~ilc[linear] as well.  Also ~pl[free-variables] and
  ~pl[rule-classes].~/~/")

(deflabel free-variables-examples-rewrite

; The second example below could have been given as follows instead, though
; this one is kind of weird since there are free variables on the right-hand
; side of the ground unit rules.

;     (encapsulate
;      (((p1 *) => *)
;       ((p2 * *) => *)
;       ((p3 *) => *)
;       ((a) => *)
;       ((b) => *))
;      (local (defun p1 (x) x))
;      (local (defun p2 (x y) (list x y)))
;      (local (defun p3 (x) x))
;      (local (defun a () 0))
;      (local (defun b () 0)))
;   
;     ; Allow default of :match-free :all (form may be omitted).
;     (set-match-free-error nil)
;   
;     (defaxiom ax1
;       (implies (and (p1 x)
;                     (p2 x y))
;                (p3 y)))
;   
;     (defaxiom p1-a-equals-p2-a-y
;       (equal (p1 (a)) (p2 (a) y)))
;   
;     (defaxiom p1-u-equals-p2-a-y
;       (equal (p1 (b)) (p2 (a) y)))
;   
;     ; Succeeds.
;     (thm (implies (p2 (a) y)
;                   (p3 y)))
;   
;     (add-match-free-override :once t)
;   
;     ; Fails.
;     (thm (implies (p2 (a) y)
;                   (p3 y)))
;   
;     (add-match-free-override :clear)
;   
;     ; Succeeds.
;     (thm (implies (p2 (a) y)
;                   (p3 y)))
;   
;     (add-match-free-override :once (:rewrite string<-l-trichotomy))
;   
;     ; Succeeds.
;     (thm (implies (p2 (a) y)
;                   (p3 y)))

  :doc
  ":Doc-Section Free-Variables-Examples

  examples pertaining to free variables in ~il[rewrite] rules~/

  The following examples illustrate ACL2's handling of free variables in
  ~il[rewrite] rules, as well as user control over how such free variables are
  handled.  ~l[free-variables] for a background discussion.~/

  ~bv[]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Example 1
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defstub p2 (x y) t) ; introduce unconstrained function

  ; Get warning because of free variable.  This would be an error if you had
  ; first executed (set-match-free-error t) in order to force yourself to
  ; specify :match-free (illustrated later, below).
  (defaxiom p2-trans
    (implies (and (p2 x y)
                  (p2 y z))
             (p2 x z)))

  ; Succeeds.
  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))

  ; The following causes an error because p2-trans is not a rune.
  (add-match-free-override :once p2-trans)

  ; After the following, the rewrite rule p2-trans will only allow one
  ; attempt per hypothesis to bind free variables.
  (add-match-free-override :once (:rewrite p2-trans))

  ; Now this same theorem fails to be proved.  Here's why.  The
  ; context for proving (p2 a d) happens to include the hypotheses in
  ; reverse order.  So when the first hypothesis of p2-trans, namely
  ; (p2 x y), is relieved, where x is bound to a (as we are attempting
  ; to rewrite the current literal (p2 a d)), we find (p2 a b) in the
  ; context before (p2 a c) and hence y is bound to b.  The
  ; instantiated second hypothesis of p2-trans is thus (p2 b d), and
  ; the proof fails.  Before the add-match-free-override form above,
  ; the proof succeeded because the rewriter was allowed to backtrack
  ; and find the other binding for the first hypothesis of p2-trans,
  ; namely, y bound to c.  Then the instantiated second hypothesis of
  ; p2-trans is (p2 c d), which is known to be true in the current
  ; context.
  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))

  ; Return to original behavior for binding free variables.
  (add-match-free-override :all t)

  ; Succeeds once again.
  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))

  (u) ; undo (add-match-free-override :all t)

  ; This is an error, since no further arguments should appear after
  ; :clear.
  (add-match-free-override :clear t)

  ; Return all rules to original behavior for binding free variables,
  ; regardless of which previous add-match-free-override forms have
  ; been executed.
  (add-match-free-override :clear)

  ; This succeeds just as it did originally.
  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))

  (ubt! 'p2-trans) ; back to the start, except retain the defstub

  ; Require that :match-free be specified for :linear and :rewrite rules with
  ; free variables.
  (set-match-free-error t)

  ; Fails because :match-free is missing.
  (defaxiom p2-trans
    (implies (and (p2 x y)
                  (p2 y z))
             (p2 x z)))

  ; Fails because :match-free must be followed by :once or :all.
  (defaxiom p2-trans
    (implies (and (p2 x y)
                  (p2 y z))
             (p2 x z))
    :rule-classes ((:rewrite :match-free nil)))

  ; Succeeds, this time with no warning at all.
  (defaxiom p2-trans
    (implies (and (p2 x y)
                  (p2 y z))
             (p2 x z))
    :rule-classes ((:rewrite :match-free :once)))

  ; Fails because we only bind once (see earlier long comment).
  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))

  ; Treat p2-trans as though `:match-free :all' had been specified.
  (add-match-free-override :all (:rewrite p2-trans))

  ; Succeeds since more than one binding is allowed for p2-trans.
  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))

  (u)
  (u)

  ; Specify that future :linear and :rewrite rules with free variables
  ; that do not have :match-free specified are treated as though
  ; `:match-free :once' were specified.
  (set-match-free-default :once)

  ; Succeeds without error since `:match-free' is specified, as described
  ; above.  But there is a warning, since :match-free is not specified for this
  ; :rewrite rule.
  (defaxiom p2-trans
    (implies (and (p2 x y)
                  (p2 y z))
             (p2 x z)))

  ; Fails since only single bindings are allowed for p2-trans.
  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))

  ; Treat p2-trans as though `:match-free :all' had been specified.
  (add-match-free-override :all t)

  ; Succeeds.
  (thm (implies (and (p2 a c)
                     (p2 a b)
                     (p2 c d))
                (p2 a d)))

  ; Test searching of ground units, i.e. rewrite rules without variables on the
  ; left side of the conclusion, for use in relieving hypotheses with free
  ; variables.  This is a very contrived example.

  (ubt! 1) ; back to the start

  (encapsulate
   (((p1 *) => *)
    ((p2 * *) => *)
    ((p3 *) => *)
    ((a) => *)
    ((b) => *))
   (local (defun p1 (x) x))
   (local (defun p2 (x y) (list x y)))
   (local (defun p3 (x) x))
   (local (defun a () 0))
   (local (defun b () 0)))

  ; Allow default of :match-free :all (form may be omitted).
  (set-match-free-error nil)

  (defaxiom ax1
    (implies (and (p2 x y)
                  (p1 y))
             (p3 x)))

  (defaxiom p2-a-b
    (p2 (a) (b)))

  (defaxiom p2-a-a
    (p2 (a) (a)))

  (defaxiom p1-b
    (p1 (b)))

  ; Succeeds; see long comment below on next attempt to prove this
  ; theorem.
  (thm (implies (p2 (a) y)
                (p3 (a))))

  ; Now ax1 will only relieve hypothesis (p2 x y) for one binding of y:
  (add-match-free-override :once t)

  ; Fails when ax1 attempts to rewrite the conclusion to true, because
  ; the most recent ground unit for hypothesis (p2 x y) with x bound
  ; to (a) is rule p2-a-a, which binds y to (a).  If more than one ground
  ; unit could be used then we would backtrack and apply rule p2-a-b,
  ; which binds y to (b) and hence hypothesis (p1 y) of ax1 is
  ; relieved by rule p1-b.
  (thm (implies (p2 (a) y)
                (p3 (a))))

  ; Return rules to original :match-free behavior.
  (add-match-free-override :clear)

  ; Succeeds once again.
  (thm (implies (p2 (a) y)
                (p3 (a))))

  ; Just for kicks, change the behavior of a built-in rule irrelevant
  ; to the proof at hand.
  (add-match-free-override :once (:rewrite string<-l-trichotomy))

  ; Still succeeds.
  (thm (implies (p2 (a) y)
                (p3 (a))))
  ~ev[]

  ~bv[]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Example 2
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ~ev[]

  The next example illustrates the use of the ~il[break-rewrite] facility
  to get information about handling of free variables by the rewriter.
  Explanation is given after this (edited) transcript.  Input begins on lines
  with a prompt (search for ``ACL2''); the rest is output.

  ~bv[]
  ACL2 !>(encapsulate
          ((p1 (u x) t)
           (bad (x) t)
           (p2 (x y z) t)
           (bar (x y) t)
           (foo (x y) t)
           (poo (x y) t)
           (prop (u) t))

          (local (defun p1 (u x) (declare (ignore u x)) nil))
          (local (defun bad (x) (declare (ignore x)) nil))
          (local (defun p2 (x y z) (declare (ignore x y z)) nil))
          (local (defun bar (x y) (declare (ignore x y)) nil))
          (local (defun foo (x y) (declare (ignore x y)) nil))
          (local (defun poo (x y) (declare (ignore x y)) nil))
          (local (defun prop (u) (declare (ignore u)) t))

          (defthm foo-poo
            (implies (syntaxp (equal y 'y3))
                     (equal (foo x y)
                            (poo x y))))

          (defthm lemma-1
            (implies (and (p1 u x)
                          (bad x)
                          (p2 x y z)
                          (bar x y)
                          (equal x x) ; admittedly silly!
                          (foo x y))
                     (prop u))
            :rule-classes ((:rewrite :match-free :all))))

  ; [[ output omitted ]]

  Summary
  Form:  ( ENCAPSULATE ((P1 ...) ...) ...)
  Rules: NIL
  Warnings:  Subsume and Non-rec
  Time:  0.08 seconds (prove: 0.00, print: 0.01, other: 0.06)
   T
  ACL2 !>:brr t
  The monitored runes are:
  NIL
   T
  ACL2 !>:monitor (:rewrite lemma-1) t
  (((:REWRITE LEMMA-1) 'T))
  ACL2 !>(thm (implies (and (p1 u0 x1)
                            (bad x1)
                            (bad x3)
                            (bar x3 y1)
                            (bar x3 y3)
                            (p1 u0 x2)
                            (p1 u0 x3)
                            (p2 x3 y1 z1)
                            (p2 x3 y3 z1))
                       (prop u0)))

  (1 Breaking (:REWRITE LEMMA-1) on (PROP U0):
  1 ACL2 >:eval

  1x (:REWRITE LEMMA-1) failed because :HYP 1 contains free variables.
  The following display summarizes the attempts to relieve hypotheses
  by binding free variables; see :DOC free-variables.

      [1] X : X1
  Failed because :HYP 3 contains free variables Y and Z, for which no
  suitable bindings were found.
      [1] X : X2
  Failed because :HYP 2 rewrote to (BAD X2).
      [1] X : X3
          [3] Z : Z1
              Y : Y1
  Failed because :HYP 6 rewrote to (FOO X3 Y1).
          [3] Z : Z1
              Y : Y3
  Failed because :HYP 6 rewrote to (POO X3 Y3).

  1 ACL2 >:unify-subst
       U : U0
  1 ACL2 >
  ~ev[]
  The ~c[:eval] command above asks the rewriter to attempt to apply the rewrite
  rule ~c[lemma-1] to the term ~c[(prop u0)], shown just above the line with
  ~c[:eval].  As we can see at the end, the variable ~c[u] in the conclusion of
  ~c[lemma-1] is being bound to the variable ~c[u0] in the conjecture.  The
  first hypothesis of ~c[lemma-1] is ~c[(p1 u x)], so the rewriter looks for
  some ~c[x] for which ~c[(p1 u0 x)] is known to be true.  It finds ~c[x1], and
  then goes on to consider the second hypothesis, ~c[(bad x)].  Since the
  theorem we are proving has ~c[(bad x1)] in the hypothesis and ~c[x] is
  currently bound to ~c[x1], the rewriter is satisfied and moves on to the
  third hypothesis of ~c[lemma-1], ~c[(p2 x y z)].  However, ~c[x] is bound
  to ~c[x1] and there are no instances of ~c[y] and ~c[z] for which
  ~c[(p2 x1 y z)] is known in the current context.  All of the above analysis
  is summarized in the first part of the output from ~c[:eval] above:
  ~bv[]
      [1] X : X1
  Failed because :HYP 3 contains free variables Y and Z, for which no
  suitable bindings were found.
  ~ev[]
  Thus, the binding of ~c[x] to ~c[x1] on behalf of the first hypothesis has
  failed.

  The rewriter now backs up to look for other values of ~c[x] that satisfy the
  first hypothesis, and finds ~c[x2] because our current theorem has a
  hypothesis of ~c[(p1 u0 x2)].  But this time, the second hypothesis of
  ~c[lemma-1], ~c[(bad x)], is not known to be true for ~c[x]; that is,
  ~c[(bad x2)] does not rewrite to ~c[t]; in fact, it rewrites to itself.  That
  explains the next part of the output from ~c[:eval] above:
  ~bv[]
      [1] X : X2
  Failed because :HYP 2 rewrote to (BAD X2).
  ~ev[]

  The rewriter now backs up again to look for other values of ~c[x] that
  satisfy the first hypothesis, and finds ~c[x3] because our current theorem
  has a hypothesis of ~c[(p1 u0 x3)].  This time, the second hypothesis of
  ~c[lemma-1] is not a problem, and moreover, the rewriter is able to bind
  ~c[y] and ~c[z] to ~c[y1] and ~c[z1], respectively, in order to satisfy the
  third hypothesis, ~c[(p2 x y z)]: that is, ~c[(p2 x2 y1 z1)] is known in the
  current context.  That explains more of the above output from ~c[:eval]:
  ~bv[]
      [1] X : X3
          [3] Z : Z1
              Y : Y1
  ~ev[]
  Unfortunately, the sixth hypothesis, ~c[(foo x y)], rewrites to itself
  under the above bindings:
  ~bv[]
  Failed because :HYP 6 rewrote to (FOO X3 Y1).
  ~ev[]
  So the rewriter looks for other bindings to satisfy the third hypothesis and
  finds these.
  ~bv[]
          [3] Z : Z1
              Y : Y3
  ~ev[]
  This time, the sixth hypothesis can be rewritten under the above bindings,
  from ~c[(foo x3 y3)] to ~c[(poo x3 y3)] by lemma ~c[foo-poo], but still not
  to ~c[t].
  ~bv[]
  Failed because :HYP 6 rewrote to (POO X3 Y3).
  ~ev[]
  There are no more free variable bindings to try, so this concludes the output
  from ~c[:eval].

  ~bv[]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Example 3
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ~ev[]

  The next pair of examples illustrates so-called ``binding hypotheses''
  (~pl[free-variables]) and explores some of their subtleties.  The first shows
  binding hypotheses in action on a simple example.  The second shows how
  binding hypotheses interact with equivalence relations and explains the role
  of ~ilc[double-rewrite].

  Our first example sets up a theory with two user-supplied rewrite rules, one
  of which has a binding hypothesis.  Below we explain how that binding
  hypothesis contributes to the proof.

  ~bv[]
  ; Define some unary functions.
  (defun f (x) (declare (ignore x)) t)
  (defun g (x) x)
  (defun h (x) x)
  (defun k (x) x)

  ; Prove some simple lemmas.  Note the binding hypothesis in g-rewrite.
  (defthm f-k-h
    (f (k (h x))))
  (defthm g-rewrite
         (implies (and (equal y (k x)) ; binding hypothesis
                       (f y))
                  (equal (g x) y)))

  ; Restrict to a theory that includes the above lemmas but avoids the above
  ; definitions.
  (in-theory (union-theories (theory 'minimal-theory)
                             '(f-k-h g-rewrite)))

  ; Prove a theorem.
  (thm (equal (g (h a)) (k (h a))))
  ~ev[]

  Let us look at how ACL2 uses the above binding hypothesis in the proof of the
  preceding ~c[thm] form.  The rewriter considers the term ~c[(g (h a))] and
  finds a match with the left-hand side of the rule ~c[g-rewrite], binding
  ~c[x] to ~c[(h a)].  The first hypothesis binds ~c[y] to the result of
  rewriting ~c[(k x)] in the current context, where the variable ~c[x] is bound
  to the term ~c[(h a)]; thus ~c[y] is bound to ~c[(k (h a))].  The second
  hypothesis, ~c[(f y)], is then rewritten under this binding, and the result
  is ~c[t] by application of the rewrite rule ~c[f-k-h].  The rule
  ~c[g-rewrite] is then applied under the already-mentioned binding of ~c[x] to
  ~c[(h a)].  This rule application triggers a recursive rewrite of the
  right-hand side of ~c[g-rewrite], which is ~c[y], in a context where ~c[y] is
  bound (as discussed above) to ~c[(k (h a))].  The result of this rewrite is
  that same term, ~c[(k (h a))].  The original call of ~c[equal] then trivially
  rewrites to ~c[t].

  We move on now to our second example, which is similar but involves a
  user-defined equivalence relation.  You may find it helpful to review
  ~c[:equivalence] rules; ~pl[equivalence].

  Recall that when a hypothesis is a call of an equivalence relation other than
  ~c[equal], the second argument must be a call of ~ilc[double-rewrite] in
  order for the hypothesis to be treated as a binding hypothesis.  That is
  indeed the case below; an explanation follows.

  ~bv[]
  ; Define an equivalence relation.
  (defun my-equiv (x y) (equal x y))
  (defequiv my-equiv) ; introduces rule MY-EQUIV-IS-AN-EQUIVALENCE

  ; Define some unary functions
  (defun f (x) (declare (ignore x)) t)
  (defun g (x) x)
  (defun h1 (x) x)
  (defun h2 (x) x)

  ; Prove some simple lemmas.  Note the binding hypothesis in lemma-3.
  (defthm lemma-1
    (my-equiv (h1 x) (h2 x)))
  (defthm lemma-2
    (f (h2 x)))
  (defthm lemma-3
         (implies (and (my-equiv y (double-rewrite x)) ; binding hypothesis
                       (f y))
                  (equal (g x) y)))

  ; Restrict to a theory that includes the above lemmas but avoids the above
  ; definitions.
  (in-theory (union-theories (theory 'minimal-theory)
                             '(lemma-1 lemma-2 lemma-3
                                       my-equiv-is-an-equivalence)))

  ; Prove a theorem.
  (thm (equal (g (h1 a)) (h2 a)))
  ~ev[]

  The proof succeeds much as in the first example, but the following
  observation is key: when ACL2 binds ~c[y] upon considering the first
  hypothesis of ~c[lemma-3], it rewrites the term ~c[(double-rewrite x)] in a
  context where it need only preserve the equivalence relation ~c[my-equiv].
  At this point, ~c[x] is bound by applying ~c[lemma-3] to the term
  ~c[(g (h1 a))]; so, ~c[x] is bound to ~c[(h1 a)].  The rule ~c[lemma-1] then
  applies to rewrite this occurrence of ~c[x] to ~c[(h2 a)], but only because
  it suffices to preserve ~c[my-equiv].  Thus ~c[y] is ultimately bound to
  ~c[(h2 a)], and the proof succeeds as one would expect.

  If we tweak the above example slightly by disabling the user's
  ~il[equivalence] ~il[rune], then the proof of the ~ilc[thm] form fails
  because the above rewrite of ~c[(double-rewrite x)] is done in a context
  where it no longer suffices to preserve ~c[my-equiv] as we dive into the
  second argument of ~c[my-equiv] in the first hypothesis of ~c[lemma-3]; so,
  ~c[lemma-1] does not apply this time.

  ~bv[]
  (in-theory (union-theories (theory 'minimal-theory)
                             '(lemma-1 lemma-2 lemma-3)))

  ; Proof fails in this case!
  (thm (equal (g (h1 a)) (h2 a)))
  ~ev[]
  ~/")

(deflabel free-variables-examples-forward-chaining

; Below is a useful comment contributed by Erik Reeber, who also wrote the
; first version of this documentation topic.

;   I've heard that the worst cases of forward-chaining blow up occur when one
;   forward-chaining rule is feeding another one.  These got worse when
;   :match-free :all showed up.  Previously, such situations were kept in check
;   by putting restrictions on the number of times a forward chaining rule
;   could use a term that was generated by another forward-chaining rule.  This
;   worked pretty well since no forward-chaining rule could generate more than
;   one new term.  However, the match-free :all code allows forward-chaining
;   rules to produce lots of terms.  Thus, such we can generate a lot more
;   rules now.

;   I should probably create such a case since it's a more realisitic situation
;   for slowdown.  I can also imagine some ways to be more restrictive about
;   such cases.  Perhaps, we should consider the number of siblings of a term
;   as well as the number of ancestors it has before we allow new terms to be
;   generated from it.  Or perhaps only the first round should allow match-free
;   :all.

;   The problem with any such solution is that it would make our
;   forward-chaining even harder to explain to new users.

  :doc
  ":Doc-Section Free-Variables-Examples

  examples pertaining to free variables in ~il[forward-chaining] rules~/

  The following examples illustrate ACL2's handling of free variables in
  ~il[forward-chaining] rules, as well as user control over how such free
  variables are handled.  ~l[free-variables] for a background discussion.~/

  ~bv[]
  ; First let us introduce a transitive operation, op, and prove a
  ; forward-chaining rule stating the transitivity of op.

  (encapsulate
   (((op * *) => *))
   (local (defun op (x y) (< x y)))
   (defthm transitivity-of-op
     (implies (and (op x y) (op y z)) (op x z))
     :rule-classes :forward-chaining))

  ; The following theorem is proved by forward chaining, using the above rule.

  (thm
   (implies (and (op u v) (op v w) (op v a))
            (op u w)))

  ; The proof of the theorem just above succeeds because the term (op u v)
  ; triggers the application of forward-chaining rule transitivity-of-op,
  ; binding x to u and y to v.  Free variable z of that rule is bound to both w
  ; and to a, resulting in the addition of both (op u w) and (op u a) to the
  ; context.  However, (op v a) happens to be at the front of the context, so
  ; if only one free-variable binding had been allowed, then z would have only
  ; been bound to a, not to w, as we now illustrate.

  (add-match-free-override :once (:forward-chaining transitivity-of-op))

  (thm ; FAILS!
   (implies (and (op u v) (op v w) (op v a))
            (op u w)))

  :ubt! 1

  ; Starting over, this time we prove transitivity-of-op as a :match-free :once
  ; forward-chaining rule.  Note that the presence of :match-free eliminates
  ; the free-variables warning that we got the first time.

  (encapsulate
   (((op * *) => *))
   (local (defun op (x y) (< x y)))
   (defthm transitivity-of-op
     (implies (and (op x y) (op y z)) (op x z))
     :rule-classes ((:forward-chaining :match-free :once))))

  (thm ; FAILS!
   (implies (and (op u v) (op v w) (op v a))
            (op u w)))

  ; Notice that if we swap the order of the last two hypotheses the theorem
  ; goes through, because this time (op v w) is first in the context.

  (thm ; SUCCEEDS!
   (implies (and (op u v) (op v a) (op v w))
            (op u w)))

  :u

  ; Now let's try setting the default to :once.

  (set-match-free-default :once)

  ; We still get a free-variables warning when we admit this forward-chaining rule.

  (encapsulate
   (((op * *) => *))
   (local (defun op (x y) (< x y)))
   (defthm transitivity-of-op
     (implies (and (op x y) (op y z)) (op x z))
     :rule-classes ((:forward-chaining))))

  ; This theorem fails--as it should.

  (thm ; FAILS!
   (implies (and (op u v) (op v w) (op v a))
            (op u w)))

  ; But if we convert this rule (or here, all possible rules) to :all rules,
  ; then the proof succeeds.

  (add-match-free-override :all t)

  (thm ; SUCCEEDS!
   (implies (and (op u v) (op v w) (op v a))
            (op u w)))

  ; Now let's test a relatively slow :all case (the next thm below).

  :ubt! 1

  (encapsulate
   (((op1 *) => *)
    ((op3 * * *) => *))
   (local (defun op1 (x) (declare (ignore x)) t))
   (local (defun op3 (x0 x1 x2)
            (declare (ignore x0 x1 x2))
            t))
   (defthm op1-op3-property
     (implies (and (op1 x0) (op1 x1) (op1 x2))
              (op3 x0 x1 x2)) 
     :rule-classes ((:forward-chaining :match-free :all))))

  ; The following succeeds, but takes a little time (about a second in one run).

  (thm (implies
        (and (op1 a0) (op1 a1) (op1 a2) (op1 a3) (op1 a4) (op1 a5)
             (op1 a6) (op1 a7) (op1 a8) (op1 a9) (op1 a10) (op1 a11)
             (op1 a12) (op1 a13) (op1 a14) (op1 a15) (op1 a16)
             (op1 a17) (op1 a18) (op1 a19) (op1 a20))
        (op3 a5 a6 a0)))

  (add-match-free-override :once t)

  ; The same theorem now fails because of the add-match-free-override, but is
  ; more than an order of magnitude faster.

  (thm (implies
        (and (op1 a0) (op1 a1) (op1 a2) (op1 a3) (op1 a4) (op1 a5)
             (op1 a6) (op1 a7) (op1 a8) (op1 a9) (op1 a10) (op1 a11)
             (op1 a12) (op1 a13) (op1 a14) (op1 a15) (op1 a16)
             (op1 a17) (op1 a18) (op1 a19) (op1 a20))
        (op3 a5 a6 a0)))

  ; A slight variant succeeds in a negligible amount of time (still with the
  ; :once override above).

  (thm (implies
        (and (op1 a0) (op1 a1) (op1 a2) (op1 a3) (op1 a4) (op1 a5)
             (op1 a6) (op1 a7) (op1 a8) (op1 a9) (op1 a10) (op1 a11)
             (op1 a12) (op1 a13) (op1 a14) (op1 a15) (op1 a16)
             (op1 a17) (op1 a18) (op1 a19) (op1 a20))
        (op3 a5 a20 a20)))

  ; Reality check: This shouldn't give a free-variables warning, and everything
  ; should work great since there are no free variables with this trigger term.

  :ubt! 1

  (encapsulate
   (((op1 *) => *)
    ((op7 * * * * * * *) => *))
   (local (defun op1 (x)
            (declare (ignore x))
            t))
   (local (defun op7 (x0 x1 x2 x3 x4 x5 x6)
            (declare (ignore x0 x1 x2 x3 x4 x5 x6))
            t))
   (defthm op1-op7-property
     (implies (and (op1 x0) (op1 x1) (op1 x2)
                   (op1 x3) (op1 x4) (op1 x5) (op1 x6))
              (op7 x0 x1 x2 x3 x4 x5 x6))
     :rule-classes ((:forward-chaining
                     :trigger-terms ((op7 x0 x1 x2 x3 x4 x5 x6))))))

  ; The following then succeeds, and very quickly.

  (thm (implies (and (op1 a0) (op1 a1) (op1 a2)
                     (op1 a3) (op1 a4) (op1 a5) (op1 a6))
                (op7 a4 a6 a5 a6 a6 a6 a6)))

  ~ev[]~/"
  )

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


; The uses of acl2-loop-only below are simply to give us a debugging
; tool for stack overflows.  When a stack overflow occurs, set :brr t.
; Then provoke the overflow.  Exit from the break and from LP.  In raw
; lisp type
; (cw-gstack)
; to see the gstack near the point of overflow.

; In addition, if one then reenters LP and does
; :monitor (:rewrite car-cons) t
; :q
; then one can do
; (brkpt1 '(:rewrite car-cons) nil nil nil nil nil *deep-gstack* *the-live-state*)
; to walk around the stack.

; Furthermore, one can interrupt ACL2 anytime with ctrl-c and do
; (cw-gstack)
; from within the Raw Lisp Break to see what is happening.  Continue with :r.

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

#-acl2-loop-only
(defparameter *saved-deep-gstack* nil)

(defmacro initial-gstack (sys-fn bkptr &rest args)

; This macro is just (push-gframe sys-fn bkptr ,@args) except it is done on an
; empty gstack.  Thus, it builds an initial gstack with the top-most frame as
; specified.  The frame is built by push-gframe, so all frames are built by
; that macro.

; This is also a convenient place to reset *add-polys-counter*, which is used
; by dmr-string.

  `(let ((gstack nil))
     #-acl2-loop-only (setq *saved-deep-gstack* nil)
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
                (cond ((eq calling-sys-fn 'rewrite-with-lemma)
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
                      (rewritten-body " the rewritten body")
                      (expansion " the expansion")
                      (equal-consp-hack-car " the equality of the cars")
                      (equal-consp-hack-cdr " the equality of the cdrs")
                      (rhs " the rhs of the conclusion")
                      (meta " the result of the metafunction")
                      (nth-update " the result of the nth/update rewriter")
                      (multiply-alists2 " the product of two polys")
                      (forced-assumption " a forced assumption")
                      (proof-checker " proof-checker top level")
                      (otherwise (er hard 'tilde-@-bkptr-phrase
                                     "When ~x0 calls ~x1 we get an unrecognized ~
                                      bkptr, ~x2."
                                     calling-sys-fn called-sys-fn bkptr))))
               (t (er hard 'tilde-@-bkptr-phrase
                      "When ~x0 calls ~x1 we get an unrecognized bkptr, ~x2."
                      calling-sys-fn called-sys-fn bkptr))))
        ((rewrite-with-lemma setup-simplify-clause-pot-lst simplify-clause
                             add-terms-and-lemmas non-linear-arithmetic synp)
         "")
        (t (er hard 'tilde-@-bkptr-phrase
               "When ~x0 calls ~x1 we get an unrecognized bkptr, ~x2."
               calling-sys-fn called-sys-fn bkptr))))

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
           (cw "~x0. Rewriting (to ~@6)~@1,~%     ~Y23,~#4~[~/   under the substitution~%~*5~]"
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
        (rewrite-with-lemma
         (cw "~x0. Attempting to apply ~F1 to~%     ~Y23"
             i
             (access rewrite-rule (cdr (access gframe frame :args)) :rune)
             (car (access gframe frame :args))
             evisc-tuple))
        (add-terms-and-lemmas
         (cw "~x0. Attempting to apply linear arithmetic to ~@1 the term ~
              list~%     ~Y23"
             i
             (let ((obj (cdr (access gframe frame :args))))
               (cond ((eq obj nil) "falsify")
                     ((eq obj t) "establish")
                     (t "simplify")))
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

  ":Doc-Section Other

  debug a rewriting loop or stack overflow~/
  ~bv[]
  Example Forms:
  (cw-gstack)
  (cw-gstack :frames 10)       ; show only the top 10 frames
  (cw-gstack :frames '(1 10))  ; same as above:  show only frames 1 through 10
  (cw-gstack :frames '(10 20)) ; show only frames 10 through 20
  (cw-gstack :evisc-tuple (evisc-tuple 3 4 nil nil))
                               ; print with print-level 3 and print-length 4
  (cw-gstack :evisc-tuple nil) ; print using default ``evisceration'',
                               ;   essentially the same as just above
  (cw-gstack :evisc-tuple '(nil 3 4 (hide)))
                               ; same as just above~/

  General Form:
  (cw-gstack :frames frames :evisc-tuple evisc-tuple)
  ~ev[]
  where ~c[:frames] and ~c[:evisc-tuple] are optional, but if they are
  supplied, their values are evaluated.  The value of ~c[frames] should be
  either a natural number or a list of two natural numbers, the first less than
  the second; and the value of ~c[evisc-tuple] should be an
  evisc-tuple (~pl[evisc-tuple]).  If ~c[:evisc-tuple] is omitted, then
  substructures deeper than 3 are replaced by ``~c[#]'' and those longer than 4
  are replaced by ``~c[...]'', and terms of the form ~c[(hide ...)] are printed
  as ~c[<hidden>].  Also ~pl[set-iprint] for an alternative to printing
  ``~c[#]'' and ``~c[...]''.

  Stack overflows may occur, perhaps caused by looping rewrite rules.  In some
  Lisps, especially GCL, stack overflows often manifest themselves as
  segmentation faults, causing the entire ACL2 image to crash.  Finding looping
  rewrite rules can be tricky, especially if you are using books supplied by
  other people.  (However, ~pl[set-rewrite-stack-limit] for a way to avoid
  stack overflows caused by rewriter loops.)

  A wonderful trick is the following.  When there is a stack overflow during a
  proof, abort and then try it again after turning on rewrite stack monitoring
  with ~c[:]~ilc[brr]~c[ t].  When the stack overflows again, exit to raw Lisp.
  How you exit to raw Lisp depends on which Lisp you are using.  In Allegro
  Common Lisp, for example, the stack overflow will leave you in an interactive
  break.  It is often a good idea to exit the break immediately (e.g., using
  ~c[:pop] if you use Allegro Common Lisp, or ~c[:q] using GCL), which will
  leave you in the top-level ACL2 command loop, after which it is recommended
  to leave that loop using ~c[:]~ilc[q].  That will leave you in raw Lisp.
  Then, execute
  ~bv[]
  (cw-gstack)
  ~ev[]
  If the loop is in the rewriter, it will probably be evident!  You can
  re-enter the ACL2 loop now with ~c[(]~ilc[lp]~c[)].

  If you are in GCL the stack overflow may cause a segmentation fault and abort
  the Lisp job.  This makes it harder to debug but here is what you do.  First,
  re-create the situation just prior to submitting the form that will cause the
  stack overflow.  You can do this without suffering through all the proofs by
  using the ~c[:]~ilc[ld-skip-proofsp] option of ~ilc[ld] to reload your
  scripts.  Before you submit the form that causes the stack overflow, exit the
  ACL2 command loop with ~c[:]~ilc[q].  In raw GCL type:
  ~bv[]
  (si::use-fast-links nil)
  ~ev[]
  This will slow GCL down but make it detect and signal stack overflows rather
  than overwrite the system memory.  Now reenter the ACL2 command loop with
  ~c[(]~ilc[lp]~c[)].

  Now carry on as described above, turning on rewrite stack monitoring with
  ~c[:]~ilc[brr]~c[ t] and provoking the stack overflow.  When it occurs, you
  will be in an interactive break.  Exit to raw Lisp with two successive
  ~c[:]~c[q]'s, one to get out of the error break and the next to get out of
  the top-level ACL2 command loop.  Then in raw GCL execute ~c[(cw-gstack)].

  Suggestion: Once you have found the loop and fixed it, you should execute the
  ACL2 command ~c[:]~ilc[brr]~c[ nil], so that you don't slow down subsequent
  proof attempts.  If you are in GCL, you should also get into raw Lisp and
  execute ~c[(si::use-fast-links t)].~/"

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
; allow the user to watch the attempt to apply the rule.  Rewrite-fncall is
; similarly affected.  Because we find "break-rewrite" a tedious name (in
; connection with user-available macros for accessing context sensitive
; information) we shorten it to simply brr when we need a name that is
; connected with the implementation of "break-rewrite."  There is no
; "break-rewrite" function -- its presence is an illusion -- and we reserve
; the string "break-rewrite" to refer to this mythical function.

; Rather than actually implement "break-rewrite" we sprinkle "break points"
; through the various rewrite functions.  These break points are the functions
; brkpt1 and brkpt2.  The reason we do this is so that we don't have to
; maintain two parallel versions of rewrite.  It is not clear this is
; justification for what is a surprisingly complicated alternative.  But since
; we haven't pursued any other approach, it is not clear that the complications
; are isolated in this one.

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
;     from input-alist (or else retain their values from the the
;     last exit of the 'brr wormhole).
; (2) test-form returns (value t) or (value nil) indicating whether
;     a break is to occur.
; (3) the LD specials are manipulated so that no output appears before
;     test-form is eval'd and an error in the test-form throws you out of
;     the wormhole.  If the test-form returns (value nil), the wormhole
;     entry/exit are entirely silent.

  `(wormhole 'brr
             ,entry-lambda
             ,input-alist
             `(pprogn (restore-brr-globals state)
                      (er-progn
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
             :ld-keyword-aliases ,aliases
             :ld-pre-eval-filter :all
             :ld-pre-eval-print  nil
             :ld-post-eval-print :command-conventions
             :ld-evisc-tuple nil
             :ld-error-triples  t
             :ld-error-action :error
             :ld-query-control-alist nil
             :ld-verbose nil))

(defun initialize-brr-stack (state)

; This is a no-op that returns nil.  But it has the secret side effect of
; setting the brr-global brr-stack to nil.  We don't want to reset all the
; brr-globals: brr-monitored-runes should persist.  The others are irrelevant
; because they will be assigned before they are read.

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

  (cond ((null stack) nil)
        (t (let ((temp (assoc-eq var-name (cdar stack))))
             (cond (temp (cdr temp))
                   (t (lookup-brr-stack var-name (cdr stack))))))))

(defun clean-brr-stack1 (gstack stack)
  (cond ((null stack)
         nil)
        ((equal gstack (caar stack)) stack)
        (t (clean-brr-stack1 gstack (cdr stack)))))

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

  (let ((cleaned-stack (clean-brr-stack1 gstack stack)))
    (prog2$
     (if (not (equal cleaned-stack stack))
         (cw "~%~%Cryptic BRR Message 1:  Sweeping dead frames off ~
              brr-stack.  If this occurs in a reproducible way ~
              without your having to cause a console interrupt or ~
              otherwise break into Lisp, please send a script to ~
              the authors of ACL2.  If, on the other hand, during ~
              this proof you've caused a console interrupt and aborted ~
              from the resulting Lisp break, it is likely that this is ~
              a bit of routine BRR housekeeping.~%~%")

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
; 'unify-subst in the frame of brr-stack that is labelled with the current
; brr-gstack.

  (let ((clean-stack (clean-brr-stack (get-brr-global 'brr-gstack state)
                                      (get-brr-global 'brr-stack state))))
    (lookup-brr-stack var clean-stack)))

(defun put-brr-local1 (gstack var val stack)

; See the Essay on "Break-Rewrite" and the comment in brr-@ above.  We assign
; val to var in the frame labelled by gstack.  This function returns the
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
; binding of 'unify-subst in the frame of brr-stack that is labelled with the
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
       (cw "~%~%Cryptic BRR Message 2:  Discarding dead brr-stack.  ~
            If this occurs in a reproducible way without your having ~
            to cause a console interrupt or otherwise break into Lisp, ~
            please send a script to the authors of ACL2.  If, on the ~
            other hand, during this proof you've caused a console ~
            interrupt and aborted from the resulting Lisp break, it is ~
            likely that this is a bit of routine BRR housekeeping.~%~%")
       (f-put-global 'brr-stack
                    (cons (cons gstack (get-brr-global 'brr-alist state))
                          nil)
                    state))))))

(defun pop-brr-stack-frame (state)

; This function may be used inside code executed within "break-rewrite".  It
; pops the top-most frame off the brr-stack.  Actually, it pops all the frames
; up through the one labelled with the current brr-gstack.

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
                   xterm (if (cdr bad-vars) 1 0) bad-vars))
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

(mutual-recursion

(defun tilde-@-failure-reason-free-phrase (hyp-number alist level unify-subst
                                                      evisc-tuple)

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
                                           new-unify-subst evisc-tuple nil)
           (tilde-@-failure-reason-free-phrase hyp-number
                                               (cdr alist) level unify-subst
                                               evisc-tuple))))))

(defun tilde-@-failure-reason-phrase1 (failure-reason level unify-subst
                                                      evisc-tuple
                                                      free-vars-display-limit)
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
        ((and (consp failure-reason)
              (integerp (car failure-reason)))
         (let ((n (car failure-reason)))
           (case
             (cdr failure-reason)
             (time-out (msg "we ran out of time while processing :HYP ~x0."
                            n))
             (ancestors (msg ":HYP ~x0 is judged more complicated than its ~
                                ancestors (type :ANCESTORS to see the ~
                                ancestors and :PATH to see how we got to this ~
                                point)."
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
                   (msg ":HYP ~x0 contains free variables ~&1, for which no ~
                           suitable bindings were found."
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
                        (msg ":HYP ~x0 contains free variables. The ~
                                following display summarizes the attempts to ~
                                relieve hypotheses by binding free variables; ~
                                see :DOC free-variables.~|~@1~%"
                             n
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
                     level unify-subst evisc-tuple))))))
               ((eq (cadr failure-reason) 'backchain-limit)

; (cddr failure-reason) is the backchain-limit at the point of
; failure.  But that number was calculated by successive additions of
; backchain limits for individual rules and we have no record of which
; rules were involved in this calculation.

                (msg "a backchain limit was reached while processing :HYP ~x0 ~
                      (but we cannot tell you which rule imposed the limit)"
                     n))
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
              (eq (car failure-reason) 'cached))
         (msg "~@0~|*NOTE*: This failure was cached earlier.  Use the hint ~
               :RW-CACHE-STATE ~x1 to disable failure caching."
              (tilde-@-failure-reason-phrase1
               (cdr failure-reason)
               level unify-subst evisc-tuple free-vars-display-limit)
              nil))
        (t (er hard 'tilde-@-failure-reason-phrase1
               "Unrecognized failure reason, ~x0."
               failure-reason))))
)

(defun tilde-@-failure-reason-phrase (failure-reason level unify-subst
                                                     evisc-tuple
                                                     free-vars-display-limit)

; In relieve-hyps1 we store a 'free-vars failure reason in which we formerly
; reversed a "failure-reason-lst", which is really an alist mapping extended
; unify-substs to failure reasons.  Now, we save consing by delaying such
; reversal until the relatively rare times that we are ready to display the
; failure reason.

  (tilde-@-failure-reason-phrase1 (fix-free-failure-reason failure-reason)
                                  level unify-subst evisc-tuple
                                  free-vars-display-limit))

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

(deflabel break-rewrite
  :doc
  ":Doc-Section Break-Rewrite

  the read-eval-print loop entered to ~il[monitor] rewrite rules~/

  ACL2 allows the user to ~il[monitor] the application of rewrite rules.
  When ~il[monitor]ed rules are about to be tried by the rewriter, an
  interactive break occurs and the user is allowed to watch and, in a
  limited sense, control the attempt to apply the rule.  This
  interactive loop, which is technically just a call of the standard
  top-level ACL2 read-eval-print loop, ~ilc[ld], on a ``~il[wormhole] ~il[state]''
  (~pl[wormhole]), is called ``break-rewrite.''  While in
  break-rewrite, certain keyword commands are available for accessing
  information about the context in which the lemma is being tried.
  These keywords are called break-rewrite ``commands.''

  Also ~pl[dmr] (Dynamically Monitor Rewrites) for a related utility, which
  allows you to watch progress of the rewriter in real time.

  To abort from inside break-rewrite at any time, execute 

  For further information, see the related ~c[:]~ilc[doc] topics listed below.
  ~terminal[For broad information on the behavior of break-rewrite, type :more.]~/

  As explained in the documentation for ~ilc[monitor], it is possible to
  cause the ACL2 rewriter to ~il[monitor] the attempted application of
  selected rules.  When such a rule is about to be tried, the rewriter
  evaluates its break condition and if the result is non-~c[nil],
  break-rewrite is entered.

  Break-rewrite permits the user to inspect the current ~il[state] by
  evaluating break-rewrite commands.  Type ~c[:]~ilc[help] in break-rewrite to
  see what the break-rewrite commands are.  However, break-rewrite is
  actually just a call of the general ACL2 read-eval-print loop, ~ilc[ld],
  on a certain ~il[state] and the break-rewrite commands are simply aliases
  provided by the ~ilc[ld]-special ~ilc[ld-keyword-aliases].  ~l[ld] for
  details about this read-eval-print loop.  Thus, with a few
  exceptions, anything you can do at the ACL2 top-level can be done
  within break-rewrite.  For example, you can evaluate arbitrary
  expressions, use the keyword command hack, access ~il[documentation],
  print ~il[events], and even define functions and prove theorems.
  However, the ``certain ~il[state]'' upon which ~ilc[ld] was called is a
  ``~il[wormhole] ~il[state]'' (~pl[wormhole]) because break-rewrite is not
  allowed to have any effect upon the behavior of rewrite.  What this
  means, very roughly but understandably, is that break-rewrite
  operates on a copy of the ~il[state] being used by rewrite and when
  break-rewrite exits the ~il[wormhole] closes and the ~il[state] ``produced''
  by break-rewrite disappears.  Thus, break-rewrite lets you query the
  state of the rewriter and even do experiments involving proofs,
  etc., but these experiments have no effect on the ongoing proof
  attempt.  In particular:

  Note that the output from break-rewrite is sometimes abbreviated by default,
  such as for the term causing the break.  This can be controlled by setting
  the ~c[:term] evisc-tuple; ~pl[set-evisc-tuple].  (Another option: use
  iprinting.  ~l[set-iprint].)  But as noted above, if you use
  ~c[set-evisc-tuple] from inside the break-rewrite ~il[wormhole], its effect
  will disappear when you exit the break.  So you might want to issue a
  ~c[set-evisc-tuple] command from the top level, outside break-rewrite.

  When you first enter break-rewrite a simple herald is printed such
  as:
  ~bv[]
  (3 Breaking (:rewrite lemma12) on (delta a (+ 1 j)):
  ~ev[]
  The integer after the open parenthesis indicates the depth of
  nested break-rewrite calls.  In this discussion we use ~c[3]
  consistently for this integer.  Unless you abort or somehow enter
  unbalanced parentheses into the script, the entire session at a
  given depth will be enclosed in balanced parentheses, making it easy
  to skip over them in Emacs.

  You then will see the break-rewrite ~il[prompt]:
  ~bv[]
  3 ACL2 !>
  ~ev[]
  The leading integer is, again, the depth.  Because breaks often
  occur recursively it is convenient always to know the level with
  which you are interacting.

  You may type arbitrary commands as in the top-level ACL2 loop.  For
  example, you might type:
  ~bv[]
  3 ACL2 !>:help
  ~ev[]
  or
  ~bv[]
  3 ACL2 !>:pe lemma12
  ~ev[]
  More likely, upon entering break-rewrite you will determine the
  context of the attempted application.  Here are some useful
  commands:
  ~bv[]
  3 ACL2 >:target           ; the term being rewritten
  3 ACL2 >:unify-subst      ; the unifying substitution
  3 ACL2 >:path             ; the stack of goals pursued by the rewriter
                            ; starting at the top-level clause being simplified
                            ; and ending with the current application
  ~ev[]
  At this point in the interaction the system has not yet tried to
  apply the ~il[monitor]ed rule.  That is, it has not tried to establish
  the hypotheses, considered the heuristic cost of backchaining,
  rewritten the right-hand side of the conclusion, etc.  When you are
  ready for it to try the rule you can type one of several different
  ``proceed'' commands.  The basic proceed commands are ~c[:ok], ~c[:go], and
  ~c[:eval].
  ~bv[]
  :ok
  ~ev[]
  exits break-rewrite without further interaction.  When
  break-rewrite exits it prints ``~c[3)]'', closing the parenthesis that
  opened the level ~c[3] interaction.
  ~bv[]
  :go
  ~ev[]
  exits break-rewrite without further interaction, but prints out
  the result of the application attempt, i.e., whether the application
  succeeded, if so, what the ~c[:target] term was rewritten to, and if not
  why the rule was not applicable.
  ~bv[]
  :eval
  ~ev[]
  causes break-rewrite to attempt to apply the rule but interaction
  at this level of break-rewrite resumes when the attempt is complete.
  When control returns to this level of break-rewrite a message
  indicating the result of the application attempt (just as in ~c[:go]) is
  printed, followed by the ~il[prompt] for additional user input.

  Generally speaking, ~c[:ok] and ~c[:go] are used when the break in question
  is routine or uninteresting and ~c[:eval] is used when the break is one
  that the user anticipates is causing trouble.  For example, if you
  are trying to determine why a lemma isn't being applied to a given
  term and the ~c[:target] of the current break-rewrite is the term in
  question, you would usually ~c[:eval] the rule and if break-rewrite
  reports that the rule failed then you are in a position to determine
  why, for example by carefully inspecting the ~c[:type-alist] of
  governing assumptions or why some hypothesis of the rule could not
  be established.

  It is often the case that when you are in break-rewrite you wish to
  change the set of ~il[monitor]ed ~il[rune]s.  This can be done by using
  ~c[:]~ilc[monitor] and ~c[:]~ilc[unmonitor] as noted above.  For example, you might want
  to ~il[monitor] a certain rule, say ~c[hyp-reliever], just when it is being
  used while attempting to apply another rule, say ~c[main-lemma].
  Typically then you would ~il[monitor] ~c[main-lemma] at the ACL2 top-level,
  start the proof-attempt, and then in the break-rewrite in which
  ~c[main-lemma] is about to be tried, you would install a ~il[monitor] on
  ~c[hyp-reliever].  If during the ensuing ~c[:eval] ~c[hyp-reliever] is broken
  you will know it is being used under the attempt to apply
  ~c[main-lemma].

  However, once ~c[hyp-reliever] is being ~il[monitor]ed it will be ~il[monitor]ed
  even after ~c[main-lemma] has been tried.  That is, if you let the proof
  attempt proceed then you may see many other breaks on ~c[hyp-reliever],
  breaks that are not ``under'' the attempt to apply ~c[main-lemma].  One
  way to prevent this is to ~c[:eval] the application of ~c[main-lemma] and
  then ~c[:]~ilc[unmonitor] ~c[hyp-reliever] before exiting.  But this case arises
  so often that ACL2 supports several additional ``flavors'' of
  proceed commands.

  ~c[:Ok!], ~c[:go!], and ~c[:eval!] are just like their counterparts
  (~c[:ok], ~c[:go], and ~c[:eval], respectively), except that while
  processing the rule that is currently broken no ~il[rune]s are
  ~il[monitor]ed.  When consideration of the current rule is complete,
  the set of ~il[monitor]ed ~il[rune]s is restored to its original
  setting.

  ~c[:Ok$], ~c[:go$], and ~c[:eval$] are similar but take an additional argument
  which must be a list of ~il[rune]s.  An example usage of ~c[:eval$] is
  ~bv[]
  3 ACL2 !>:eval$ ((:rewrite hyp-reliever))
  ~ev[]
  These three commands temporarily install unconditional breaks on
  the ~il[rune]s listed, proceed with the consideration of the currently
  broken rule, and then restore the set of ~il[monitor]ed rules to its
  original setting.

  Thus, there are nine ways to proceed from the initial entry into
  break-rewrite although we often speak as though there are two, ~c[:ok]
  and ~c[:eval], and leave the others implicit.  We group ~c[:go] with ~c[:ok]
  because in all their flavors they exit break-rewrite without further
  interaction (at the current level).  All the flavors of ~c[:eval]
  require further interaction after the rule has been tried.

  To abort a proof attempt and return to the top-level of ACL2 you may at any
  time type ~c[(a!)] followed by a carriage return.  If you are not in a raw
  Lisp break, you may type ~c[:a!] instead.  The utility ~c[p!] is completely
  analogous to ~c[a!] except that it pops up only one ~ilc[ld] level.  If you
  have just entered the break-rewrite loop, this will pop you out of that loop,
  back to the proof.  ~l[a!] and ~pl[p!].

  We now address ourselves to the post-~c[:eval] interaction with
  break-rewrite.  As noted, that interaction begins with
  break-rewrite's report on the results of applying the rule: whether
  it worked and either what it produced or why it failed.  This
  information is also printed by certain keyword commands available
  after ~c[:eval], namely ~c[:wonp], ~c[:rewritten-rhs], and ~c[:failure-reason].  In
  addition, by using ~ilc[brr@] (~pl[brr@]) you can obtain this
  information in the form of ACL2 data objects.  This allows the
  development of more sophisticated ``break conditions'';
  ~pl[monitor] for examples.  In this connection we point out the
  macro form ~c[(ok-if term)].  ~l[ok-if].  This command exits
  break-rewrite if ~c[term] evaluates to non-~c[nil] and otherwise does not
  exit.  Thus it is possible to define macros that provide other kinds
  of exits from break-rewrite.  The only way to exit break-rewrite
  after ~c[:eval] is ~c[:ok] (or, equivalently, the use of ~ilc[ok-if]).

  ACL2 users who wish to know more about break-rewrite so that they
  can develop more convenient ways to ~il[monitor] rules are encouraged to
  speak to J Moore.

  The rest of this ~il[documentation] discusses a few implementation
  details of break-rewrite and may not be interesting to the typical
  user.

  There is no ACL2 function named break-rewrite.  It is an illusion
  created by appropriate calls to two functions named ~c[brkpt1] and
  ~c[brkpt2].  As previously noted, break-rewrite is ~ilc[ld] operating on a
  ~il[wormhole] ~il[state].  One might therefore wonder how break-rewrite can
  apply a rule and then communicate the results back to the rewriter
  running in the external ~il[state].  The answer is that it cannot.
  Nothing can be communicated through a ~il[wormhole].  In fact, ~c[brkpt1] and
  ~c[brkpt2] are each calls of ~ilc[ld] running on ~il[wormhole] ~il[state]s.  ~c[Brkpt1]
  implements the pre-~c[:eval] break-rewrite and ~c[brkpt2] implements the
  post-~c[:eval] break-rewrite.  The rewriter actually calls ~c[brkpt1] before
  attempting to apply a rule and calls ~c[brkpt2] afterwards.  In both
  cases, the rewriter passes into the ~il[wormhole] the relevant
  information about the current context.  Logically ~c[brkpt1] and ~c[brkpt2]
  are no-ops and ~ilc[rewrite] ignores the ~c[nil] they return.  But while
  control is in them the execution of ~ilc[rewrite] is suspended and cannot
  proceed until the break-rewrite interactions complete.

  This design causes a certain anomoly that might be troubling.
  Suppose that inside break-rewrite before ~c[:evaling] a rule (i.e., in
  the ~c[brkpt1] ~il[wormhole] ~il[state]) you define some function, ~c[foo].  Suppose
  then you ~c[:eval] the rule and eventually control returns to
  break-rewrite (i.e., to ~c[brkpt2] on a ~il[wormhole] ~il[state] with the results
  of the application in it).  You will discover that ~c[foo] is no longer
  defined!  That is because the ~il[wormhole] ~il[state] created during your
  ~c[pre-:eval] interaction is lost when we exit the ~il[wormhole] to resume
  the proof attempt.  The post-~c[:eval] ~il[wormhole] ~il[state] is in fact
  identical to the initial pre-~c[:eval] ~il[state] (except for the results of
  the application) because ~ilc[rewrite] did not change the external ~il[state]
  and both ~il[wormhole] ~il[state]s are copies of it.  A similar issue occurs
  with the use of ~il[trace] utilities: all effects of calling ~ilc[trace$] and
  ~ilc[untrace$] are erased when you proceed from a break in the break-rewrite
  loop.

  There is a lot more to know about break-rewrite, most of which is
  fairly easy to learn from looking at the code, since it is all
  expressed in ACL2.  Feel free to ask questions of J Moore.")

(deflabel break-lemma
  :doc
  ":Doc-Section Break-Rewrite

  a quick introduction to breaking rewrite rules in ACL2~/
  ~bv[]
  Example:
  :brr t                          ; if you haven't done that yet
  :monitor (:rewrite lemma12) t   ; to install a break point on the
                                  ; rule named (:rewrite lemma12)
  ~ev[]~/

  ACL2 does not support Nqthm's ~c[break-lemma] but supports a very
  similar and more powerful break facility.  Suppose some proof is
  failing; apparently some particular rule is not being used and you
  wish to learn why.  Then you need the ACL2 ~il[break-rewrite] facility.
  ~l[break-rewrite] and all of its associated ~c[:]~ilc[doc] topics for
  details.  The following basic steps are required.

  (1) To enable the ``break rewrite'' feature, you must first execute
  ~bv[]
  ACL2 !>:brr t
  ~ev[]
  at the top-level of ACL2.  Equivalently, evaluate ~c[(brr t)].
  ~il[Break-rewrite] stays enabled until you disable it with ~c[(brr nil)].
  When ~il[break-rewrite] is enabled the ACL2 rewriter will run slower than
  normal but you will be able to ~il[monitor] the attempts to apply
  specified rules.

  (2) Decide what ~il[rune]s (~pl[rune]) you wish to ~il[monitor].  For
  example, you might want to know why ~c[(:rewrite lemma12 . 2)] is not
  being used in the attempted proof.  That, by the way, is the name of
  the second rewrite rule generated from the event named ~c[lemma12].

  The command
  ~bv[]
  ACL2 !>:monitor (:rewrite lemma12 . 2) t
  ~ev[]
  will install an ``unconditional'' break point on that rule.  The
  ``~c[t]'' at the end of the command means it is unconditional, i.e., a
  break will occur every time the rule is tried.  ACL2 supports
  conditional breaks also, in which case the ~c[t] is replaced by an
  expression that evaluates to non-~c[nil] when you wish for a break to
  occur.  ~l[monitor].  The above keyword command is, of course,
  equivalent to
  ~bv[]
  ACL2 !>(monitor '(:rewrite lemma12 . 2) t)
  ~ev[]
  which you may also type.  You may install breaks on as many rules
  as you wish.  You must use ~ilc[monitor] on each rule.  You may also
  change the break condition on a rule with ~ilc[monitor].  Use ~ilc[unmonitor]
  (~pl[unmonitor]) to remove a rule from the list of ~il[monitor]ed
  rules.

  (3) Then try the proof again.  When a ~il[monitor]ed rule is tried by the
  rewriter you will enter an interactive break, called ~il[break-rewrite].
  ~l[break-rewrite] for a detailed description.  Very simply,
  ~il[break-rewrite] lets you inspect the context of the attempted
  application both before and after the attempt.  When ~il[break-rewrite]
  is entered it will print out the ``target'' term being rewritten.
  If you type ~c[:go] ~il[break-rewrite] will try the rule and then exit,
  telling you (a) whether the rule was applied, (b) if so, how the
  target was rewritten, and (c) if not, why the rule failed.  There
  are many other commands.  ~l[brr-commands].

  (4) When you have finished using the ~il[break-rewrite] feature you
  should disable it to speed up the rewriter.  You can disable it with
  ~bv[]
  ACL2 !>:brr nil
  ~ev[]
  The list of ~il[monitor]ed rules and their break conditions persists
  but is ignored.  If you enable ~il[break-rewrite] later, the list of
  ~il[monitor]ed rules will be displayed and will be used again by rewrite.

  You should disable the ~il[break-rewrite] feature whenever you are not
  intending to use it, even if the list of ~il[monitor]ed rules is empty,
  because the rewriter is slowed down as long as ~il[break-rewrite] is
  enabled.

  If you get a stack overflow, ~pl[cw-gstack].")

(deflabel brr-commands
  :doc
  ":Doc-Section Break-Rewrite

  ~il[Break-Rewrite] Commands~/
  ~bv[]
  :a!             abort to ACL2 top-level
  :p!             pop one level (exits a top-level break-rewrite loop)
  :target         term being rewritten
  :unify-subst    substitution making :lhs equal :target
  :hyps           hypotheses of the rule
  :hyp i          ith hypothesis of the rule
  :lhs            left-hand side of rule's conclusion
  :rhs            right-hand side of rule's conclusion
  :type-alist     type assumptions governing :target
  :initial-ttree  ttree before :eval (~pl[ttree])
  :ancestors      negations of backchaining hypotheses being pursued
  :wonp           indicates if application succeed (after :eval)
  :rewritten-rhs  rewritten :rhs (after :eval)
  :final-ttree    ttree after :eval (~pl[ttree])
  :failure-reason reason rule failed (after :eval)
  :path           rewrite's path from top clause to :target
  :frame i        ith frame in :path
  :top            top-most frame in :path
  :ok             exit break
  :go             exit break, printing result
  :eval           try rule and re-enter break afterwards
  :ok!            :ok but no recursive breaks
  :go!            :go but no recursive breaks
  :eval!          :eval but no recursive breaks
  :ok$ runes      :ok with runes monitored during recursion
  :go$ runes      :go with runes monitored during recursion
  :eval$ runes    :eval with runes monitored during recursion
  :help           this message
  :standard-help  :help message from ACL2 top-level
  ~ev[]~/

  ~il[Break-rewrite] is just a call of the standard ACL2 read-eval-print
  loop, ~ilc[ld], on a ``~il[wormhole]'' ~il[state].  Thus, you may execute most
  commands you might normally execute at the top-level of ACL2.
  However, all ~il[state] changes you cause from within ~il[break-rewrite] are
  lost when you exit or ~c[:eval] the rule.  You cannot modify ~il[stobj]s from
  within the break.  ~l[break-rewrite] for
  more details and ~pl[ld] for general information about the
  standard ACL2 read-eval-print loop.")

(defdoc dmr
  ":Doc-Section Other

  dynamically monitor rewrites and other prover activity~/

  In addition to utilities that allow you to set breakpoints or print rewriting
  information to the screen ~-[] ~pl[break-rewrite] ~-[] ACL2 provides a
  utility for watching the activity of the rewriter and some other proof
  processes, in real time.  This utility is called ``dmr'', which is an acronym
  for ``dynamically monitor rewrites''.  The utility comes in two parts: an
  ACL2 component that frequently writes a file (the ``dmr file'') containing
  the relevant information, and an Emacs component that frequently displays the
  contents of that file in an Emacs buffer (the ``dmr buffer'').  Other editors
  could, in principle, be programmed to display that file; anyone developing
  such a capability is invited to contribute it to the ACL2 community.

  The dmr utility can be extremely helpful for expensive proofs, especially
  when ACL2 is not providing any output.  The ~il[break-rewrite] and
  ~ilc[accumulated-persistence] utilities may be a bit easier to use, so you
  might want to try those first.  But the dmr utility can be a very helpful
  debugging aide, as it can visually give you a sense of where ACL2 is spending
  its time.

  The Emacs portion of this utility is already loaded if you load the
  distributed Emacs file ~c[emacs/emacs-acl2.el].  Otherwise, invoke the
  following Emacs command, say by typing ~c[Control-X Control-E] after the
  right parenthesis, where ~c[DIR] is the directory of your ACL2 distribution.
  ~bv[]
  (load \"<DIR>/emacs/monitor.el\") ; absolute pathnames might work best
  ~ev[]
  You only need to do that once.  Then each time you want to observe the
  rewriter in action, invoke the following to see it displayed in a buffer,
  which we call the ``dmr buffer'':
  ~bv[]
  Control-t 1
  ~ev[]
  But first you will need to enable monitoring at the ACL2 level:
  ~bv[]
  (dmr-start)
  ~ev[]
  Monitoring has some cost.  So if you have started it, then at some point you
  may want to turn it off when not using it.  Any time the dmr buffer
  (generally called ~c[\"acl2-dmr-<user_name>\"]) is not visible, Emacs
  monitoring is turned off.  You can also turn off Emacs monitoring explicitly,
  with:
  ~bv[]
  Control-t 2
  ~ev[]
  At the ACL2 level you can disable monitoring as follows:
  ~bv[]
  (dmr-stop)
  ~ev[]~/

  ~em[Interpreting the dmr buffer display.]

  We explain the dmr buffer display by way of the following example.  It is a
  snapshot of a dmr buffer taken from one of the distributed workshop books,
  ~c[books/workshops/2004/legato/support/proof-by-generalization-mult.lisp].
  ~bv[]
   0. (DEFTHM . WP-ZCOEF-G-MULTIPLIES)
   1. SIMPLIFY-CLAUSE
     2. Rewriting (to simplify) the atom of literal 18; argument(s) 1
     4. Rewriting (to simplify) the expansion; argument(s) 3|2
     7. Applying (:DEFINITION WP-ZCOEF-G)
  *  8. Rewriting (to simplify) the rewritten body; argument(s) 2|1|2|2
  *  13. Applying (:REWRITE MOD-ZERO . 2)
  *    14. Rewriting (to establish) the atom of hypothesis 4
  *    15. Applying (:META META-INTEGERP-CORRECT)
  ~ev[]
  Each line indicates an ACL2 activity that leads to the activity shown on the
  line just below it.  Moreover, lines are sometimes collapsed to make the
  display more compact.  Consider for example the first few lines.  Above, we
  are proving a theorem named ~c[WP-ZCOEF-G-MULTIPLIES].  Lines 1 and 2 show
  the clause simplification process invokes the rewriter on the 18th literal.
  (Recall that a clause is a disjunction of literals; for example the clause
  ~c[{(NOT A), (NOT B), C}] would be displayed as ~c[(IMPLIES (AND A B) C)].)
  This 18th literal mentioned on line 2 is a function call ~c[(f arg1 ...)],
  and ``~c[argument(s) 1]'' indicates that the rewriter, which works
  inside-out, is considering the first argument (``~c[arg1]'').  Thus the
  display could instead have shown the following.
  ~bv[]
     2. Rewriting (to simplify) the atom of literal 18
     3. Rewriting (to simplify) the first argument
     4. Rewriting (to simplify) the expansion; argument(s) 3|2
  ~ev[]
  But it saved space to combine lines 2 and 3.  Line 4 suggests that the above
  ~c[arg1] is a function call that has been opened up because of an ~c[:expand]
  hint or, perhaps, an expansion directed explicitly by the prover (as can
  happen during induction).  The annotation ``~c[argument(s) 3|2]'' then
  indicates that the rewriter is diving into the third argument of the
  expansion, and then into the second argument of that.  Let us call the result
  ~c[term7] (since it is the one to be considered on line 7).

  Now consider the next two lines:
  ~bv[]
     7. Applying (:DEFINITION WP-ZCOEF-G)
  *  8. Rewriting (to simplify) the rewritten body; argument(s) 2|1|2|2
  ~ev[]
  Line 7 is saying that ~c[term7] (defined above) is modified by applying the
  definition of ~c[WP-ZCOEF-G] to it.  Line 8 then says that the body of this
  definition has been rewritten (with its formals bound to the actuals from
  ~c[term7]) and the rewriter is diving into the subterms of that rewritten
  body, as indicated.  Notice also that line 8 is the first line marked with an
  asterisk (``~c[*]'') in the margin.  This line is the first that is different
  from what was shown the previous time the display was updated (about 1/10
  second earlier, by default).  When a line is marked with an asterisk, so are
  all the lines below it; so the lines without an asterisk are those that have
  been stable since the last display.  In this example we may see line 7 marked
  without an asterisk for a while, which suggests that the rule
  ~c[(:DEFINITION WP-ZCOEF-G)] is expensive.  (Also
  ~pl[accumulated-persistence].)  In general, a line that persists for awhile
  without a leading asterisk can suggest why the proof is taking a long time.

  Finally, note the indentation of line 14 relative to line 13.  Extra
  indentation occurs when an attempt is being made to relieve a hypothesis
  (i.e., rewrite it to ~c[t]).  In particular, rewrites that will be
  incorporated directly into a (top-level) literal are all indented just two
  spaces, starting with the first rewrite directly under a process such as
  ~c[SIMPLIFY-CLAUSE] (shown line 1 above).  If the indentation is at least the
  value of raw Lisp variable ~c[*dmr-indent-max*] (by default, 20), then
  indenttion is restricted to that column, but ACL2 prints ~c[{n}] where n is
  the column that would have been used for indentation if there were no
  maximum.

  You can move the cursor around in the dmr buffer even while it is being
  updated.  But emacs will attempt to keep the cursor no later than the first
  asterisk (``~c[*]'') in the margin.  Thus, you can move the cursor around in
  the stable part of the display, and emacs will keep the cursor in that stable
  part.

  WARNING: Things could go terribly wrong if the same user runs two different
  ACL2 sessions with dmr active, because the same file will be written by two
  different ACL2 processes.

  WARNING: For dmr to work, emacs and ACL2 need to be run on the same machine
  because the file used to communicate between ACL2 and emacs is under
  ~c[/tmp].  Except, you can probably hack around that restriction by changing
  ~c[*dmr-file-name*] in ACL2 (in raw Lisp) and correspondingly in Emacs file
  ~c[monitor.el].

  More generally, advanced users are welcome to search for the string
  ~bv[]
  User-settable dmr variables
  ~ev[]
  in ACL2 files ~c[interface-raw.lisp] and ~c[emacs/monitor.el] in order to
  customize their dmr environments.

  In order to update the dmr file with the latest stack information, interrupt
  ACL2 and then evaluate: ~c[(dmr-flush)].  In order to support resumption of
  the interrupted proof (assuming your host Common Lisp supports resumption),
  evaluation of ~c[(dmr-start)] automatically causes evaluation of the form
  ~c[(set-debugger-enable t)]; ~pl[set-debugger-enable].

  Note for users of the experimental extension ACL2(p) (~pl[parallelism]): when
  waterfall-parallelism has been set to a non-~c[nil] value
  (~pl[set-waterfall-parallelism]), statistics about parallel execution are
  printed instead of the usual information.~/

  :cited-by break-rewrite
  :cited-by accumulated-persistence")

(defun raw-mode-p (state)
  (f-get-global 'acl2-raw-mode-p state))

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
                     #+:non-standard-analysis "(r)"
                     #-:non-standard-analysis ""))
         0 channel state nil)))

; We now develop code to display type-alists nicely.

(defun ts< (x y)

; This is just a heuristic order for the type-alist command (proof-checker and
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
  (cond ((null l1) l2)
        ((null l2) l1)
        ((term-order (car l1) (car l2))
         (cons (car l1) (merge-term-order (cdr l1) l2)))
        (t (cons (car l2) (merge-term-order l1 (cdr l2))))))

(defun merge-sort-term-order (l)
  (cond ((null (cdr l)) l)
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

(defun print-terms (terms iff-flg wrld)

; Print untranslations of the given terms with respect to iff-flg, following
; each with a newline.

; We use cw instead of the fmt functions because we want to be able to use this
; function in print-type-alist-segments (used in brkpt1), which does not return
; state.

  (if (endp terms)
      terms
    (prog2$
     (cw "~q0" (untranslate (car terms) iff-flg wrld))
     (print-terms (cdr terms) iff-flg wrld))))

(defun print-type-alist-segments (segs wrld)

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
                                 wrld)
                    (print-type-alist-segments (cdr segs) wrld)))))

(defun print-type-alist (type-alist wrld)
  (print-type-alist-segments (type-alist-segments type-alist nil) wrld))

; End of code for printing type-alists.

(defun tilde-*-ancestors-stack-msg1 (i ancestors wrld evisc-tuple)
  (cond ((endp ancestors) nil)
        ((eq (car (car ancestors)) :binding-hyp)
         (cons (msg "~c0. Binding Hyp: ~Q12~|~
                          Unify-subst:  ~Q32~%"
                    (cons i 2)
                    (untranslate (dumb-negate-lit (cadr (car ancestors)))
                                 t wrld)
                    evisc-tuple
                    (caddr (car ancestors)))
               (tilde-*-ancestors-stack-msg1 (+ 1 i) (cdr ancestors)
                                             wrld evisc-tuple)))
        (t (cons (msg "~c0. Hyp: ~Q12~|~
                            Runes:  ~x3~%"
                      (cons i 2)
                      (untranslate (dumb-negate-lit (car (car ancestors)))
                                   t wrld)
                      evisc-tuple
                      (car (cddddr (car ancestors))))
                 (tilde-*-ancestors-stack-msg1 (+ 1 i) (cdr ancestors)
                                               wrld evisc-tuple)))))

(defun tilde-*-ancestors-stack-msg (ancestors wrld evisc-tuple)
  (list "" "~@*" "~@*" "~@*"
         (tilde-*-ancestors-stack-msg1 0 ancestors wrld evisc-tuple)))

(defun brkpt1 (lemma target unify-subst type-alist ancestors initial-ttree
                     gstack state)

; #+ACL2-PAR note: since we lock the use of wormholes, brr might be usable
; within the parallelized waterfall.  However, since locks can serialize
; computation, we leave brr disabled for now.  Kaufmann has the following
; reaction to using brr and waterfall parallelism at the same time:

;;; "My immediate reaction is that if someone wants to use brr, they should
;;; turn off parallelism.  I'd probably even make it illegal to have both
;;; waterfall-parallelism enabled and :brr t at the same time."

; Parallelism blemish: cause an error when a user tries to enable parallelism
; and brr is enabled.  Also cause an error when enabling brr and
; waterfall-parallism is enabled.  We do not label this a "wart", because we
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
         (if (assoc-equal (access rewrite-rule lemma :rune)
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
                     (initial-ttree . ,initial-ttree))))
     '(pprogn
       (push-brr-stack-frame state)
       (put-brr-local 'depth (1+ (or (get-brr-local 'depth state) 0)) state)
       (let ((pair (assoc-equal (access rewrite-rule
                                        (get-brr-local 'lemma state)
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
                         (access rewrite-rule (get-brr-local 'lemma state)
                                 :rune)
                         (get-brr-local 'target state)
                         (term-evisc-tuple t state))
                     (value t))))
           (t (pprogn
               (pop-brr-stack-frame state)
               (value nil)))))))
     '(
; If you add commands, change the deflabel brr-commands.
       (:ok
        0 (lambda nil

; Note:  Proceed-from-brkpt1 is not defined in this file!  It is here used
; in a constant, fortunately, because it cannot yet be defined.  The problem
; is that it involves chk-acceptable-monitors, which in turn must look at
; the rules named by given runes, which is a procedure we can define only
; after introducing certain history management utilities.

            (proceed-from-brkpt1 'silent t :ok state)))
       (:go
        0 (lambda nil
            (proceed-from-brkpt1 'print t :go state)))
       (:eval
        0 (lambda nil
            (proceed-from-brkpt1 'break t :eval state)))
       (:ok!
        0 (lambda nil
            (proceed-from-brkpt1 'silent nil :ok! state)))
       (:go!
        0 (lambda nil
            (proceed-from-brkpt1 'print nil :go! state)))
       (:eval!
        0 (lambda nil
            (proceed-from-brkpt1 'break nil :eval! state)))
       (:ok$
        1 (lambda (runes)
            (proceed-from-brkpt1 'silent runes :ok$ state)))
       (:go$
        1 (lambda (runes)
            (proceed-from-brkpt1 'print runes :go$ state)))
       (:eval$
        1 (lambda (runes)
            (proceed-from-brkpt1 'break runes :eval$ state)))
       (:q
        0 (lambda nil
            (prog2$ (cw "Proceed with some flavor of :ok, :go, or :eval, or use ~
                       :p! to pop or :a! to abort.~%")
                    (value :invisible))))
       (:target
        0 (lambda nil
            (prog2$ (cw "~x0~|" (get-brr-local 'target state))
                    (value :invisible))))
       (:hyps
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (access rewrite-rule (get-brr-local 'lemma state) :hyps))
             (value :invisible))))
       (:hyp
        1 (lambda (n)
            (cond
             ((and (integerp n)
                   (>= n 1)
                   (<= n (length (access rewrite-rule (get-brr-local 'lemma state) :hyps))))
              (prog2$ (cw "~X01~|"
                          (nth (1- n) (access rewrite-rule (get-brr-local 'lemma state) :hyps))
                          nil)
                      (value :invisible)))
             (t (er soft :HYP
                    ":HYP must be given an integer argument between 1 and ~x0."
                    (length (access rewrite-rule (get-brr-local 'lemma state) :hyps)))))))
       (:lhs
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (access rewrite-rule (get-brr-local 'lemma state) :lhs))
             (value :invisible))))
       (:rhs
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (access rewrite-rule (get-brr-local 'lemma state) :rhs))
             (value :invisible))))
       (:unify-subst
        0 (lambda nil
            (prog2$
             (cw "~*0"
                 (tilde-*-alist-phrase (get-brr-local 'unify-subst state)
                                       (term-evisc-tuple t state)
                                       5))
             (value :invisible))))
       (:type-alist
        0 (lambda nil
            (prog2$
             (cw "~%Decoded type-alist:~%")
             (prog2$
              (print-type-alist-segments
               (type-alist-segments (get-brr-local 'type-alist state) nil)
               (w state))
              (prog2$
               (cw "~%==========~%Use ~x0 to see actual type-alist.~%"
                   '(get-brr-local 'type-alist state))
               (value :invisible))))))
       (:ancestors
        0 (lambda nil
            (prog2$
             (cw "Ancestors stack (from first backchain (0) to ~
                current):~%~*0~%Use ~x1 to see actual ancestors stack.~%"
                 (tilde-*-ancestors-stack-msg
                  (get-brr-local 'ancestors state)
                  (w state)
                  (term-evisc-tuple t state))
                 '(get-brr-local 'ancestors state))
             (value :invisible))))
       (:initial-ttree
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (get-brr-local 'initial-ttree state))
             (value :invisible))))
       (:final-ttree
        0 (lambda nil
            (prog2$
             (cw "~F0 has not yet been :EVALed.~%"
                 (access rewrite-rule (get-brr-local 'lemma state) :rune))
             (value :invisible))))
       (:rewritten-rhs
        0 (lambda nil
            (prog2$
             (cw "~F0 has not yet been :EVALed.~%"
                 (access rewrite-rule (get-brr-local 'lemma state) :rune))
             (value :invisible))))
       (:failure-reason
        0 (lambda nil
            (prog2$
             (cw "~F0 has not yet been :EVALed.~%"
                 (access rewrite-rule (get-brr-local 'lemma state) :rune))
             (value :invisible))))
       (:wonp
        0 (lambda nil
            (prog2$
             (cw "~F0 has not yet been :EVALed.~%"
                 (access rewrite-rule (get-brr-local 'lemma state) :rune))
             (value :invisible))))
       (:path
        0 (lambda nil
            (prog2$ (cw-gstack)
                    (value :invisible))))
       (:frame
        1 (lambda (n)
            (let ((rgstack (reverse (get-brr-global 'brr-gstack state))))
              (cond
               ((and (integerp n)
                     (>= n 1)
                     (<= n (length rgstack)))
                (prog2$
                 (cw-gframe n
                            (if (= n 1)
                                nil 
                              (access gframe (nth (- n 2) rgstack) :sys-fn))
                            (nth (- n 1) rgstack)
                            nil)
                 (value :invisible)))
               (t (er soft :frame
                      ":FRAME must be given an integer argument between 1 and ~x0."
                      (length rgstack)))))))
       (:top
        0 (lambda nil
            (prog2$
             (cw-gframe 1 nil (car (reverse (get-brr-global 'brr-gstack state))) nil)
             (value :invisible))))
       (:help
        0 (lambda nil
            (doc 'brr-commands)))
       (:standard-help 0 help))))))

(defun brkpt2 (wonp failure-reason unify-subst gstack rewritten-rhs final-ttree
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
                     (rewritten-rhs . ,rewritten-rhs)
                     (rcnst . ,rcnst)
                     (final-ttree . ,final-ttree))))
     '(cond
       ((eq (get-brr-local 'action state) 'silent)
        (prog2$ (cw "~F0)~%" (get-brr-local 'depth state))
                (pprogn
                 (f-put-global 'brr-monitored-runes
                               (get-brr-local 'saved-brr-monitored-runes state)
                               state)
                 (pop-brr-stack-frame state)
                 (value nil))))
       ((eq (get-brr-local 'action state) 'print)
        (pprogn
         (put-brr-local-lst (f-get-global 'brr-alist state) state)
         (prog2$ (if (get-brr-local 'wonp state)
                     (cw "~%~F0 ~F1 produced ~X23.~|~F0)~%" 
                         (get-brr-local 'depth state)
                         (access rewrite-rule
                                 (get-brr-local 'lemma state)
                                 :rune)
                         (get-brr-local 'rewritten-rhs state)
                         (term-evisc-tuple t state))
                   (cw "~%~F0x ~F1 failed because ~@2~|~F0)~%" 
                       (get-brr-local 'depth state)
                       (access rewrite-rule
                               (get-brr-local 'lemma state)
                               :rune)
                       (tilde-@-failure-reason-phrase
                        (get-brr-local 'failure-reason state)
                        1
                        (get-brr-local 'unify-subst state)
                        (term-evisc-tuple t state)
                        (free-vars-display-limit state))))
                 (pprogn
                  (f-put-global 'brr-monitored-runes
                                (get-brr-local 'saved-brr-monitored-runes state)
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
                    (prog2$
                     (if (get-brr-local 'wonp state)
                         (cw "~%~F0! ~F1 produced ~X23.~|~%"
                             (get-brr-local 'depth state)
                             (access rewrite-rule
                                     (get-brr-local 'lemma state)
                                     :rune)
                             (get-brr-local 'rewritten-rhs state)
                             (term-evisc-tuple t state))
                       (cw "~%~F0x ~F1 failed because ~@2~|~%"
                           (get-brr-local 'depth state)
                           (access rewrite-rule
                                   (get-brr-local 'lemma state)
                                   :rune)
                           (tilde-@-failure-reason-phrase
                            (get-brr-local 'failure-reason state)
                            1
                            (get-brr-local 'unify-subst state)
                            (term-evisc-tuple t state)
                            (free-vars-display-limit state))))
                     (value t)))))))
     '(
; If you add commands, change the deflabel brr-commands.     
       (:ok 0 (lambda nil 

; Note:  Exit-brr is not yet defined because it calls proceed-from-brkpt1.
; See the note above about that function.

                (exit-brr state)))
       (:eval  0 (lambda nil
                   (prog2$ (cw "You already have run some flavor of :eval.~%")
                           (value :invisible))))
       (:eval!  0 (lambda nil
                    (prog2$ (cw "You already have run some flavor of :eval.~%")
                            (value :invisible))))
       (:eval$  0 (lambda nil
                    (prog2$ (cw "You already have run some flavor of :eval.~%")
                            (value :invisible))))
       (:go  0 (lambda nil 

; Like :ok, :man.

                 (exit-brr state)))
       (:go!  0 (lambda nil (exit-brr state)))
       (:go$  0 (lambda nil (exit-brr state)))
       (:q  0 (lambda nil
                (prog2$ (cw "Exit with :ok or use :p! to pop or :a! to abort.~%")
                        (value :invisible))))
       (:target
        0 (lambda nil
            (prog2$ (cw "~x0~|" (get-brr-local 'target state))
                    (value :invisible))))
       (:hyps
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (access rewrite-rule (get-brr-local 'lemma state) :hyps))
             (value :invisible))))
       (:hyp
        1 (lambda (n)
            (cond
             ((and (integerp n)
                   (>= n 1)
                   (<= n (length (access rewrite-rule (get-brr-local 'lemma state) :hyps))))
              (prog2$ (cw "~X01~|"
                          (nth (1- n) (access rewrite-rule (get-brr-local 'lemma state) :hyps))
                          nil)
                      (value :invisible)))
             (t (er soft :HYP
                    ":HYP must be given an integer argument between 1 and ~x0."
                    (length (access rewrite-rule (get-brr-local 'lemma state) :hyps)))))))
       (:lhs
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (access rewrite-rule (get-brr-local 'lemma state) :lhs))
             (value :invisible))))
       (:rhs
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (access rewrite-rule (get-brr-local 'lemma state) :rhs))
             (value :invisible))))
       (:unify-subst
        0 (lambda nil
            (prog2$
             (cw "~*0"
                 (tilde-*-alist-phrase (get-brr-local 'unify-subst state)
                                       (term-evisc-tuple t state)
                                       5))
             (value :invisible))))
       (:type-alist
        0 (lambda nil
            (prog2$
             (cw "~%Decoded type-alist:~%")
             (prog2$
              (print-type-alist-segments
               (type-alist-segments (get-brr-local 'type-alist state) nil)
               (w state))
              (prog2$
               (cw "~%==========~%Use ~x0 to see actual type-alist.~%"
                   '(get-brr-local 'type-alist state))
               (value :invisible))))))
       (:ancestors
        0 (lambda nil
            (prog2$
             (cw "Ancestors stack (from first backchain (0) to ~
                current):~%~*0~%Use ~x1 to see actual ancestors stack.~%"
                 (tilde-*-ancestors-stack-msg
                  (get-brr-local 'ancestors state)
                  (w state)
                  (term-evisc-tuple t state))
                 '(get-brr-local 'ancestors state))
             (value :invisible))))
       (:initial-ttree
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (get-brr-local 'initial-ttree state))
             (value :invisible))))
       (:final-ttree
        0 (lambda nil
            (prog2$
             (cw "~x0~|"
                 (get-brr-local 'final-ttree state))
             (value :invisible))))
       (:rewritten-rhs
        0 (lambda nil
            (prog2$
             (cond
              ((or (get-brr-local 'wonp state)
                   (member-eq (get-brr-local 'failure-reason state)
                              '(too-many-ifs rewrite-fncallp)))
               (cw "~x0~|" (get-brr-local 'rewritten-rhs state)))
              (t (cw "? ~F0 failed.~%"
                     (access rewrite-rule
                             (get-brr-local 'lemma state)
                             :rune))))
             (value :invisible))))
       (:failure-reason
        0 (lambda nil
            (prog2$
             (if (get-brr-local 'wonp state)
                 (cw "? ~F0 succeeded.~%"
                     (access rewrite-rule
                             (get-brr-local 'lemma state)
                             :rune))
               (cw "~@0~|"
                   (tilde-@-failure-reason-phrase
                    (get-brr-local 'failure-reason state)
                    1
                    (get-brr-local 'unify-subst state)
                    (term-evisc-tuple t state)
                    (free-vars-display-limit state))))
             (value :invisible))))
       (:path
        0 (lambda nil
            (prog2$ (cw-gstack)
                    (value :invisible))))
       (:frame
        1 (lambda (n)
            (let ((rgstack (reverse (get-brr-global 'brr-gstack state))))
              (cond
               ((and (integerp n)
                     (>= n 1)
                     (<= n (length rgstack)))
                (prog2$
                 (cw-gframe n
                            (if (= n 1)
                                nil 
                              (access gframe (nth (- n 2) rgstack) :sys-fn))
                            (nth (- n 1) rgstack)
                            nil)
                 (value :invisible)))
               (t (er soft :frame
                      ":FRAME must be given an integer argument between 1 and ~x0."
                      (length rgstack)))))))
       (:top
        0 (lambda nil
            (prog2$
             (cw-gframe 1 nil (car (reverse (get-brr-global 'brr-gstack state))) nil)
             (value :invisible))))
       (:help
        0 (lambda nil
            (doc 'brr-commands)))
       (:standard-help 0 help))))))

; We now develop some of the code for an implementation of an idea put
; forward by Diederik Verkest, namely, that patterns should be allowed
; in :expand hints.

(defrec expand-hint
  ((equiv
    .
    alist) ; :none, or a partial unify-subst for matching term against actual
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
              (t (let ((alist-none-p (eq (access expand-hint x :alist) :none)))
                   (mv-let
                    (flg ignore-unify-subst)
                    (cond
                     (alist-none-p
                      (mv (equal (access expand-hint x :pattern) term) nil))
                     (t (one-way-unify1 (access expand-hint x :pattern)
                                        term
                                        (access expand-hint x :alist))))
                    (declare (ignore ignore-unify-subst))
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
                                  (and alist-none-p
                                       (length expand-lst))))
                             (t (expand-permission-result1
                                 term (cdr expand-lst) geneqv wrld)))))
                     (t (expand-permission-result1 term (cdr expand-lst)
                                                   geneqv wrld))))))))
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

; - if hyp is non-nil, then assuming hyp, term is provably equal to the
;   application of unify-subst to new-term;

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
; below did indeed cause a rewriting loop through Version_4.3.

;   (defun first-nondecrease (lst)
;     (cond ((endp lst) nil)
;   	((endp (cdr lst)) (list (car lst)))
;   	((> (car lst) (cadr lst)) (list (car lst)))
;   	(t (cons (car lst) (first-nondecrease (cdr lst))))))
;   
;   (defun removeN (lst n)
;     (cond ((endp lst) nil)		
;   	((zp n) lst)	
;   	(t (removeN (cdr lst) (1- n)))))
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
;   	     (n (len first)))
;   	(let ((remain (longest-nondecrease (removeN lst n))))
;   	  (if (>= n (len remain)) first remain)))))
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

(defun ev-fncall! (fn args state latches aok)

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

; Formerly, here we had (declare (ignore latches)).  But CCL complained
; about unused lexical variable LATCHES when defining/compiling the *1*
; function.  So instead we use LATCHES in a trivial way.

                          (prog2$ latches ; fool CCL; see comment above
                                  (and (null erp)
                                       val)))))))
  #+(and (not acl2-loop-only) lucid)
  (declare (ignore state))
  #-acl2-loop-only
  (return-from ev-fncall!
               (mv nil (apply fn args) latches))
  (ev-fncall fn args state latches nil aok))

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

           (ev-fncall! fn args state nil t))
          (t (ev-fncall fn args state nil nil t)))))

(defun get-evg (q ctx)

; Q is a quotep, or at least we expect it to be.  We cause a hard error if not,
; else we return the "explicit value guts".

  (if (quotep q)
      (cadr q)
    (er hard ctx
        "We expected a quotep in this context, variables, but ~x0 is not a ~
         quotep!"
        q)))

(defun ev-synp (synp-term unify-subst mfc state)

; Synp-term is the quotation of the term to be evaluated.  Unify-subst is the
; unifying substitution presently in force, and mfc is the meta-level context
; (formerly referred to as "metafunction-context").  This function has been
; modeled (weakly) on ev-fncall-meta.

; This call to synp is the result of the macro-expansion of a syntaxp or
; bind-free hyothesis.  Or at least it might as well be; we check in
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

(defun bad-synp-alist (alist unify-subst vars-to-be-bound wrld)

; Alist is the (non-nil non-t) value returned by a synp hypothesis,
; Unify-subst is an alist containing the unifying substitution
; gathered so far, and vars-to-be-bound is either t or a quoted list
; of variables.  We check that alist is indeed an alist, that it does
; not bind any variables already bound in unify-subst, and that it
; only binds variables to ACL2 terms.  If vars-to-be-bound is anything
; other than t, we also require that alist only binds vars present in
; vars-to-be-bound.

; We return nil if the alist is legal, else a string or message suitable for
; printing with ~@.

  (if (alistp alist)
      (bad-synp-alist1 alist
                       unify-subst
                       (get-evg vars-to-be-bound 'bad-synp-alist)
                       wrld)
    "it is not an alist"))

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

; Below, we sketch a proof of the following theorem.

; Theorem.  Suppose that the following is a theorem, where the only axioms for
; ev are evaluator axioms.

;  (implies (ev (hyp-fn term) a)
;           (equal (ev term a) (ev (meta-fn term) a)))

; Suppose in addition that lhs, hyp, and rhs are terms, and that:

;  (hyp-fn (quote lhs)) = (quote hyp)
;  (meta-fn (quote lhs)) = (quote rhs)

; Then the following is a theorem:

;  (implies hyp
;           (equal lhs rhs)).

; The proof of the above theorem uses the following lemma.

; Lemma.  Assume that u is a term, ev is an evaluator for the function symbols
; in u, and a0 is a term of the form (list (cons 'v1 t1) ... (cons 'vn tn))
; where (v1 ... vn) includes all variables occurring free in u and each ti is a
; term.  Let s be the substitution mapping vi to ti (1 <= i <= n).  Then the
; following is a theorem:

;   (ev 'u a0) = u/s

; Proof:  An easy induction on the structure of term u.  Q.E.D.

; We may now prove the theorem.  Let (v1 .. vn) be the variables
; occurring free in lhs, rhs, or hyp.  Let a0 be the term

;  (list (cons 'v1 v1) ... (cons 'vn vn)).

; We instantiate the assumed theorem

;   (implies (ev (hyp-fn term) a)
;            (equal (ev term a) (ev (meta-fn term) a)))

; replacing term by 'lhs and a by a0:

;   (implies (ev (hyp-fn 'lhs) a0)
;            (equal (ev 'lhs a0) (ev (meta-fn 'lhs) a0)))

; which is provably equal, by computation, to:

;   (implies (ev 'hyp a0)
;            (equal (ev 'lhs a0) (ev 'rhs a0)))

; By functional instantiation, we may replace ev by an "extended" evaluator for
; a set of function symbols including all those that occur in hyp, lhs, or rhs.
; (See the comment in defaxiom-supporters.)  Then by the lemma the formula
; above simplifies to

;   (implies hyp
;            (equal lhs rhs))

; as desired.

; We extend the argument above to allow use of attachments (see the Essay on
; Defattach) in metafunctions, assuming that there is no ancestor (including
; siblings) of ev that is also an ancestor of hyp-fn or meta-fn.  (This check
; is implemented in function chk-evaluator-use-in-rule.)  The argument above
; shows then that

;   (implies (ev 'hyp a0)
;            (equal (ev 'lhs a0) (ev 'rhs a0)))

; is a theorem of the evaluation history, h_e, because of the computation step,
; as opposed to the current session history, h_s.  It suffices that h_e not
; contain any attachments to ancestors of ev, because in that case the formula
; above is actually a theorem of the sub-history h' containing all ancestors of
; ev in h_e, by the conservativity of history extension.  But h' is contained
; (as a set) in h_s, so the formula above is in fact a theory of the current
; history, as desired.  It remains then to restrict each defattach event so
; that the resulting evaluation history has no attachments to any ancestor of
; ev, yet still computes (hyp-fn 'lhs) to be 'hyp and (meta-fn 'lhs) to be
; 'rhs.  This is easy to do: restrict to attachment pairs <f,g> for which f is
; ancestral in hyp-fn or meta-fn (and hence none is ancestral in ev).  The
; Attachment Restriction Lemma in the Essay on Defattach justifies that the
; result is a legal evaluation history.  Clearly the computations above use
; only attachments in this restricted set, because of closure under ancestors
; (see in particular the comment about must-be-equal in constraint-info).

; Finally we sketch how to modify the arguments above in the case of
; clause-processors.  In that case we assume that the following has been proved
; in the current session history, where CL and A are variables, B is a term,
; and <CL-LIST> represents the application of a clause-processor, as described
; in :doc clause-processor.

;   (implies (and (pseudo-term-listp CL)
;                 (alistp A)
;                 (EVL (conjoin-clauses <CL-LIST>)
;                       B))
;            (EVL (disjoin CL) A))

; The way this rule is used is to replace a clause by the corresponding
; <CL-LIST>, obtained by applying the clause-processor.  Now imagine a
; particular clause cl0 and corresponding cl-list0 produced by running the
; clause-processor, possibly with attachments.  We instantiate (and slightly
; weaken) the above formula to obtain the following, where as in the case of
; metafunctions, A is a formal alist binding each 'v to v for variable v free
; in cl0.

;   (implies (and (pseudo-term-listp 'cl0)
;                 (alistp A)
;                 (forall a2 (EVL (conjoin-clauses 'cl-list0)
;                             a2))
;            (EVL (disjoin 'cl0) A))

; We are assuming that cl-list0 is provable, which discharges the third
; hypothesis.  The first two discharge trivially, and we conclude that (EVL
; (disjoin 'cl0) A) is a theorem, which implies that clause cl0 holds as per
; the Lemma proved above for the metafunction case.

; But as for metafunctions, we have only shown that (EVL (disjoin 'cl0) A) is
; provable in the evaluation history for the current session.  We now follow
; (but in brief) the same argument as we gave in the metafunctions case.
; First, by the assumption that no common ancestor of ev and the
; clause-processor has an attachment, we may restrict to attachments to
; functions ancestral in the clause-processor.  Then we appeal to a
; conservativity argument to conclude that (EVL (disjoin 'cl0) A) holds in the
; current session history, and therefore so does cl0.

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
; obligation clearly holds.

; So, we enrich the notion of ancestor to include guards.  However, we can
; weaker our notion of ancestor to avoid the next-to-last argument of
; return-last, except when it is used to implement mbe.  This weakening was
; inspired by an example sent to us by Sol Swords, who derived it from his
; actual experience, and is justified by imagining that all such calls of
; return-last are expanded away before storing events.  The parameter rlp
; passed to our functions is true when this special handling of return-last is
; to be performed.

; End of Essay on Correctness of Meta Reasoning

; Rockwell Addition:  This is beginning of the nu-rewriter.  It extends
; right through the beginning of the rewrite clique.

; The NU-Rewriter

; In this section we define the nth/update-nth rewriter, aka
; nu-rewriter, which provides fast simplification of terms of the form
; (nth i (update-nth j v s)) and (nth i (update-nth-array j k v s)).
; Someday we hope to generalize this to arbitrary rules.

; This work was inspired and driven by Matt Wilding and Dave Greve at
; Rockwell Advanced Technology Center.  The abstract algorithm is
; described in "Rewriting for Symbolic Execution of State Machines" by
; J Strother Moore.  That description is referred to in some of the
; comments below as "the paper".

(deflabel nu-rewriter
  :doc
  ":Doc-Section Miscellaneous

  rewriting ~c[NTH]/~c[UPDATE-NTH] expressions~/

  The rewriter contains special provisions for rewriting expressions
  composed of ~c[nth], ~c[update-nth], ~c[update-nth-array], together
  with ~c[let] expressions and other applications of non-recursive
  functions or ~c[lambda] expressions.  For details see the paper
  ``Rewriting for Symbolic Execution of State Machine Models'' by J
  Strother Moore.  Also ~pl[set-nu-rewriter-mode].~/

  The ``nu-rewriter'' is a recent addition to the main rewrite engine
  in ACL2.  Consider the expression
  ~bv[]
   (let ((s (update-nth 1 (new-a x s) s)))
     (let ((s (update-nth 2 (new-b x s) s)))
       (let ((s (update-nth 3 (new-c x s) s)))
         s)))
  ~ev[]
  If the ~c[let]s in this expression are expanded, a very large
  expression results because of the duplicate occurrences of ~c[s]:
  ~bv[]
  (update-nth 3
              (new-c x
                     (update-nth 2
                                 (new-b x
                                        (update-nth 1
                                                    (new-a x s)
                                                    s))
                                 (update-nth 1
                                             (new-a x s)
                                             s)))
              (update-nth 2
                          (new-b x
                                 (update-nth 1
                                             (new-a x s)
                                             s))
                          (update-nth 1
                                      (new-a x s)
                                      s))).
  ~ev[]
  This expansion of the ~c[let] expression can be very expensive in space
  and time.  In particular, the ~c[(new-a x s)] expression might be 
  rewritten many times.

  Now imagine asking what 2nd component of the structure is.  That is,
  consider
  ~bv[]
   (nth 2
        (let ((s (update-nth 1 (new-a x s) s)))
          (let ((s (update-nth 2 (new-b x s) s)))
            (let ((s (update-nth 3 (new-c x s) s)))
              s))))
  ~ev[]
  The normal ACL2 rewrite engine would answer this question by first
  rewriting the arguments to the ~c[nth] expression; in particular, it would
  expand the nested ~c[let] expression to the large nested ~c[update-nth]
  expression and then, using rules such as
  ~bv[]
  (defthm nth-update-nth
    (equal (nth m (update-nth n val l))
           (if (equal (nfix m) (nfix n))
               val (nth m l))))
  ~ev[]
  would reduce the expression to ~c[(new-b x (update-nth 1 (new-a x s) s))].
  
  The purpose of the nu-rewriter is to allow simplifications like this
  without first expanding the ~c[let]s.  The ``nu'' in the name is an
  acronym for ``~c[nth/update-nth]''.  The nu-rewriter knows how to
  move an ~c[nth] into a ~c[let] without expanding the ~c[let] and how
  to simplify it if it nestles up against an ~c[update-nth].

  There are four characteristics of this problem: the presence of
  ~c[nth], the presence of ~c[update-nth], the use of ~c[let] to
  provide ``sequential'' updates, and the use of constant indices.
  ~c[Nth] and ~c[update-nth] need not occur explicitly; they may be
  used inside of definitions of ``wrapper'' functions.  

  Because the nu-rewriter changes the order in which things are rewritten,
  its routine use can make ACL2 unable to reproduce old proofs.  It is
  therefore switched off by default.  If your application exhibits the
  characteristics above, you might wish to switch the nu-rewriter on
  using ~ilc[set-nu-rewriter-mode].

  More will eventually be written about the nu-rewriter.  However, it
  is described in detail in the paper cited at the beginning of this
  documentation topic.~/")

; We first present all of the raw Lisp definitions we will need.
; All of this is concerned with memoization, but some of the memoization
; code is not raw.  

; Rockwell Addition:  A major problem with the nu-rewriter implementation
; is that I do not express it 100% in ACL2 but use a lot of raw Lisp in the
; cache maintenance.  The defparameters below are, of course, only used in
; code that is protected by the acl2-loop-only read conditional for the
; non-logic case.  But the logic case of that code doesn't usually correspond
; to the "real" code.  That is, I will often write
; #-acl2-loop-only ; Rockwell Addition
; (raw lisp code)
; #+acl2-loop-only ; Rockwell Addition
; (acl2 code)
; but the two codes are not equivalent under any stretch of the imagination.
; Every such read conditional ought to be inspected and I would like,
; eventually, to replace them all by ACL2.

; Here are all the defparameters associated with the nu-rewriter.

#-acl2-loop-only ; Rockwell Addition
(defparameter *nth-update-tracingp* nil)

#-acl2-loop-only ; Rockwell Addition
(defparameter *lambda-abstractp* t)

#-acl2-loop-only ; Rockwell Addition
(defparameter *nu-memos* (make-array$ '(65535)))

#-acl2-loop-only ; Rockwell Addition
(defparameter *nu-memos-ens* nil)

#-acl2-loop-only ; Rockwell Addition
(defparameter *nu-memos-wrld* nil)

#-acl2-loop-only ; Rockwell Addition
(defparameter *ring-buffer-size* (the (integer 0 1000) 5))

; The cache is an array, named *nu-memos*, with indices 0 through
; 65534 (inclusive).  Accessing the array at location i returns a pair
; (n . ring), where ring is a ``ring buffer'' described below and n is
; the number of items in the ring.  That number is never larger than
; *ring-buffer-size*.

; Note: The simple-vector forms below cause failure when running interpreted in
; GCL 2.6.6, 2.6.7, and a preliminary version of 2.6.8.  But they are fine in
; GCL 2.7.0 as of April 2006, and when running compiled, so we leave them as
; is.

#-acl2-loop-only ; Rockwell Addition
(defun-one-output initialize-nu-memos (i)
; Call this with i = 65534.
  (declare (type (integer -1 65534) i))
  (cond ((= i -1) nil)
        (t
         (setf (svref (the (simple-vector 65535) *nu-memos*)
                      (the (integer 0 65534) i))
               (cons 0 nil))
         (initialize-nu-memos (- i 1)))))
      
#-acl2-loop-only ; Rockwell Addition
(defun-one-output clear-nu-memos1 (i)
; Call this with i = 65534.
  (declare (type (integer -1 65534) i))
  (cond ((= i -1) nil)
        (t 
         (let ((pair (svref (the (simple-vector 65535) *nu-memos*)
                            (the (integer 0 65534) i))))
           (setf (car pair) 0)
           (setf (cdr pair) nil))
         (clear-nu-memos1 (- i 1)))))

; The answers stored in the cache are sensitive to ens and wrld.  But
; we do not store those objects in the k-tuple of inputs.  Instead, we
; associate them implicitly with the cache.  Every item in the cache
; was computed with ens *nu-memos-ens* and wrld *nu-memos-wrld*.  When
; we clear the cache we actually let the old items persist if the ens
; and wrld are the same.

#-acl2-loop-only ; Rockwell Addition
(defun-one-output clear-nu-memos (reallyp ens wrld)
  (cond ((or reallyp
             (not (and (equal ens *nu-memos-ens*)
                       (eq wrld *nu-memos-wrld*))))
         (clear-nu-memos1 65534)
         (setq *nu-memos-ens* ens)
         (setq *nu-memos-wrld* wrld)
         t)
        (t nil)))

; A ring buffer is a linked list of records.  Each record is actually
; a triple.  The three fields are accessed by the macros below.  These
; macros are used both in raw lisp code and regular code, so they are
; not raw.  A triple is of the form (item next . prev) where item is
; the data item stored in the record and next and prev are pointers to
; the next and previous record in the ring.  This structure is
; circular.  Recall that the number of items in the ring is given
; outside the ring.

(defmacro this-item (x) `(car ,x))
(defmacro next-ptr (x) `(cadr ,x))
(defmacro prev-ptr (x) `(cddr ,x))

; Given two records
; x: (xitem xnext . xprev)
; y: (yitem ynext . yprev)
; the following function links them so that y is the next record after
; x (and x is the previous record to y).
; x: (xitem y . xprev)
; y: (yitem ynext . x)

#-acl2-loop-only ; Rockwell Addition
(defun-one-output link-em (x y)
  (setf (next-ptr x) y)
  (setf (prev-ptr y) x))

#-acl2-loop-only ; Rockwell Addition
(defun-one-output destructive-get-memo1 (d1 d2 d3 ptr0 ptr1 ptr2)

; In general, we do not know (at this level) what the items of our
; ring buffers hold.  But we assume here that we can access the car,
; cadr, and caddr of an item.  This function searches down the link
; structure of ptr2 for an item whose first three elements are d1, d2,
; and d3 respectively.  (We don't want to waste the time and space of
; consing up the key to look for it.)  We fail when ptr2 reaches ptr0,
; and we return nil.  Ptr1 is always the prev record from ptr2.

; ptr0 -> itema <-+
;         ...     |
; ptr1 -> itemi   |
; ptr2 -> itemj   |
;         itemk   |
;         ...     |
;         itemz   |
;            |____|

; Suppose we find that itemj is the one we're looking for (its first
; three elements are d1, d2, and d3).  Then we move it to the front
; so that the ring looks like:

; ptr0 -> itema <-+
;         ...     |
; ptr1 -> itemi   |
;         itemk   |
;         ...     |
;         itemz   |
; ans  -> itemj   |
;            |____|

; and we return ans as the new ring.

  (cond
   ((eq ptr2 ptr0) nil)

   ((and (eq    d1 (car (this-item ptr2)))
         (equal d2 (cadr (this-item ptr2)))
         (equal d3 (caddr (this-item ptr2))))
    
    (link-em ptr1 (next-ptr ptr2))
    (link-em (prev-ptr ptr0) ptr2)
    (link-em ptr2 ptr0)
    ptr2)
   (t (destructive-get-memo1 d1 d2 d3 ptr0 ptr2 (next-ptr ptr2)))))

#-acl2-loop-only ; Rockwell Addition
(defun-one-output destructive-get-memo (d1 d2 d3 rbuff)

; We search rbuff for the item whose first three elements are d1, d2,
; and d3.  We return nil if we don't find it.  If we find it, we
; rearrange the ring so that the found item is at the front and return
; that ring.

  (cond ((null rbuff) nil)
        ((and (eq    d1 (car (this-item rbuff)))
              (equal d2 (cadr (this-item rbuff)))
              (equal d3 (caddr (this-item rbuff))))
         rbuff)
        (t (destructive-get-memo1 d1 d2 d3 rbuff rbuff (next-ptr rbuff)))))

(defun get-memo (recursively term stack memo-alist)

; We ignore memo-alist and use the *nu-memos* as our cache.  Memo-alist is
; a fiction to help us keep our story straight.  We search the cache
; for an item whose first three elements are the first three args above,
; recursively, term, and stack.  If we find it, it will look like:

; (recursively term stack flg term2 stack2 ttree2)

; and means that nth-update-rewrite1 returned (mv flg term2 stack2 ttree2)
; as the answer for

; (nth-update-rewrite1 recursivelyp term stack 
;                      *nu-memos-ens* *nu-memos-wrld* state memo-alist)

; In that case, we return (mv t flg term2 stack2 ttree2).  Otherwise we return
; (mv nil nil nil nil nil).

  #-acl2-loop-only ; Rockwell Addition
  (declare (ignore memo-alist))

; Rockwell Addition:  Non-equivalent read conditionals!

  #-acl2-loop-only ; Rockwell Addition
  (let* ((pair (svref (the (simple-vector 65535) *nu-memos*)
                      (the (integer 0 65534) (mk term stack))))

; (car pair) is a natural number and (cdr pair) is a ring buffer.
; The number is how many items are in the ring buffer.

         (temp (destructive-get-memo recursively term stack (cdr pair))))
    (cond (temp
           (setf (cdr pair) temp)
           (let ((temp1 (cdddr (this-item temp))))
             (mv t
                 (car temp1)
                 (cadr temp1)
                 (caddr temp1)
                 (cadddr temp1))))
          (t (mv nil nil nil nil nil))))
  #+acl2-loop-only ; Rockwell Addition

; Lies.  All lies...  But I can imagine making memo-alist behave this
; way...

  (let ((temp (assoc-equal (list recursively term stack) memo-alist)))
    (cond (temp
           (mv t
               (car (cdr temp))
               (cadr (cdr temp))
               (caddr (cdr temp))
               (cadddr (cdr temp))))
          (t (mv nil nil nil nil nil)))))

#-acl2-loop-only ; Rockwell Addition
(defun-one-output destructive-retire-memo (item rbuff)

; Rbuff is a ring buffer whose first item is the most recently hit and
; whose length is equal to the maximum ring buffer size.  We add item
; into the ring, bumping out the last item (which is the prev of the
; first one) and rotate so that that record is the first.

  (let ((new (prev-ptr rbuff)))
    (setf (this-item new) item)
    new))

#-acl2-loop-only ; Rockwell Addition
(defun-one-output destructive-insert-memo (item rbuff)

; Rbuff is a ring buffer whose size is less than the allowed maximum.
; We add a record for item and make it the first.

  (cond ((null rbuff)
         (let ((temp (cons item (cons nil nil))))
           (setf (next-ptr temp) temp)
           (setf (prev-ptr temp) temp)
           temp))
        (t (let ((temp (cons item (cons nil nil))))
             (link-em (prev-ptr rbuff) temp)
             (link-em temp rbuff)
             temp))))

; These stat functions are only used to print stats about the cache.
; I don't document them.

#-acl2-loop-only ; Rockwell Addition
(defun-one-output nu-memo-stats1 (i buckets items full-buckets)
  (declare (type (integer -1 65534) i))
  (cond
   ((= i -1) (list buckets items full-buckets))
   (t
    (let ((n (car (svref (the (simple-vector 65535) *nu-memos*)
                         (the (integer 0 65534) i)))))
      (if (equal n 0)
          (nu-memo-stats1 (- i 1) buckets items full-buckets)
        (nu-memo-stats1 (- i 1)
                        (+ 1 buckets)
                        (+ n items)
                        (cond ((equal n *ring-buffer-size*)
                               (+ 1 full-buckets))
                              (t full-buckets))))))))

#-acl2-loop-only ; Rockwell Addition
(defun-one-output nu-memo-stats ()
  (let* ((triple (nu-memo-stats1 65534 0 0 0))
         (buckets (car triple))
         (items (cadr triple))
         (full-buckets (caddr triple)))
    (cw " Memo Stats (*ring-buffer-size* = ~x0)~%~
         ~ Items:   ~x1~%~
         ~ Buckets: ~x2~%~
         ~ Full:    ~x3~%"
        *ring-buffer-size*
        items
        buckets
        full-buckets)))

(defun memo-key1 (term)

; We compute a hash key for term.  This is an ACL2 function, not just a
; raw lisp function.  See memo-key.

  (the (unsigned-byte 14)
       (cond ((variablep term) 1)
             ((quotep term)
              (if (integerp (cadr term))
; Rockwell Addition:   I think these two read conditionals are equivalent.
                  #-acl2-loop-only ; Rockwell Addition
                  (if (eq (type-of (cadr term)) 'fixnum)
                      (mod (the fixnum (cadr term)) 16384)
                    (mod (the integer (cadr term))
                         16384)) ; 2^14
                  #+acl2-loop-only ; Rockwell Addition
                  (mod (the integer (cadr term))
                       16384)
                2))
             ((null (fargs term)) 3)
             ((null (cdr (fargs term)))
              (memo-key1 (fargn term 1)))
             (t (mod
                 (the (unsigned-byte 16)
                      (+ (the (unsigned-byte 14)
                              (memo-key1 (fargn term 1)))
                         (the (unsigned-byte 15)
                              (* 2 (the (unsigned-byte 14)
                                        (memo-key1 (fargn term 2)))))))
                 16384)))))

(defun bounded-length (lst ans max)
  (declare (type (signed-byte 30) ans max))

; We assume ans <= max.

  (the-fixnum
   (cond
    ((null lst) ans)
    ((= ans max) max)
    (t (bounded-length (cdr lst) (+ 1 ans) max)))))

(defun memo-key (term stack)

; This is how we compute a hash key for term and stack.

; Experiments suggest that with the hash function below the optimal
; bucket size is 3-4.  But if you change the *s to +s, and the bucket
; size to 5-7, you get slightly better performance even though there
; are many fewer items in the table.



  (the (unsigned-byte 29)
       (* (the (unsigned-byte 14)
               (mod 
                (the (unsigned-byte 28)
                     (* (the (unsigned-byte 14) (memo-key1 term))
                        (the (unsigned-byte 14)
                             (+ 1 (the (unsigned-byte 13)
                                       (bounded-length stack 0 8191))))))
                16384))
          (the (unsigned-byte 15)
               (+ 1 (the (unsigned-byte 14)
                         (memo-key1 (cadr (car stack)))))))))

(defun mk (term stack)
  (the (integer 0 65534)
       (mod (the (unsigned-byte 29)
                 (memo-key term stack))
            65535)))

; These show functions are just used for debugging...

(defun show-rbuff1 (r s)
  (if (eq r s) nil (cons (this-item s) (show-rbuff1 r (next-ptr s)))))

(defun show-rbuff (r)
  (cond ((null r) nil)
        ((eq (next-ptr r) r) (list (this-item r)))
        (t (cons (this-item r) (show-rbuff1 r (next-ptr r))))))
  
; As noted, this implementation of memoization is in raw lisp.  But we
; act as though the memo hash array is an ACL2 object and generally
; pass it around in the variable memo-alist.  Think of memo-alist as
; an alist that really does associate our inputs and outputs in just
; the way the hash array does.  Of course, to add something to it we
; would have to cons and we don't do that.  In fact, the memo-alist
; starts as nil and stays nil and is totally irrelevant except that it
; provides a fiction that explains what we're doing.  The logical code
; grows the alist but that never, in fact, happens.

(defun memo-exit (recursivelyp term stack flg term2 stack2 ttree2 memo-alist)

; We know that term/stack (with recursivelyp) doesn't occur in
; memo-alist.  If flg is non-nil, we modify memo-alist so that it does
; memoize this call.  In any case, we return the appropriate result.

  (mv flg
      term2
      stack2
      ttree2

; Rockwell Addition:  Non-equivalent read conditionals!

      #-acl2-loop-only ; Rockwell Addition
      (if flg
          (let* ((k (the (integer 0 65534)
                         (mk term stack)))
                 (pair (svref (the (simple-vector 65535) *nu-memos*)
                              (the (integer 0 65534) k)))
                 (item (list recursivelyp term stack flg term2 stack2 ttree2)))
            (declare (type (integer 0 65534) k))
            (cond
             ((= (the (integer 0 1000)
                      (car pair))
                 (the (integer 0 1000)
                      *ring-buffer-size*))
              (setf (cdr pair)
                    (destructive-retire-memo item (cdr pair))))
             (t (setf (car pair) (the (integer 0 1000)
                                      (+ 1
                                         (the (integer 0 999) (car pair)))))
                (setf (cdr pair)
                      (destructive-insert-memo item (cdr pair)))))
            memo-alist)
        memo-alist)
      #+acl2-loop-only ; Rockwell Addition

; Lies...  We ought to modify memo-alist so that old entries that
; hash to the same key get deleted if there are too many...

      (cons (cons (list recursivelyp term stack)
                  (list flg term2 stack2 ttree2))
            memo-alist)))

; Now we get to the ACL2 code.

(defun nfix-quote (x)

; X is known to be a quotep.  We return the result of nfixing it.

  (if (and (integerp (cadr x))
           (<= 0 (cadr x)))
      x
    *0*))

; Stack is a list of frames.  Each frame is of the form (vars . terms)
; and denotes the substitution carried out by subcor-vars.  We will write
; term/stack to mean the instance of term obtained by successively
; applying each substitution in the stack, starting with the top-most.
; Alternatively, term/stack is just a lambda application, e.g.,
; term/((vars1 . args1) ... (varsk . argsk)) is
; ((lambda varsk
;    ...
;    ((lambda vars1 term)
;     args1))
;  argsk)

(defun bound-in-framep (var vars terms)

; We exploit the fact that nil is not a term.  We return the term to which
; var is bound or else we return nil.

  (cond ((endp vars) nil)
        ((eq var (car vars)) (car terms))
        (t (bound-in-framep var (cdr vars) (cdr terms)))))

(defun non-rec-defun1 (lemmas ens ttree)
  (cond
   ((endp lemmas)
    (mv nil nil ttree))
   (t
    (let* ((lemma (car lemmas))
           (subclass (access rewrite-rule lemma :subclass)))

; Note: It is assumed (twice) below that a rune whose base symbol is
; the name of the function the rule rewrites is the definition of the
; function.  That is suppose the rule of some rune (:REWRITE fn) is
; (equal (fn ...)  ...)  Then we assume that this is the introduction
; of fn.  The introduction of a function symbol can only be by
; constraint (which must have a different name than the function
; symbol itself) or by DEFUN, which uses the convention assumed here.
; The impact of our assumption is that if the rune is so named it is
; not necessary to check that the args of the lhs are distinct
; variables: that is ensured by DEFUN.

      (cond
       ((and (eq subclass 'definition)
             (eq (access rewrite-rule lemma :equiv) 'equal)
             (null (access rewrite-rule lemma :hyps))
             (null (car (access rewrite-rule lemma :heuristic-info)))
             (enabled-numep (access rewrite-rule lemma :nume) ens)
             (or (eq (ffn-symb (access rewrite-rule lemma :lhs))
                     (cadr (access rewrite-rule lemma :rune)))
                 (and
                  (symbol-listp (fargs (access rewrite-rule lemma :lhs)))
                  (no-duplicatesp (fargs (access rewrite-rule lemma :lhs))))))
        (mv (fargs (access rewrite-rule lemma :lhs))
            (access rewrite-rule lemma :rhs)
            (push-lemma (access rewrite-rule lemma :rune) ttree)))
       ((and (eq subclass 'abbreviation)
             (eq (access rewrite-rule lemma :equiv) 'equal)
             (enabled-numep (access rewrite-rule lemma :nume) ens)
             (or (eq (ffn-symb (access rewrite-rule lemma :lhs))
                     (cadr (access rewrite-rule lemma :rune)))
                 (and
                  (symbol-listp (fargs (access rewrite-rule lemma :lhs)))
                  (no-duplicatesp (fargs (access rewrite-rule lemma :lhs))))))
        (mv (fargs (access rewrite-rule lemma :lhs))
            (access rewrite-rule lemma :rhs)
            (push-lemma (access rewrite-rule lemma :rune) ttree)))
       (t (non-rec-defun1 (cdr lemmas) ens ttree)))))))

(defun non-rec-defun (fn ens wrld ttree)

; Fn must be a function symbol or lambda expression.  We return (mv
; formals body ttree'), where, if body is non-nil, it is a theorem that:

; (equal (fn . formals) body)

; and formals is a list of distinct variable names.  Ttree' is an
; extension of ttree that records the rule we used.  Furthermore, the
; rule is enabled, body is non-recursive in fn, and fn is neither HIDE
; nor NTH-UPDATE-ARRAY (which are treated here as though they were
; undefined).

; If fn is an enabled non-recursive function (other than HIDE, etc),
; we return the standard formals and body from its def-body.
; Otherwise, we look for the most recently proved enabled
; non-recursive unconditional EQUALity :definition of fn with distinct
; vars on the lhs.

; Note: If you prove a non-recursive unconditional :definition of a
; function and you want it used by the nu-rewriter as though it were
; the definition, you must DISABLE the function.  Otherwise, we just
; use the standard formals and body as above.  This decision was made
; for efficiency.  It is expensive to go to the property list and scan
; all the lemmas looking for an enabled non-recursive unconditional
; EQUALity :definition of fn with distinct vars on the lhs --
; especially if we do it every time that deref recurs!

  (cond ((flambdap fn)
         (mv (lambda-formals fn)
             (lambda-body fn)
             ttree))
        ((or (eq fn 'if)
             (eq fn 'hide)
             (eq fn 'update-nth-array))
         (mv nil nil ttree))
        (t (let ((def-body (def-body fn wrld)))
             (cond
              ((or (null def-body)
                   (access def-body def-body :recursivep))
               (mv nil nil ttree))
              ((enabled-numep (access def-body def-body :nume) ens)
               (let ((formals (access def-body def-body :formals)))
                 (mv formals
                     (latest-body (fcons-term fn formals)
                                  (access def-body def-body :hyp)
                                  (access def-body def-body :concl))
                     (push-lemma (access def-body def-body :rune)
                                 ttree))))
              (t ; (print (list 'checking fn 'props))
               (non-rec-defun1
                (getprop fn 'lemmas nil 'current-acl2-world wrld)
                ens
                ttree)))))))

; The paper talks about ``facets.''  But we never create facets as
; objects in this code.  Instead, we keep pairs of variables, e.g.,
; term and stack, that together represent the facet in question.

(mutual-recursion

(defun deref-var (var stack ens wrld ttree)

; We return (mv term' stack' ttree'), where <term',stack'> is the
; preferred facet of <var,stack> and ttree' is an extension of ttree
; that records the runes used.

  (cond
   ((endp stack)
    (mv var nil ttree))
   (t (let ((temp (bound-in-framep var (car (car stack)) (cdr (car stack)))))
        (cond (temp (deref temp (cdr stack) ens wrld ttree))
              (t (deref-var var (cdr stack) ens wrld ttree)))))))

(defun deref (term stack ens wrld ttree)
  (cond ((variablep term)
         (deref-var term stack ens wrld ttree))
        ((fquotep term)
         (mv term nil ttree))
        (t (let ((fn (ffn-symb term)))
             (mv-let
              (formals body ttree)
              (non-rec-defun fn ens wrld ttree)
              (cond
               (body
                (deref body
                       (cons (cons formals (fargs term))
                             stack)
                       ens wrld ttree))
               (t (mv term stack ttree))))))))
)

; Once upon a time we used the following code to determine whether two
; facets are equal.  But in Rockwell trials it never did anything
; different than the faster version used below.

; (mutual-recursion
; 
;  (defun equal-derefs (term1 stack1 term2 stack2 ens wrld)
;   (mv-let
;    (term1 stack1)
;    (deref term1 stack1 ens wrld)
;    (mv-let
;     (term2 stack2)
;     (deref term2 stack2 ens wrld)
;     (cond
;      ((and (equal term1 term2)
;            (equal stack1 stack2))
;       t)
;      ((variablep term1)
; 
; ; When deref returns a var, it is unbound.  If both are vars, they are
; ; denote equal terms precisely if they are the same (unbound) var.  If
; ; one is a var and the other isn't, we don't know if they denote equal
; ; terms.
; 
;       (if (equal term1 term2)
;           t
;         '?))
;      ((variablep term2) '?)
;      ((fquotep term1)
;       (if (fquotep term2)
;           (equal term1 term2)
;         '?))
;      ((fquotep term2) '?)
;      ((eq (ffn-symb term1) (ffn-symb term2))
;       (equal-derefs-lst (fargs term1) stack1
;                         (fargs term2) stack2
;                         ens wrld))
;      (t '?)))))
; 
;  (defun equal-derefs-lst (term-lst1 stack1 term-lst2 stack2 ens wrld)
;   (cond ((endp term-lst1) t)
;         (t (let ((flg (equal-derefs (car term-lst1) stack1
;                                     (car term-lst2) stack2
;                                     ens wrld)))
;              (cond
;               ((eq flg t)
;                (equal-derefs-lst (cdr term-lst1) stack1
;                                  (cdr term-lst2) stack2
;                                  ens wrld))
;               (t '?)))))))

(defun equal-derefs (term1 stack1 term2 stack2)
  (cond
   ((and (quotep term1)
         (quotep term2))
    (equal (cadr term1) (cadr term2)))
   ((and (equal term1 term2)
         (equal stack1 stack2))
    t)
   (t '?)))

; Next we develop the notion of lambda abstraction, i.e., how to
; create the lambda application corresponding to the facet
; <term,stack>.  The interesting part is creating simple, correct
; lambda applications.

(defun filter-args (formals vars actuals)
  (cond ((endp formals) nil)
        ((member-eq (car formals) vars)
         (cons (car actuals) (filter-args (cdr formals) vars (cdr actuals))))
        (t (filter-args (cdr formals) vars (cdr actuals)))))

(mutual-recursion

(defun foccurrences (term1 term2 ans)

; We ``count'' the number of occurrences of term1 in term2,
; ``summing'' the result into ans to be tail recursive, except:

; ans = nil means we've seen 0
; ans = t   means we've seen 1
; ans = >   means we've seen 2 or more

; Thus, nil + 1 = t
;       t + 1   = >
;       > + 1   = >
; so (+ ans 1) is (if ans '> t) and we can short-circuit whenever ans
; is >.

; Observe that if (eq (foccurrences term1 term2 t) '>) is t, then term1
; occurs at least once in term2.  This could also be tested by asking
; whether (foccurrences term1 term2 nil) is non-nil, but that idiom is
; less efficient because the former short-circuits as soon as the
; first occurrence is found, while the latter doesn't short-circuit
; until the second occurrence (if any) is found.

  (cond
   ((equal term1 term2) (if ans '> t))
   ((eq ans '>) '>)
   ((variablep term2) ans)
   ((fquotep term2) ans)
   (t (foccurrences-lst term1 (fargs term2) ans))))

(defun foccurrences-lst (term lst ans)
  (cond ((endp lst) ans)
        ((eq ans '>) '>)
        (t (foccurrences-lst term
                             (cdr lst)
                             (foccurrences term (car lst) ans))))))

(defun every-var-at-most-oncep (vars body)

; Return t iff every var in vars occurs at most once in body.  That
; is, if no var in vars occurs more than once.

  (cond ((endp vars) t)
        ((eq (foccurrences (car vars) body nil) '>)
         nil)
        (t (every-var-at-most-oncep (cdr vars) body))))

(defun every-actual-simple (args)
  (cond ((endp args) t)
        ((or (variablep (car args))
             (fquotep (car args)))
         (every-actual-simple (cdr args)))
        (t nil)))

(defun make-clean-lambda-application (formals body args)

; Build a lambda application ((lambda formals body) . args), except
; clean it up.  For example ((lambda (s) s) a) becomes just a,
; ((lambda (s) '123) a) becomes just '123, and ((lambda (x y) (foo x))
; a b) becomes ((lambda (x) (foo x)) a).

; WARNING: This function invites incorrect improvements!  Don't mess
; with body!  For example one might be tempted to substitute into body
; for some of the formals (e.g., those occurring only once) while
; leaving the duplicated formals.  This would be wrong.  It might
; introduce a var into body that is not bound in the formals.  It
; might also cause a var in the body to be captured by the remaining
; formals.  Just don't mess with body unless you're clear headed!

  (let ((body-vars (all-vars body)))
    (cond ((not (subsetp-eq body-vars formals))
           (er hard 'make-clean-lambda-application
               "It was supposedly impossible to derive a lambda body ~
                containing variables not bound in the lambda formals.  ~
                But the proposed lambda body ~p0 contains variables not ~
                in ~x1."
               body formals))
          ((null body-vars)

; ((lambda (v1 ... vk) 'evg) a1 ... ak) => 'evg.  However, we also deal here
; with the case that the body is a non-quoted constant involving no vars,
; like (F (G) (H)).

           body)
          ((every-var-at-most-oncep body-vars body)

; ((lambda (v1 ... vk) vi) a1 ... ak) => ai 
; ((lambda (v1 ... vk) (f vi vj)) a1 ... ak) => (f ai aj).

; We could, in general, always return the following, it is just an
; explosive idea if some var occurs more than once.

           (subcor-var formals args body))
          (t (let ((minimal-formals
                    (filter-args formals body-vars formals))
                   (minimal-args
                    (filter-args formals body-vars args)))
               (cond
                ((every-actual-simple minimal-args)
                 (subcor-var minimal-formals minimal-args body))
                ((subsetp minimal-formals body-vars)
                 (fcons-term (make-lambda minimal-formals body) minimal-args))
                (t 
                 (fcons-term (make-lambda minimal-formals
                                          body)
                             minimal-args))))))))

(defun lambda-stack (stack term)

; Build the lambda application denoted by term/stack.

  (cond ((endp stack)
         term)
        (t (lambda-stack
            (cdr stack)
            (make-clean-lambda-application (car (car stack))
                                           term
                                           (cdr (car stack)))))))

; We next deal with reconciliaton.  The version described in the paper
; is quite simple and is implemented below.  But for many weeks we
; experimented with a different version, based on a notion called
; ``widgets.''  That version was ultimately unsound.  But it might
; actually be better than the simple version and if you are interested
; in improving reconcilliation, look for the file
; /v/hank/v104/rockwell/acl2x/v2-5/rewrite.lisp and find the first
; occurrence of the word "widget."

; The function that reconciles a list of stacks is strange in that it
; ignores those stacks corresponding to quoted constants.  So most of
; these functions take a list of terms and skip the stack in question
; if the term is quoted.  To understand what is going on, see
; reconcile-stacks.

(defun shorten-each-stack-to-len (n terms stacks)

; We shorten each stack in stacks to be length n, except those that
; correspond to quoted terms, which are simply set to nil.

  (cond ((endp stacks) nil)
        (t (cons (cond ((quotep (car terms))
                        nil)
                       (t (nthcdr (- (len (car stacks)) n) (car stacks))))
                 (shorten-each-stack-to-len n (cdr terms) (cdr stacks))))))

(defun all-equal-stacks (the-stack terms stacks)
  (cond ((endp stacks) t)
        ((quotep (car terms))
         (all-equal-stacks the-stack (cdr terms) (cdr stacks)))
        ((eq the-stack t)
         (all-equal-stacks (car stacks) (cdr terms) (cdr stacks)))
        (t (and (equal the-stack (car stacks))
                (all-equal-stacks the-stack (cdr terms) (cdr stacks))))))

(defun non-quoted-stack (terms stacks)
  (cond ((endp stacks) nil)
        ((quotep (car terms))
         (non-quoted-stack (cdr terms) (cdr stacks)))
        (t (car stacks))))

(defun cdr-all (x)
  (cond ((endp x) nil)
        (t (cons (cdr (car x)) (cdr-all (cdr x))))))

(defun len-common-tail (n terms stacks)
  (cond ((zp n) 0)
        ((all-equal-stacks t terms stacks) n)
        (t (len-common-tail (- n 1) terms (cdr-all stacks)))))

(defun butlast-all-stacks (terms stacks n)
  (cond ((endp stacks) nil)
        (t (cons (if (quotep (car terms))
                     nil
                   (butlast (car stacks) n))
                 (butlast-all-stacks (cdr terms) (cdr stacks) n)))))

(defun min-stack-len (terms stacks)
  (cond ((endp stacks) nil)
        ((quotep (car terms))
         (min-stack-len (cdr terms) (cdr stacks)))
        (t (let ((x (len (car stacks)))
                 (temp (min-stack-len (cdr terms) (cdr stacks))))
             (cond
              (temp (min x temp))
              (t x))))))

(defun reconcile-stacks (terms stacks)

; For the moment, forget about terms.  Stacks is a list of n stacks,
; (stack1 ... stackn).  We return (mv (list ext1 ... extn) stack),
; where stack is the greatest common ancestor of all the stacki and
; each exti has the property stacki = (append exti stack).

; For example, if stacks is:
; ((a b c d e f g)
;      (x d e f g)
;    (y y d e f g)
;      (z d e f g)
;  (u u u d e f g))
;        ^
; then we return (mv '((a b c) (x) (y y) (z) (u u u)) '(d e f g)).
; (The above are not really stacks, but function doesn't look at the
; structure beyond what is shown above.)  We do this by first
; computing the length of the shortest stack, in this case 5.  We then
; shorten every stack to that length.  Then we compare them all.  If
; they're all the same, that's our common ancestor.  Else, we cdr each
; and repeat.  Once we find the common ancestor, we use butlast to
; compute the initial part of each stack, where (butlast '(y y d e f
; g) 4) is (y y).

; Now what about terms?  It is a list of n terms, in 1:1
; correspondence with stacks.  Each termi is interpreted under stacki.
; But if a term is a quoted constant, its interpretation is fixed
; regardless of the stack.  So we do not let the stacks of the quoted
; terms influence our answer.

  (let ((min-len (min-stack-len terms stacks)))
    (cond
     ((null min-len)

; Then all the terms are quoted.

      (mv (butlast-all-stacks terms stacks 0) ; just a list of nils
          nil))
     (t
      (let ((n (len-common-tail min-len
                                terms
                                (shorten-each-stack-to-len min-len
                                                           terms stacks))))
        (if (zp n)
            (mv stacks nil)
          (mv (butlast-all-stacks terms stacks n)
              (let ((stack (non-quoted-stack terms stacks)))
                (nthcdr (- (len stack) n) stack)))))))))

(defun reconcile-terms (terms exts)
  (cond
   ((endp terms) nil)
   (t (cons (lambda-stack (car exts) (car terms))
            (reconcile-terms (cdr terms) (cdr exts))))))

(defun all-equal (x lst)
  (cond ((endp lst) t)
        (t (and (equal x (car lst))
                (all-equal x (cdr lst))))))

(defun recon (terms stacks)

; Terms and stacks are in 1:1 correspondence.  We return (mv terms' stack).
; Terms' and terms are in 1:1 correspondence, where, for corresponding
; termi, stacki, and termi', we have termi/stacki = termi'/stack.

; A correct answer is always delivered by the t clause below.  The other
; two clauses are just special cases.  One experiment with actual data
; suggests that the second special case below is almost always the one we
; see.  Out of 82514 calls of this function on actual data (TOS0-TEST),
; we saw 81380 calls of the form handled by that case!  The remaining
; cases were also pathological in some sense.

  (cond ((null (cdr terms))
         (mv terms (car stacks)))
        ((and (quotep (car terms))
              (all-equal (cadr stacks) (cddr stacks)))
         (mv terms (cadr stacks)))
        (t
         (mv-let (exts stack)
                 (reconcile-stacks terms stacks)
                 (mv (reconcile-terms terms exts) stack)))))

(defun with-reconciliation-let-bindings (terms var)
  (cond ((endp terms) nil)
        (t (cons (list (car terms) `(car ,var))
                 (with-reconciliation-let-bindings (cdr terms)
                                                   `(cdr ,var))))))

(defmacro with-reconciliation (terms stacks common-stack body)

; This macro allows us to write:

; (with-reconciliation (i j v s)
;                      (is js vs ss)
;                      stack
;                      <body>)

; and mean:

; (mv-let (temp stack)
;         (recon (list i j v s) (list is js vs ss))
;         (let ((i (car temp))
;               (j (cadr temp))
;               (v (caddr temp)) 
;               (s (cadddr temp)))
;           <body>))

; That is, we reconcile i/is, j/js, ..., to get new terms i, j, ... and a
; common stack stack, which we then do with as we please in the body.

  `(mv-let (with-reconciliation-temp ,common-stack)
           (recon (list ,@terms) (list ,@stacks))
           (let ,(with-reconciliation-let-bindings
                  terms
                  'with-reconciliation-temp)
             (check-vars-not-free (with-reconciliation-temp) ,body))))

; Now we develop a special-purpose rule applier.

(mutual-recursion

(defun lambda-stack-one-way-unify1 (pat term stack alist ens wrld ttree)

; Alist binds vars in pat to term1/stack1 pairs: (var . (term1
; . stack1)).  No Change Loser on alist and ttree.

  (cond
   ((variablep pat)
    (let ((trip (assoc-eq pat alist)))
      (cond
       (trip
        (cond
         ((eq (equal-derefs (cadr trip) (cddr trip) term stack) t)
          (mv t alist ttree))
         (t (mv nil alist ttree))))
       (t (mv t
              (cons (cons pat (cons term
                                    (if (quotep term) nil stack)))
                    alist)
              ttree)))))
   ((fquotep pat)
    (cond ((equal pat term) (mv t alist ttree))
          (t (mv nil alist ttree))))
   (t
    (mv-let (term stack ttree1)
            (cond ((variablep term)
                   (deref-var term stack ens wrld ttree))
                  ((flambda-applicationp term)
                   (deref term stack ens wrld ttree))
                  (t (mv term stack ttree)))
            (cond
             ((variablep term)
              (mv nil alist ttree))
             ((fquotep term)

; This case is handled far more elaborately in one-way-unify1.
; Suppose term is '5 and pat is (+ 1 ...).  Then in one-way-unify1 we
; recursively unify ... with 4.  But here we just fail.

              (mv nil alist ttree))
             ((eq (ffn-symb pat) (ffn-symb term))
              (mv-let (ans alist1 ttree1)
                      (lambda-stack-one-way-unify1-lst (fargs pat)
                                                       (fargs term)
                                                       stack alist
                                                       ens wrld ttree1)
                      (cond (ans (mv ans alist1 ttree1))
                            (t (mv nil alist ttree)))))
             (t (mv nil alist ttree)))))))

(defun lambda-stack-one-way-unify1-lst (pat-lst term-lst stack alist
                                                ens wrld ttree)

; Warning:  This function is NOT a no change loser!  When it fails,
; the returned alist and ttree might not be the original ones.

  (cond
   ((endp pat-lst) (mv t alist ttree))
   (t (mv-let (flg alist ttree)
              (lambda-stack-one-way-unify1 (car pat-lst)
                                           (car term-lst)
                                           stack alist ens wrld ttree)
              (cond
               (flg
                (lambda-stack-one-way-unify1-lst (cdr pat-lst)
                                                 (cdr term-lst)
                                                 stack alist ens wrld ttree))
               (t (mv nil alist ttree)))))))
)

(defun lambda-stack-one-way-unify (pat term stack ens wrld ttree)

; We one-way-unify pat with term/stack, returning (mv t alist stack' ttree')
; if we win and (mv nil nil nil ttree) otherwise.  When we win, alist is an
; alist pairing variables of pat with terms, each of which is to be
; interpreted under stack'.  That is, ((pat/alist)/stack') is
; term/stack.  The returned ttree is an extension of ttree if we win and
; is ttree if we lose.

; No change loser on ttree.

  (mv-let
   (ans alist ttree)
   (lambda-stack-one-way-unify1 pat term stack nil ens wrld ttree)
   (cond
    (ans
     (let ((vars (strip-cars alist))
           (terms (strip-cadrs alist))
           (stacks (strip-cddrs alist)))
       (mv-let (terms common-stack)
               (recon terms stacks)
               (mv t
                   (pairlis$ vars terms)
                   common-stack
                   ttree))))
    (t (mv nil nil nil ttree)))))
             
; Here is how we apply certain rewrite rules to term/stack.

(defun apply-abbrevs-to-lambda-stack1 (term stack ens wrld lemmas ttree)

; Term is known to be a function symbol application and lemmas are the
; rewrite lemmas for that symbol.  We apply the first enabled
; abbreviation lemma (with equiv EQUAL) to term/stack.  We restrict
; our attention to lemmas for which the variables on the rhs are a
; subset of those on the lhs.  The subset restriction prevents the
; introduction of an unbound variable into the lambda expressions
; implicit in term'/stack'.  We return (mv hitp term' stack' ttree'), where,
; if hitp is t, term/stack is equal to term'/stack' and ttree' is an
; extension of ttree.

  (cond
   ((endp lemmas) (mv nil term stack ttree))
   ((and (enabled-numep (access rewrite-rule (car lemmas) :nume) ens)
         (equal (access rewrite-rule (car lemmas) :equiv) 'equal)
         (eq (access rewrite-rule (car lemmas) :subclass) 'abbreviation)
         (subsetp-eq (all-vars (access rewrite-rule (car lemmas) :rhs))
                     (all-vars (access rewrite-rule (car lemmas) :lhs))))
    (mv-let (flg alist stack1 ttree)
            (lambda-stack-one-way-unify
             (access rewrite-rule (car lemmas) :lhs)
             term stack ens wrld ttree)
            (cond
             (flg
              #-acl2-loop-only ; Rockwell Addition
              (cond
               (*nth-update-tracingp*
                (cw "Abbrev: ~x0~%"
                    (access rewrite-rule (car lemmas) :rune))))
              (let ((term1
                     (sublis-var alist
                                 (access rewrite-rule (car lemmas) :rhs))))
                (mv t
                    term1
                    (if (quotep term1) nil stack1)
                    (push-lemma (access rewrite-rule (car lemmas) :rune)
                                ttree))))
             (t (apply-abbrevs-to-lambda-stack1 term stack ens wrld
                                                (cdr lemmas) ttree)))))
   (t (apply-abbrevs-to-lambda-stack1 term stack ens wrld
                                      (cdr lemmas) ttree))))

(defun apply-abbrevs-to-lambda-stack (hitp term stack ens wrld state ttree)

; We try to eval term/stack, if possible.  Otherwise, we apply abbrev
; rules.  If any rule hits, we repeat on the output of the rule.  We
; return (mv hitp' term' stack' ttree'), where term/stack is equal to
; term'/stack' and hitp' is t if either hitp is t initially or we did
; something.  Ttree' is an extension of ttree.

  (cond
   ((or (variablep term)
        (fquotep term)
        (flambda-applicationp term))
    (mv hitp term stack ttree))

; I once added this because we see expt's a lot.  But I only gained one second
; out of 100, and it means expt can't be disabled.  So I don't think this is
; worth it.

;  ((and (eq (ffn-symb term) 'expt)
;        (quotep (fargn term 1))
;        (quotep (fargn term 2)))
;   (mv t
;       (kwote (expt (fix (cadr (fargn term 1))) (nfix (cadr (fargn term 2)))))
;       nil
;       ttree))

   ((and (null stack)
         (logicalp (ffn-symb term) wrld)
         (all-quoteps (fargs term))
         (enabled-xfnp (ffn-symb term) ens wrld)

; We don't mind disallowing constrained functions that have attachments,
; because the call of ev-fncall below disallows the use of attachments (last
; parameter, aok, is nil).

         (not (getprop (ffn-symb term) 'constrainedp nil
                       'current-acl2-world wrld)))
    (mv-let
     (erp val latches)
     (pstk
      (ev-fncall (ffn-symb term)
                 (strip-cadrs (fargs term))
                 state
                 nil
                 t
                 nil))
     (declare (ignore latches))
     (cond
      (erp
       (mv-let
        (hitp1 term1 stack1 ttree)
        (apply-abbrevs-to-lambda-stack1
         term stack ens wrld
         (getprop (ffn-symb term) 'lemmas nil 'current-acl2-world wrld)
         ttree)
        (cond
         (hitp1
          (apply-abbrevs-to-lambda-stack t term1 stack1 ens wrld state ttree))
         (t (mv hitp term stack ttree)))))
      (t #-acl2-loop-only ; Rockwell Addition         
         (cond (*nth-update-tracingp*
                (cw "Eval: ~x0~%" term)))
         (mv t (kwote val) nil
             (push-lemma (fn-rune-nume (ffn-symb term)
                                       nil t wrld)
                         ttree))))))
   (t (mv-let
       (hitp1 term1 stack1 ttree)
       (apply-abbrevs-to-lambda-stack1
        term stack ens wrld
        (getprop (ffn-symb term) 'lemmas nil 'current-acl2-world wrld)
        ttree)
       (cond
        (hitp1
         (apply-abbrevs-to-lambda-stack t term1 stack1 ens wrld state ttree))
        ((eq (ffn-symb term) 'equal)
         (let ((p (equal-derefs (fargn term 1) stack
                                (fargn term 2) stack)))
           (cond
            ((eq p '?) (mv hitp term stack ttree))
            (p (mv t *t* nil ttree))
            (t (mv t *nil* nil ttree)))))
        (t (mv hitp term stack ttree)))))))

; We create a fake rune (see the Essay on Fake-Runes) for the
; nu-rewriter.  This allows us to record that something was done.  It
; would probably be sufficient to add (:rewrite nth-update-nth) or
; (:rewrite nth-update-nth-array) to the ttree, as appropriate, to
; report a hit.  But what if one of those runes is disabled?  We did
; not want to use a disabled rune.  And we did not want to give the
; user three ways to shut off the nu-rewriter (by using the
; nu-rewriter-mode or disabling one of those runes).  So we use this
; fake rune instead and simply don't are whether the nth-update-nth
; runes are enabled or not.  It is as though this were a metafunction
; justified by the existence of those runes but independent of them in
; application.

(defconst *fake-rune-for-nu-rewriter*
  '(:FAKE-RUNE-FOR-NU-REWRITER nil))

; And here is the special-purpose rewriter itself.

(mutual-recursion

(defun nth-update-rewriter1-continue
  (recursivelyp term stack flg1 term1 stack1 ttree1 try-abbrevsp
                ens wrld state memo-alist)

; This function is used to memoize the fact that on the argument
; triple (recursivelyp, term, stack) nth-update-rewriter1 returned
; (flg1, term1, stack1, ttree1) -- EXCEPT that we continue to simplify by
; applying abbreviations to term1/stack1 -- which also evaluates
; ground function applications -- and recursively calling
; nth-update-rewriter1 on the result.  We actually memoize the final
; result, not the intermediate one.

  (cond
   (try-abbrevsp
    (mv-let
     (flg2 term2 stack2 ttree2)
     (apply-abbrevs-to-lambda-stack nil term1 stack1 ens wrld state ttree1)
     (cond
      (flg2
;      (format t "Abbreves hit!~%")
       (mv-let
        (flg3 term3 stack3 ttree3 memo-alist)
        (nth-update-rewriter1 recursivelyp term2 stack2
                              ens wrld state memo-alist)
        (declare (ignore flg3))
        (memo-exit recursivelyp term stack
                   t term3 stack3 (cons-tag-trees ttree2 ttree3) memo-alist)))
      (t 

; If we were told to try abbrevs and none fired, then we are done.  We
; assume that the input has already had nth-update-rewriter1 applied
; to it, if we're trying abbrevs.  To do otherwise is risk a loop.

       (memo-exit recursivelyp term stack
                  flg1
                  term1
                  stack1
                  ttree1
                  memo-alist)))))
   (flg1

; We're not trying abbrevs and the original input changed from term to
; term1.  So try again.

    (mv-let
     (flg3 term3 stack3 ttree3 memo-alist)
     (nth-update-rewriter1 recursivelyp term1 stack1
                           ens wrld state memo-alist)
     (declare (ignore flg3))
     (memo-exit recursivelyp term stack
                t term3 stack3 (cons-tag-trees ttree1 ttree3) memo-alist)))
   (t (memo-exit recursivelyp term stack
                 nil
                 term1
                 stack1
                 ttree1
                 memo-alist))))

(defun nth-update-rewriter1
   (recursivelyp term stack ens wrld state memo-alist)

; We return (mv flg term' stack' ttree) where
; (1) (EQUAL term/stack term'/stack)
; (2) term' is a quote, if possible
; (3) flg is T iff we applied NTH-UPDATE-NTH or NTH-UPDATE-NTH-ARRAY
;     to some part of term', and
; (4) ttree lists all the rules we used.

; Warning: We might change term to a quote by lookup in stack, without
; applying a rule.  Hence flg = nil does NOT mean that term = term'.

; Stack is a stack of frames.  Each frame is a pair of the form
; (vars . actuals).  We determine whether

; (equal (nth i (update-nth j v s))                     ; lhs
;        (if (equal (nfix i) (nfix j)) v (nth i s)))    ; rhs

; applies to term/stack.  If so, we return (mv t new-term new-stack)
; such that new-term/new-stack is equal to term/stack.  Else,
; we return (mv nil term stack).  That is, no matter what, we
; return a term and stack equal to the original one.

; This function also deals with (nth i (update-nth-array ...))
; in a similar fashion.

; Nomenclature.  The patterns shown below indicate the names we will
; use for the various parts of term/stack.  We look at term through
; the lens of the stack, without applying the full substitution to it.
; We initially try to see it as

; (NTH i r)

; and then, by dereferencing r, as

; (NTH i (UPDATE-NTH j v s)),

; where each piece is represented by a term and a stack.  Thus we
; have

; term/stack = (NTH i/is (UPDATE-NTH j/js v/vs s/ss))

; Now, if term was bound in stack then term1 is now its ultimate
; binding.  Of course, term/stack is equal to term1/stack1.

   (mv-let
    (xx1 xx2 xx3 xx4 xx5)
    (get-memo recursivelyp term stack memo-alist)

    (cond
     (xx1
      (mv xx2 xx3 xx4 xx5 memo-alist))
     (t
      (mv-let
       (term1 stack1 ttree1)
       (deref term stack ens wrld nil)

       (cond
        ((variablep term1)

; If term1 is a variable, then stack1 is nil.

         (mv nil term1 nil ttree1 memo-alist))

        ((fquotep term1)
         (mv nil term1 nil ttree1 memo-alist))

; We used to have the following code.  But it blocked a (at least one)
; proof in the fp books (LOGAND-DEF).  So I eliminated it.  But it was
; added for a reason.  Other changes we're now running seem to have
; rendered that reason no longer relevant...  This deleted code does not
; track ttrees, so if it is reinstated the ttree issues will have to be
; thought out.

;;;     ((and (nvariablep term)
;;;           (flambdap (ffn-symb term))
;;;           (eq (ffn-symb term1) 'IF)
;;;           stack1)
;;;
;;; ; If the ORIGINAL term, the one we deref'd above, is a LAMBDA that contains
;;; ; an IF at the top of its body, we lift the IF out of the LAMBDA.
;;;
;;;      (mv-let
;;;       (aflg a as memo-alist)
;;;       (nth-update-rewriter1 recursivelyp? ; When this was done, I didn't
;;;                                           ; have the recursivelyp flag.
;;;                             (fargn term1 1) stack1
;;;                             ens wrld state memo-alist)
;;;       (declare (ignore aflg))
;;;       (mv t `(IF ,(lambda-stack as a)
;;;                  ,(lambda-stack stack1 (fargn term1 2))
;;;                  ,(lambda-stack stack1 (fargn term1 3)))
;;;           nil
;;;           memo-alist)))

        ((not (eq (ffn-symb term1) 'nth))

; So term/stack isn't an (nth ...).  We can't do anything with it, unless we
; are doing this recursively or else an abbreviation lemma clears the way.

         (cond
          ((or (not recursivelyp)
               (eq (ffn-symb term1) 'hide))
           (nth-update-rewriter1-continue recursivelyp term stack
                                          nil term1 stack1 ttree1
                                          t ens wrld state memo-alist))

; In the next two clauses we know that recursivelyp is t.

          ((eq (ffn-symb term1) 'IF)
           (mv-let
            (aflg a as attree memo-alist)
            (nth-update-rewriter1 t (fargn term1 1) stack1
                                  ens wrld state memo-alist)

; On this IF we use the ``abc'' approach: simplify the test first and
; then the two branches.  But on (NTH i (IF a b c)) we use the ``bca''
; approach of working first on (NTH i b) and (NTH i c) in hopes that
; they come out equal.  We tried the bca approach on this IF and tried
; it on one of the standard Rockwell problems and it gave marginally worse
; performance than the abc approach.

            (cond
             ((quotep a)
              (cond
               ((equal a *nil*)
                (nth-update-rewriter1-continue
                 recursivelyp term stack
                 t (fargn term1 3) stack1 (cons-tag-trees ttree1 attree)
                 nil ens wrld state memo-alist))
               (t (nth-update-rewriter1-continue
                   recursivelyp term stack
                   t (fargn term1 2) stack1 (cons-tag-trees ttree1 attree)
                   nil ens wrld state memo-alist))))
             (t (mv-let
                 (bflg b bs bttree memo-alist)
                 (nth-update-rewriter1 t (fargn term1 2) stack1
                                       ens wrld state
                                       memo-alist)
                 (mv-let
                  (cflg c cs cttree memo-alist)
                  (nth-update-rewriter1 t (fargn term1 3) stack1
                                        ens wrld state
                                        memo-alist)
                  (cond
                   ((eq (equal-derefs b bs c cs) t)
                    (memo-exit t term stack t b bs
                               (cons-tag-trees bttree cttree) memo-alist))
                   (t (with-reconciliation
                       (a b c)
                       (as bs cs)
                       common-stack

; There are no abbrev rules on IF and a, at least, is not quoted so
; we cannot evaluate the IF below.  Thus, we're done.

                       (memo-exit t term stack
                                  (or aflg bflg cflg)
                                  `(IF ,a ,b ,c)
                                  common-stack
                                  (cons-tag-trees attree
                                                  (cons-tag-trees bttree
                                                                  cttree))
                                  memo-alist))))))))))
          (t (mv-let
              (aflg args astacks attree memo-alist)
              (nth-update-rewriter1-lst t (fargs term1) stack1
                                        ens wrld state memo-alist)
              (cond
               (aflg
                (mv-let
                 (args astack)
                 (recon args astacks)
                 (let ((aterm (cons-term (ffn-symb term1) args)))
                   (nth-update-rewriter1-continue
                    recursivelyp term stack
                    t aterm astack (cons-tag-trees ttree1 attree)
                    t ens wrld state memo-alist))))
               (t (nth-update-rewriter1-continue
                   t term stack nil term1 stack1 ttree1
                   t ens wrld state memo-alist)))))))
        (t

; We start by rewriting the first argument to the nth expression.
; It is not unheard-of for this argument to be an nth expression
; itself.  That is, we might be looking at (nth (nth & &) &).

         (mv-let
          (iflg i is ittree memo-alist)
          (nth-update-rewriter1 t (fargn term1 1) stack1
                                ens wrld state memo-alist)
          (mv-let
           (r rs irttree)  ; includes ittree!
           (deref (fargn term1 2) stack1 ens wrld ittree)
           (cond
            ((or (variablep r)
                 (fquotep r))

; So we are looking at an expression like (NTH i r), where r is a variable
; or a quoted constant.

             (with-reconciliation
              (i r)
              (is rs)
              common-stack
              (nth-update-rewriter1-continue
               recursivelyp term stack
               iflg `(NTH ,i ,r) common-stack irttree
               t ens wrld state memo-alist)))
            ((eq (ffn-symb r) 'IF)

; We are looking at (NTH i (IF a b c)).  We turn it into (IF a (NTH i
; b) (NTH i c)), provided at least one of the branches simplifies or
; we can decide the test.  The code below may duplicate i!

             (let* ((a (fargn r 1))
                    (as (if (quotep a) nil rs))
                    (b (fargn r 2))
                    (bs (if (quotep b) nil rs))
                    (c (fargn r 3))
                    (cs (if (quotep c) nil rs)))
               (with-reconciliation
                (i b) (is bs) inner-bs
                (mv-let
                 (xflg x xs xttree memo-alist)
                 (nth-update-rewriter1 t `(NTH ,i ,b) inner-bs
                                       ens wrld state memo-alist)
                 (with-reconciliation
                  (i c) (is cs) inner-cs
                  (mv-let
                   (yflg y ys yttree memo-alist)
                   (nth-update-rewriter1 t `(NTH ,i ,c) inner-cs
                                         ens wrld state memo-alist)
                   (cond
                    ((or xflg yflg)

; Equal-derefs is not perfect; it sometimes says nil when the two
; derefs are recursively equal.  We tried the fully recursive,
; complete equal-derefs and found it too slow.  We also tried
; reconciling a, x and y and then asking whether x is y, but found
; that slower than this.

                     (cond
                      ((eq (equal-derefs x xs y ys) t)
                       (memo-exit recursivelyp term stack
                                  t x xs
                                  (cons-tag-trees irttree
                                                  (cons-tag-trees xttree
                                                                  yttree))
                                  memo-alist))
                      (t
                       (mv-let
                        (aflg a as attree memo-alist)
                        (nth-update-rewriter1 t a as
                                              ens wrld state memo-alist)
                        (declare (ignore aflg))
                        (cond
                         ((quotep a)
                          (cond
                           ((equal a *nil*)
                            (memo-exit recursivelyp term stack t y ys
                                       (cons-tag-trees irttree
                                                       (cons-tag-trees attree
                                                                       yttree))
                                       memo-alist))
                           (t
                            (memo-exit recursivelyp term stack t x xs
                                       (cons-tag-trees irttree
                                                       (cons-tag-trees attree
                                                                       xttree))
                                       memo-alist))))
                         (t
                          (with-reconciliation
                           (a x y) (as xs ys) common-stack
; There are no abbrev rules on IF and a, at least, is not a constant, so
; we can't eval the IF below.  We're done.

                           (memo-exit recursivelyp term stack
                                      t `(IF ,a ,x ,y) common-stack
                                      (cons-tag-trees
                                       irttree
                                       (cons-tag-trees
                                        attree
                                        (cons-tag-trees xttree
                                                        yttree)))
                                      memo-alist))))))))
                    ((null iflg)

; If iflg is off, we haven't changed term/stack at all and avoid the
; reconciliation otherwise necessary.

                     (nth-update-rewriter1-continue
                      recursivelyp term stack
                      nil term stack nil
                      t ens wrld state memo-alist))
                    (t (with-reconciliation
                        (i r) (is rs) common-stack
                        (nth-update-rewriter1-continue
                         recursivelyp term stack
                         t `(NTH ,i ,r) common-stack irttree
                         t ens wrld state memo-alist))))))))))
            ((eq (ffn-symb r) 'UPDATE-NTH)

; We are looking at (NTH i (UPDATE-NTH j v s)).

             (mv-let
              (jflg j js jttree memo-alist)
              (nth-update-rewriter1 t (fargn r 1) rs
                                    ens wrld state memo-alist)
              (declare (ignore jflg))
              (let* ((i (if (quotep i) (nfix-quote i) i))
                     (j (if (quotep j) (nfix-quote j) j))
                     (irjttree (push-lemma *fake-rune-for-nu-rewriter*
                                           (cons-tag-trees irttree jttree)))
                     (i=j (equal-derefs i is j js))
                     (v (fargn r 2))
                     (vs (if (quotep v) nil rs))
                     (s (fargn r 3))
                     (ss (if (quotep s) nil rs)))
                (cond
                 ((eq i=j '?)
                  (with-reconciliation
                   (i j) (is js) ps
                   (let ((nfixi (if (quotep i) i `(NFIX ,i)))
                         (nfixj (if (quotep j) j `(NFIX ,j))))
                     (mv-let
                      (pflg p ps pttree)
                      (apply-abbrevs-to-lambda-stack nil
                                                     `(EQUAL ,nfixi ,nfixj)
                                                     ps ens wrld state
                                                     irjttree)
                      (declare (ignore pflg))
                      (cond
                       ((quotep p)
                        (cond
                         ((equal p *nil*)
                          (with-reconciliation
                           (i s) (is ss) common-stack
                           (nth-update-rewriter1-continue
                            recursivelyp term stack
                            t
                            `(NTH ,i ,s)
                            common-stack
                            pttree
                            nil ens wrld state memo-alist)))
                         (t
                          (nth-update-rewriter1-continue
                           recursivelyp term stack
                           t v vs pttree
                           nil ens wrld state memo-alist))))
                       (t
                        (with-reconciliation
                         (p i v s) (ps is vs ss) common-stack
                         (nth-update-rewriter1-continue
                          recursivelyp term stack
                          t
                          `(IF ,p
                               ,v
                               (NTH ,i ,s))
                          common-stack
                          pttree
                          nil ens wrld state memo-alist))))))))
                 ((eq i=j t)
                  (nth-update-rewriter1-continue
                   recursivelyp term stack
                   t v vs
                   irjttree
                   nil ens wrld state memo-alist))
                 (t
                  (with-reconciliation
                   (i s) (is ss) common-stack
                   (nth-update-rewriter1-continue
                    recursivelyp term stack
                    t `(NTH ,i ,s) common-stack 
                    irjttree
                    nil ens wrld state memo-alist)))))))
            ((eq (ffn-symb r) 'UPDATE-NTH-ARRAY)

; We are looking at (NTH i (UPDATE-NTH-ARRAY j k v s)).
; The operative rule is
; (equal (NTH i (UPDATE-NTH-ARRAY j k v s))
;        (if (equal (nfix i) (nfix j))
;            (update-nth k v (nth i s))
;          (nth i s))))

             (mv-let
              (jflg j js jttree memo-alist)
              (nth-update-rewriter1 t (fargn r 1) rs
                                    ens wrld state memo-alist)
              (declare (ignore jflg))
              (let* ((i (if (quotep i) (nfix-quote i) i))
                     (j (if (quotep j) (nfix-quote j) j))
                     (irjttree (push-lemma *fake-rune-for-nu-rewriter*
                                           (cons-tag-trees irttree jttree)))
                     (i=j (equal-derefs i is j js))
                     (k (fargn r 2))
                     (ks (if (quotep k) nil rs))
                     (v (fargn r 3))
                     (vs (if (quotep v) nil rs))
                     (s (fargn r 4))
                     (ss (if (quotep s) nil rs)))
                (cond
                 ((eq i=j '?)
                  (with-reconciliation
                   (i j) (is js) ps
                   (let ((nfixi (if (quotep i) i `(NFIX ,i)))
                         (nfixj (if (quotep j) j `(NFIX ,j))))
                     (mv-let
                      (pflg p ps pttree)
                      (apply-abbrevs-to-lambda-stack nil
                                                     `(EQUAL ,nfixi ,nfixj)
                                                     ps ens wrld state
                                                     irjttree)
                      (declare (ignore pflg))
                      (cond
                       ((quotep p)
                        (cond
                         ((equal p *nil*)
                          (with-reconciliation
                           (i s) (is ss) common-stack
                           (nth-update-rewriter1-continue
                            recursivelyp term stack
                            t
                            `(NTH ,i ,s)
                            common-stack pttree
                            nil ens wrld state memo-alist)))
                         (t
                          (with-reconciliation
                           (i k v s) (is ks vs ss) common-stack
                           (nth-update-rewriter1-continue
                            recursivelyp term stack
                            t
                            `(UPDATE-NTH ,k ,v (NTH ,i ,s))
                            common-stack pttree
                            nil ens wrld state memo-alist)))))
                       (t
                        (with-reconciliation
                         (p i k v s) (ps is ks vs ss) common-stack
                         (nth-update-rewriter1-continue
                          recursivelyp term stack
                          t
                          `(IF ,p
                               (UPDATE-NTH ,k ,v (NTH ,i ,s))
                               (NTH ,i ,s))
                          common-stack pttree
                          nil ens wrld state memo-alist))))))))
                 ((eq i=j t)
                  (with-reconciliation
                   (i k v s) (is ks vs ss) common-stack
                   (nth-update-rewriter1-continue
                    recursivelyp term stack
                    t `(UPDATE-NTH ,k ,v (NTH ,i ,s)) common-stack irjttree
                    nil ens wrld state memo-alist)))
                 (t
                  (with-reconciliation
                   (i s) (is ss) common-stack
                   (nth-update-rewriter1-continue
                    recursivelyp term stack
                    t
                    `(NTH ,i ,s) common-stack irjttree
                    nil ens wrld state memo-alist)))))))
            ((eq (ffn-symb r) 'NTH)

; We are looking at (NTH i (NTH ...)).  We first simplify the inner
; NTH.  It could simplify to an UPDATE-NTH.  So after rewriting it we
; recur.

             (mv-let
              (rflg1 r1 r1s rttree memo-alist)
              (nth-update-rewriter1 t r rs
                                    ens wrld state memo-alist)

              (cond
               (rflg1
                (with-reconciliation
                 (i r1)
                 (is r1s)
                 common-stack
                 (nth-update-rewriter1-continue
                  recursivelyp term stack
                  t `(NTH ,i ,r1) common-stack
                  (cons-tag-trees irttree rttree)
                  nil ens wrld state memo-alist)))
               (t

; We are looking at (NTH i (NTH ...)) but we couldn't simplify the inner
; NTH.  So we behave just as we do in the clause below, when r isn't
; even an NTH.

                (cond
                 ((null iflg)
                  (nth-update-rewriter1-continue
                   recursivelyp term stack
                   nil term stack nil
                   t ens wrld state memo-alist))
                 (t (with-reconciliation
                     (i r) (is rs) common-stack
                     (nth-update-rewriter1-continue
                      recursivelyp term stack
                      t `(NTH ,i ,r) common-stack
                      (cons-tag-trees irttree rttree)
                      t ens wrld state memo-alist))))))))
            ((and (eq (ffn-symb r) 'CONS)
                  (quotep i)
                  (integerp (cadr i))
                  (<= 0 (cadr i))
                  (mv-let (un temp-alist)
                          (simplifiable-mv-nth1 (cadr i) r nil)
                          (declare (ignore temp-alist))
                          un))

; We are looking at (NTH 'n (CONS u0 (CONS u1 ... (CONS un ...)...)))
; where r is the cons nest and we know there there are enough
; elements.  The code above is a little strange because of its use of
; simplifiable-mv-nth1.  That function actually has nothing to do with
; MV-NTH and just asks whether its second arg is a cons-term of
; sufficient depth, as given by its first arg.  The last arg is an
; alist for use in chasing variables that occur in the cons-term.  We
; supply nil, which means we insist that r be a suitable cons-term at
; the ``top-level'' of its structure.  We ignore the returned alist
; because it is nil.

             (mv-let (un temp-alist)
                     (simplifiable-mv-nth1 (cadr i) r nil)
                     (declare (ignore temp-alist))
                     (nth-update-rewriter1-continue
                      recursivelyp term stack
                      t un rs irttree t ens wrld state memo-alist)))
            (t

; We are looking at (NTH i r), where r is a function or lambda
; application but not an IF, UPDATE-NTH or UPDATE-NTH-ARRAY.

             (cond
              ((null iflg)
               (nth-update-rewriter1-continue
                recursivelyp term stack
                nil term stack nil
                t ens wrld state memo-alist))
              (t (with-reconciliation
                  (i r) (is rs) common-stack
                  (nth-update-rewriter1-continue
                   recursivelyp term stack
                   t `(NTH ,i ,r) common-stack irttree
                   t ens wrld state memo-alist)))))))))))))))

(defun nth-update-rewriter1-lst (recursivelyp args stack
                                              ens wrld state memo-alist)
  (cond
   ((endp args)
    (mv nil nil nil nil memo-alist))
   (t (mv-let (aflg1 arg1 astack1 attree1 memo-alist)
              (nth-update-rewriter1 recursivelyp (car args) stack
                                    ens wrld state memo-alist)
              (mv-let (aflg2 args1 astacks1 attree2 memo-alist)
                      (nth-update-rewriter1-lst recursivelyp (cdr args) stack
                                                ens wrld state memo-alist)
                      (mv (or (or aflg1
                                  (and (not (quotep (car args)))
                                       (quotep arg1)))
                              aflg2)
                          (cons arg1 args1)
                          (cons astack1 astacks1)
                          (cons-tag-trees attree1 attree2)
                          memo-alist))))))
)

(mutual-recursion

(defun nth-update-rewriter-targetp (term wrld)

; We determine whether the function NTH is used as a function in term
; or in the body of any non-recursive fn used in term.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (nth-update-rewriter-targetp (lambda-body (ffn-symb term)) wrld)
             (nth-update-rewriter-target-lstp (fargs term) wrld)))
        (t (or (getprop (ffn-symb term) 'nth-update-rewriter-targetp nil
                        'current-acl2-world wrld)
               (nth-update-rewriter-target-lstp (fargs term) wrld)))))

(defun nth-update-rewriter-target-lstp (lst wrld)
  (declare (xargs :guard (pseudo-term-listp lst)))
  (if (null lst)
      nil
    (or (nth-update-rewriter-targetp (car lst) wrld)
        (nth-update-rewriter-target-lstp (cdr lst) wrld))))

)

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

(defun nth-update-rewriter (recursivep term alist ens wrld state)

; Term is a function or lambda application.  This function may rewrite
; term/alist and returns (mv hitp term' ttree), where either hitp is nil (in
; which case term' is irrelevant) or term' is equal to term/alist and ttree
; justifies the equivalence.

; Note: Consistent with the conventions inside the rewriter, alist may
; not bind every variable of term.  That is, we might see the term (fn
; x y) and an alist that binds x to a but does not mention y.

; This function applies two rules, looking for the two targets:
;  (nth i (update-nth j v s))
; and
;  (nth i (update-nth-array j k v s))
; and rewriting in the obvious way.  But it looks through IFs and LAMBDAs
; and proceeds in an outside-in manner.

; If recursivep is t, we explore term/alist to the tips.  If
; recursivep is nil, we only proceed if term/alist is an NTH
; expression.  However, term/alist is an NTH expression either because
; term is an NTH expression or because term is a variable bound to an
; NTH expression in alist.  But term is not a variable.

  (cond
   ((not (nu-rewriter-mode wrld)) (mv nil nil nil))
   ((not (if recursivep
             (nth-update-rewriter-targetp term wrld)
           (eq (ffn-symb term) 'NTH)))

; This exit is always sound.  The idea of the test above is this: If
; we are to explore the term recursively and it does not contain any
; targets, then we don't bother.  Alternatively, if we are not to
; explore it recursively and it is not an NTH expression, we don't
; bother.  We look at term rather than term/alist because everything
; in alist has been simplified already, so if we do work it will be
; because of stuff in term.

; Tests have shown that it is worth the cost of looking for targets
; before proceeding.  This is because we call this function with
; recursivep = t more often than we might (namely, on every rewrite
; during backchaining and recursive function expansion, and whenever
; the arguments to a non-rec fn application change when rewritten).
; If these calls are changed to recursivep = nil, then things speed up
; by not looking ahead for targets.  But suppose that an argument, a,
; has changed from (compute st) to some huge expression, expr, and the
; term being rewritten is (if (test a) (nth 1 a) (nth 1 st)), and
; suppose that we can tell that (nth 1 expr) is (nth 1 a) by
; nth-update reasoning.  Then we would win bigtime.  Therefore, I
; believe it is important to use recursivep = t agressively when it
; might help.

    (mv nil nil nil))
   (t
    #-acl2-loop-only ; Rockwell Addition
    (cond
     (*nth-update-tracingp*
      (cw "(nth-update-rewriter:~%~
           ~ recp:  ~x0~%~
           ~ term:  ~x1~%~
           ~ alist: ~x2~%~
           ~ (..."
          recursivep
          (untranslate term nil wrld)
          alist)))

    #-acl2-loop-only ; Rockwell Addition
    (clear-nu-memos nil ens wrld)
           
    (mv-let (flg term1 stack1 ttree1 memo-alist)

; Rockwell Addition:  Non-equivalent read conditionals!  Well, they
; may be equivalent if you take the view that TIME's output is to the
; comment window.  This could be done in straight ACL2.

            #-acl2-loop-only ; Rockwell Addition
            (cond
             (*nth-update-tracingp*
              (time
               (nth-update-rewriter1 recursivep
                                     term
                                     (make-stack-from-alist term alist)
                                     ens wrld state nil)))
             (t (nth-update-rewriter1 recursivep
                                      term
                                      (make-stack-from-alist term alist)
                                      ens wrld state nil)))
            #+acl2-loop-only ; Rockwell Addition
            (nth-update-rewriter1 recursivep
                                  term
                                  (make-stack-from-alist term alist)
                                  ens wrld state nil)
            (declare (ignore memo-alist))
            #-acl2-loop-only ; Rockwell Addition
            (cond
             (*nth-update-tracingp*
              (cw "...)~%")
              (nu-memo-stats)))
            
            (cond
             ((null flg)
              #-acl2-loop-only ; Rockwell Addition
              (cond
               (*nth-update-tracingp*
                (cw " output: no change)~%")))
              (mv nil nil nil))
             (t (let ((ans (lambda-stack stack1 term1)))
                  #-acl2-loop-only ; Rockwell Addition
                  (cond
                   (*nth-update-tracingp*
                    (cw " output: ~x0)~%"
                        (untranslate ans nil wrld))))
                  (mv t ans ttree1))))))))

; Here is how we create a lambda application.

(defun collect-by-position (sub-domain full-domain full-range)

; Full-domain and full-range are lists of the same length, where
; full-domain is a list of symbols.  Collect into a list those members
; of full-range that correspond (positionally) to members of
; full-domain that belong to sub-domain.

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

; Example:
; (make-lambda-application '(x y z)
;                          '(foo x z)
;                          '((x1 a b) (y1 a b) (z1 a b)))
; equals
; ((lambda (x z) (foo x z)) (x1 a b) (z1 a b))
;
; Note that the irrelevant formal y has been eliminated.

  (let ((vars (all-vars body)))
    (cond
     ((null vars)
      body)
     ((equal formals actuals)
      body)
     ((set-difference-eq vars formals)
      (er hard 'make-lambda-application
          "Unexpected unbound vars ~x0"
          (set-difference-eq vars formals)))
     (t

; The slightly tricky thing here is to avoid using all the formals,
; since some might be irrelevant.  Note that the call of
; intersection-eq below is necessary rather than just using vars, even
; though it is a no-op when viewed as a set operation (as opposed to a
; list operation), in order to preserve the order of the formals.

      (fcons-term (make-lambda (intersection-eq formals vars) body)
                  (collect-by-position vars formals actuals))))))

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

(defabbrev memo-activep (memo)
  (or (eq memo :start) (consp memo)))

(defabbrev activate-memo (memo)
  (if (eq memo t) :start memo))

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
                      ACL2 preprocessor (a sort of rewriter).  There is ~
                      probably a loop caused by some set of enabled simple ~
                      rules.  To see why the limit was exceeded, ~@1retry the ~
                      proof with :hints~%  :do-not '(preprocess)~%and then ~
                      follow the directions in the resulting error message.  ~
                      See :DOC rewrite-stack-limit."
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
                    try (cw-gstack :frames 30).  You will then probably ~
                    notice a loop caused by some set of enabled rules, some ~
                    of which you can then disable; see :DOC disable.  Also ~
                    see :DOC rewrite-stack-limit."
                   (rewrite-stack-limit wrld)
                   (if (f-get-global 'gstackp state)
                       ""
                     "first execute~%  :brr ~
                      t~%and then try the proof again, and then "))
               ,form))))

(defun bad-synp-hyp-msg1 (hyp bound-vars all-vars-bound-p wrld)

; A hyp is a "good synp hyp" if either it does not mention SYNP as a function
; symbol or else it is a call of SYNP that we know how to handle in our
; processing of rewrite and linear rules.  We return nil in this case, or else
; an appropriate message explaining the problem.  See bad-synp-hyp-msg.

  (if (ffnnamep 'synp hyp)
      (cond ((not (eq (ffn-symb hyp) 'synp))
             (mv (cons
                  "a call of syntaxp or bind-free can occur only ~
                   at the top level of a hypothesis, but in ~x0 it ~
                   appears elsewhere."
                  (list (cons #\0 (untranslate hyp t wrld))))
                 bound-vars all-vars-bound-p))

; Note that we check for the well-formedness of a call to synp in
; translate, so the following bindings should be safe.

            (t
             (let* ((term-to-be-evaluated (get-evg (fargn hyp 3)
                                                   'bad-synp-hyp-msg1-arg3))
                    (vars (all-vars term-to-be-evaluated))
                    (saved-term (get-evg (fargn hyp 2)
                                         'bad-synp-hyp-msg1-arg2))
                    (vars-to-be-bound (get-evg (fargn hyp 1)
                                               'bad-synp-hyp-msg1-arg1)))
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
                                           bound-vars))))
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
                                 (cons #\1 bound-vars)
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
                                                    bound-vars))))
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
                                                    bound-vars))))
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
; or chk-acceptable-linear-rule2, or in rewrite-with-lemma.

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

(defun relieve-hyp-synp (rune hyp0 unify-subst rdepth type-alist wrld state
                              fnstack ancestors backchain-limit
                              simplify-clause-pot-lst rcnst gstack ttree bkptr)

; Hyp0 is a call of synp.  This special case of relieve-hyp returns some of the
; same values as does relieve-hyp, namely:

; (mv wonp failure-reason unify-subst' ttree''),

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
                        :ttree ttree)
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
             ((bad-synp-alist val unify-subst (fargn hyp0 1) wrld)
              (mv (er hard 'relieve-hyp
                      "The evaluation of the BIND-FREE form in hypothesis ~p0 ~
                       of rule ~x1 produced the result ~x2, which is illegal ~
                       because ~@3."
                      (untranslate hyp0 t wrld)
                      rune
                      val
                      (bad-synp-alist val unify-subst (fargn hyp0 1) wrld))
                  nil unify-subst ttree))
             (t
              (mv t nil 

; We attempt to keep all terms in quote-normal form, which explains the
; modification of val just below.

                  (append (pairlis$ (strip-cars val)
                                    (sublis-var-lst nil (strip-cdrs val)))
                          unify-subst)

; See comment for call of push-lemma above, for why we do not include the
; executable-counterparts of functions in the term just evaluated.

                  (push-lemma (fn-rune-nume 'synp nil nil wrld) ttree)))))))

(defmacro recursivep (fn wrld)

; Experiments show a slight speedup in Allegro CL (perhaps a half percent on a
; very small run) if we make this a macro.

  `(access def-body
          (def-body ,fn ,wrld)
          :recursivep))

(defun push-lemma? (rune ttree)
  (if rune
      (push-lemma rune ttree)
    ttree))

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
; a free variable without using bind-free or being a binding hypothesis;
; otherwise, we are in the normal-failure case.

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
; whose left-hand side has variables x1 and x2, such that hypthesis 2 binds
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
; symbol-<.  The value of each key is a sorted-rw-cache-list.  We return a
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
        ((symbol-< (caar alist1) (caar alist2))
         (mv-let (flg rest)
                 (merge-rw-caches (cdr alist1) alist2)
                 (declare (ignore flg))
                 (mv nil (cons (car alist1) rest))))
        (t ; (symbol-< (caar alist2) (caar alist1))
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
        ((symbol-< (caar a1) (caar a2))
         (cons (car a1)
               (merge-symbol-alistp (cdr a1) a2)))
        (t
         (cons (car a2)
               (merge-symbol-alistp a1 (cdr a2))))))

(defun merge-sort-symbol-alistp (alist)
  (cond ((endp (cdr alist)) alist)
        ((endp (cddr alist))
         (cond ((symbol-< (car (car alist)) (car (cadr alist)))
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
; mod-completion in distributed book arithmetic-2/floor-mod/floor-mod.lisp
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

(mutual-recursion

(defun dumb-occur-var (var term)

; This function determines if variable var occurs in the given term.  This is
; the same as dumb-occur, but optimized for the case that var is a variable.

  (cond ((eq var term) t)
        ((variablep term) nil)
        ((fquotep term) nil)
        (t (dumb-occur-var-lst var (fargs term)))))

(defun dumb-occur-var-lst (var lst)
  (cond ((null lst) nil)
        (t (or (dumb-occur-var var (car lst))
               (dumb-occur-var-lst var (cdr lst))))))
)

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

; Quoting :doc bind-free (and similarly for syntaxp): "every variable occuring
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
; implementation, we found no such cases in
; books/workshops/2004/legato/support/proof-by-generalization-mult.lisp,
; books/workshops/2004/smith-et-al/support/bags/eric-meta.lisp, or an
; "insert-proof" example sent to us by Dave Greve.

  (cond
   ((rw-cacheable-failure-reason failure-reason)

; We take advantage here of the guard on rw-cacheable-failure-reason, i.e.,
; that (consp failure-reason) and (posp (car failure-reason)).

    (let* ((hyp (nth (1- (car failure-reason)) hyps))
           (entry (make rw-cache-entry
                        :unify-subst
                        (restrict-alist-to-all-vars
                         unify-subst

; In the case of a synp hypothesis, our possible restriction of unify-subst is
; based on the variables occurring free in the term that is to be evaluated.

                         (cond ((and (nvariablep hyp)
                                     (eq (ffn-symb hyp) 'synp))
                                (let ((qterm (fargn hyp 3)))
                                  (assert$ (quotep qterm)
                                           (unquote qterm))))
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

; Recs is a psorted list of rw-cache-entry records.  We know that some record
; in recs whose :failure-reason satisfies free-failure-p has the given
; unify-subst and hyps fields, and we replace that one by the given entry.

  (cond ((endp recs)
         (er hard 'replace-free-rw-cache-entry1 ; see comment above
             "Implementation error: see 'replace-free-rw-cache-entry"))
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
; stored under the base-symbol of rune as the key, has the given unify-subst
; and hyps.  We replace it with entry.

  (let* ((cache (tagged-objects tag ttree))
         (base (base-symbol rune))
         (recs (cdr (assoc-rw-cache base cache))))
    (assert$
     recs ; otherwise we wouldn't be doing a replacement
     (extend-tag-tree
      tag
      (put-assoc-rw-cache
       base
       (replace-free-rw-cache-entry1 unify-subst hyps entry recs)
       cache)
      (remove-tag-from-tag-tree tag ttree)))))

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

(defun alist-keys-subsetp (x keys)
  (cond ((endp x) t)
        ((member-eq (caar x) keys)
         (alist-keys-subsetp (cdr x) keys))
        (t nil)))

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
              (rw-cacheable-failure-reason failure-reason))
         (acons new-unify-subst
                failure-reason
                rw-cache-alist-new))
        (t rw-cache-alist-new)))

(mutual-recursion

; State is an argument of rewrite only to permit us to call ev.  In general,
; wrld may be an extension of (f-get-global 'current-acl2-world state), but we
; use state only to pass it down to ev.

; Keep this nest in sync with mfc-rw+ and pc-rewrite*.

(defun rewrite (term alist bkptr ; &extra formals
                     rdepth step-limit
                     type-alist obj geneqv wrld state fnstack ancestors
                     backchain-limit
                     simplify-clause-pot-lst rcnst gstack ttree)

; See the :Doc-Section documentation string for the rule-class REWRITE
; below.  It is unfortunate that we had to use up the doc string for
; this function to document a random token.  This points out a flaw
; in our design of the documentation facilities.

; Comments on the function REWRITE

; The Input
; c term:       the "matrix" term we are to rewrite.
; c alist:      a substitution we are to apply to term before rewriting it.
; h type-alist: a list of assumptions governing this rewrite
;   obj:        (objective of rewrite) t, nil, or ? - of heuristic use only.
; c geneqv:     a generated equivalence relation to maintain
;   wrld:       the current world
;   fnstack:    fns and terms currently being expanded - of heuristic use only
; h ancestors:  a list of terms assumed true, modified as we backchain.
; h backchain-limit: of heuristic use only
; h simplify-clause-pot-lst: a pot-lst of polys
; h rcnst:      the rewrite constant arguments
; h ttree:      the evolving ttree describing the rewrites.
;   rdepth:     maximum allowed stack depth - of heuristic use only
;   step-limit: number of recursive calls permitted for rewrite

; The Output:
; a new step-limit, a term term', and a tag-tree ttree'

; The Specification of Rewrite: The axioms in wrld permit us to infer that the
; Rewrite Assumption implies that term' is geneqv to term/alist.  One can write
; this "wrld |- h -> c."  The args are tagged with h and c according to how
; they are involved in this spec.

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

  ":Doc-Section Rule-Classes

  make some ~c[:rewrite] rules (possibly conditional ones)~/

  This doc topic discusses the rule-class ~c[:rewrite].  If you want a general
  discussion of how rewriting works in ACL2 and some guidance on how to
  construct effective rewrite rules, ~pl[introduction-to-rewrite-rules-part-1]
  and then ~pl[introduction-to-rewrite-rules-part-2].

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.  Example ~c[:]~ilc[corollary]
  formulas from which ~c[:rewrite] rules might be built are:
  ~bv[]
  Example:
  (equal (+ x y) (+ y x))            replace (+ a b) by (+ b a) provided
                                     certain heuristics approve the
                                     permutation.

  (implies (true-listp x)            replace (append a nil) by a, if
           (equal (append x nil) x)) (true-listp a) rewrites to t

  (implies                           replace (member a (append b c)) by
      (and (eqlablep e)              (member a (append c b)) in contexts  
           (true-listp x)            in which propositional equivalence
           (true-listp y))           is sufficient, provided (eqlablep a)
      (iff (member e (append x y))   (true-listp b) and (true-listp c)
           (member e (append y x)))) rewrite to t and the permutative
                                     heuristics approve~/

  General Form:
  (and ...
       (implies (and ...hi...)
                (implies (and ...hk...)
                         (and ...
                              (equiv lhs rhs)
                              ...)))
       ...)
  ~ev[]
  Note: One ~c[:rewrite] rule class object might create many rewrite rules from
  the ~c[:]~ilc[corollary] formula.  To create the rules, we first translate
  the formula, expanding all macros (~pl[trans]) and also expanding away calls
  of all so-called ``guard holders,'' ~ilc[mv-list] and ~ilc[return-last] (the
  latter resulting for example from calls of ~ilc[prog2$], ~ilc[mbe], or
  ~ilc[ec-call]), as well as expansions of the macro `~ilc[the]'.  Next, we
  eliminate all ~c[lambda]s; one may think of this step as simply substituting
  away every ~ilc[let], ~ilc[let*], and ~ilc[mv-let] in the formula.  We then
  flatten the ~ilc[AND] and ~ilc[IMPLIES] structure of the formula; for
  example, if the hypothesis or conclusion is of the form
  ~c[(and (and term1 term2) term3)], then we replace that by the ``flat'' term
  ~c[(and term1 term2 term3)].  (The latter is actually an abbreviation for the
  right-associated term ~c[(and term1 (and term2 term3))].)  The result is a
  conjunction of formulas, each of the form
  ~bv[]
  (implies (and h1 ... hn) concl)
  ~ev[]
  where no hypothesis is a conjunction and ~c[concl] is neither a conjunction
  nor an implication.  If necessary, the hypothesis of such a conjunct may be
  vacuous.  We then further coerce each ~c[concl] into the form
  ~c[(equiv lhs rhs)], where ~c[equiv] is a known ~il[equivalence] relation, by
  replacing any ~c[concl] not of that form by ~c[(iff concl t)].  A ~c[concl]
  of the form ~c[(not term)] is considered to be of the form
  ~c[(iff term nil)].  By these steps we reduce the given ~c[:]~ilc[corollary]
  to a sequence of conjuncts, each of which is of the form
  ~bv[]
  (implies (and h1 ... hn)
           (equiv lhs rhs))
  ~ev[]
  where ~c[equiv] is a known ~il[equivalence] relation.  ~l[equivalence] for a
  general discussion of the introduction of new ~il[equivalence] relations.
  At this point, we check whether ~c[lhs] and ~c[rhs] are the same term; if so,
  we cause an error, since this rule will loop.  (But this is just a basic
  check; the rule could loop in other cases, for example if ~c[rhs] is an
  instance of ~c[lhs]; ~pl[loop-stopper].)

  We create a ~c[:rewrite] rule for each such conjunct, if possible, and
  otherwise cause an error.  It is possible to create a rewrite rule from such
  a conjunct provided ~c[lhs] is not a variable, a quoted constant, a
  ~ilc[let]-expression, a ~c[lambda] application, or an ~ilc[if]-expression.

  A ~c[:rewrite] rule is used when any instance of the ~c[lhs] occurs in a
  context in which the ~il[equivalence] relation is an admissible ~il[congruence]
  relation.  First, we find a substitution that makes ~c[lhs] equal to the
  target term.  Then we attempt to relieve the instantiated hypotheses of the
  rule.  Hypotheses that are fully instantiated are relieved by recursive
  rewriting.  Hypotheses that contain ``free variables'' (variables not
  assigned by the unifying substitution) are relieved by attempting to guess a
  suitable instance so as to make the hypothesis equal to some known assumption
  in the context of the target.  If the hypotheses are relieved, and certain
  restrictions that prevent some forms of infinite regress are
  met (~pl[loop-stopper]), the target is replaced by the instantiated ~c[rhs],
  which is then recursively rewritten.

  ACL2's rewriting process has undergone some optimization.  In particular,
  when a term ~c[t1] is rewritten to a new term ~c[t2], the rewriter is then
  immediately applied to ~c[t2].  On rare occasions you may find that you do
  not want this behavior, in which case you may wish to use a trick involving
  ~ilc[hide]; ~pl[meta], near the end of that documentation.

  In another optimization, when the hypotheses and right-hand side are rewritten,
  ACL2 does not really first apply the substitution and then rewrite; instead, it
  as it rewrites those terms it looks up the ~i[already rewritten] values of the
  bound variables.  Sometimes you may want those bindings rewritten again, e.g.,
  because the variables occur in slots that admit additional equivalence
  relations.  See ~i[double-rewrite].

  ~l[introduction-to-rewrite-rules-part-1] and
  ~pl[introduction-to-rewrite-rules-part-2] for an extended discussion of how
  to create effective rewrite rules.~/

  :cite free-variables
  :cite force
  :cite case-split
  :cite double-rewrite
  :cite syntaxp
  :cite bind-free"

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
     (cond ((zero-depthp rdepth)
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
           ((fquotep term) (mv step-limit term ttree))
           ((eq (ffn-symb term) 'if)

; Normally we rewrite (IF a b c) by rewriting a and then one or both
; of b and c, depending on the rewritten a.  But in the special case
; (IF a b b) we just rewrite and return b.  We have seen examples
; where this comes up, e.g., nth-update-rewriter can produce such IFs.

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
;                                      ; doesn't rewrite to a consant
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
                       :geneqv *geneqv-iff*)
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

            (sl-let (rewritten-test ttree)
                    (rewrite-entry (rewrite (fargn term 1) alist 1)
                                   :obj '?
                                   :geneqv *geneqv-iff*)
                    (sl-let (rewritten-concl ttree)
                            (rewrite-entry (rewrite (fargn term 2) alist 1)
                                           :obj '?
                                           :geneqv *geneqv-iff*)
                            (mv step-limit
                                (subcor-var

; It seems reasonable to keep this in sync with the corresponding use of
; subcor-var in rewrite-atm.

                                 (formals 'IMPLIES wrld)
                                 (list rewritten-test
                                       rewritten-concl)
                                 (body 'IMPLIES t wrld))
                                ttree))))
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
              (cond
               ((and (eq fn 'mv-nth)
                     (simplifiable-mv-nthp term alist))

; This is a special case.  We are looking at a term/alist of the form
; (mv-nth 'i (cons x0 (cons x1 ... (cons xi ...)...))) and we immediately
; rewrite it to xi and proceed to rewrite that.  Before we did this, we would
; rewrite x0, x1, etc., all of which are irrelevant.  This code is helpful
; because of the way (mv-let (v0 v1 ... vi ...) (foo ...) (p v0 ...))
; is translated.  Note however that the bkptr we report in the rewrite entry
; below is 2, i.e., we say we are rewriting the 2nd arg of the mv-nth, when
; in fact we are rewriting a piece of it (namely xi).

                (mv-let (term1 alist1)
                        (simplifiable-mv-nth term alist)
                        (rewrite-entry
                         (rewrite term1 alist1 2)
                         :ttree (push-lemma
                                 (fn-rune-nume 'mv-nth nil nil wrld)
                                 ttree))))
               (t
                (mv-let
                 (flg term1 ttree1)
; Rockwell Addition
                 (cond
                  ((eq (nu-rewriter-mode wrld) :literals)
                   (mv nil nil nil))
                  (t
                   (nth-update-rewriter
                    (cond (ancestors t) ; see below
                          ((recursive-fn-on-fnstackp fnstack) t)
                          (t nil))
                    term alist
                    (access rewrite-constant rcnst
                            :current-enabled-structure)
                    wrld
                    state)))

; Note about the handling of the recursivelyp flag above: If ancestors
; is non-nil or if there is a recursive function on the fnstack, then
; this term was not analyzed by the call of nth-update-rewriter in
; rewrite-atm.  Therefore, we explore it recursively to get rid of
; huge irrelevant parts.  But if ancestors is nil and there are no
; recursive functions in sight, then this term was seen earlier.  It
; is possible that it was seen under a different context -- our alist
; here contains rewritten terms.  So it is possible the term can be
; further simplified now.  But rewrite is now recursing through the
; main goal and there is no need for nth-update-rewriter to do that.
; So we need not look at it recursively.

                 (cond
                  (flg (rewrite-entry
                        (rewrite term1 nil 'nth-update)
                        :ttree (cons-tag-trees ttree1 ttree)))
                  (t
                   (sl-let
                    (rewritten-args ttree)
                    (rewrite-entry
                     (rewrite-args
                      (fargs term)
                      alist
                      1)
                     :obj '?
                     :geneqv
                     (geneqv-lst fn
                                 geneqv
                                 (access rewrite-constant rcnst
                                         :current-enabled-structure)
                                 wrld))
                    (cond
                     ((and
                       (or (flambdap fn)
                           (logicalp fn wrld))
                       (all-quoteps rewritten-args)
                       (or
                        (flambda-applicationp term)
                        (and (enabled-xfnp
                              fn
                              (access rewrite-constant rcnst
                                      :current-enabled-structure)
                              wrld)

; We don't mind disallowing constrained functions that have attachments,
; because the call of ev-fncall below disallows the use of attachments (last
; parameter, aok, is nil).

                             (not (getprop fn 'constrainedp nil
                                           'current-acl2-world
                                           wrld)))))

; Note: The test above, if true, leads here where we execute the
; executable counterpart of the fn (or just go into the lambda
; expression if it's a lambda application).  The test however is
; obscure.  What it says is "run the function if (a) it is either a
; lambda or a :logic function symbol, (b) all of its args are quoted
; constants, and either (c1) the fn is a lambda expression, or (c2)
; the fn is enabled and fn is not a constrained fn."  Thus,
; constrained fns fail the test.  Defined functions pass the test
; provided such functions are currently toggled.  Undefined functions
; (e.g., car) pass the test.

                      (cond ((flambda-applicationp term)
                             (rewrite-entry
                              (rewrite (lambda-body fn)
                                       (pairlis$ (lambda-formals fn)
                                                 rewritten-args)
                                       'lambda-body)))
                            (t
                             (mv-let
                              (erp val latches)
                              (pstk
                               (ev-fncall fn
                                          (strip-cadrs rewritten-args)
                                          state
                                          nil t nil))
                              (declare (ignore latches))
                              (cond
                               (erp

; We following a suggestion from Matt Wilding and attempt to rewrite the term
; before applying HIDE.  This is really a heuristic choice; we could choose
; always to apply HIDE, as we did before v2-8.  So we do not apply
; nth-update-rewriter (as in the next next COND clause, below), nor do we apply
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
                                         (fcons-term* 'hide new-term1)
                                         (push-lemma (fn-rune-nume 'hide nil nil
                                                                   wrld)
                                                     ttree)))
                                    (t (mv step-limit new-term2 ttree))))))
                               (t (mv step-limit
                                      (kwote val)
                                      (push-lemma
                                       (fn-rune-nume fn nil t wrld)
                                       ttree))))))))
                     ((and (or (equal fn 'NTH)
                               (flambdap fn)
                               (not (recursivep fn wrld)))
                           (not (member-eq (nu-rewriter-mode wrld)
                                           '(nil :literals)))
                           (not (equal-mod-alist-lst
                                 (fargs term) alist rewritten-args)))

; If this is an application of NTH, a lambda expression, or a
; non-recursive function, and the arguments changed in the rewrite
; above, then we will try nth-update-rewriter again.  We do so
; recursively.

                      (mv-let (hitp term1 ttree1)
; Rockwell Addition
                              (nth-update-rewriter
                               t
                               (cons-term fn rewritten-args)
                               nil
                               (access rewrite-constant rcnst
                                       :current-enabled-structure)
                               wrld
                               state)
                              (cond
                               (hitp
                                (rewrite-entry
                                 (rewrite term1 nil 'nth-update)
                                 :ttree (cons-tag-trees ttree1 ttree)))
                               (t

; Note:  This code is the same as that below.  Keep them in sync!

                                (sl-let
                                 (rewritten-term ttree)
                                 (rewrite-entry
                                  (rewrite-primitive fn rewritten-args))
                                 (rewrite-entry
                                  (rewrite-with-lemmas rewritten-term)))))))
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
                              type-alist obj geneqv wrld state fnstack ancestors
                              backchain-limit
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
                            (getprop (ffn-symb new-term) 'lemmas nil
                                     'current-acl2-world wrld)))
                          (declare (ignore rewrittenp))
                          (mv step-limit term1 ttree)))))))

(defun rewrite-if (test unrewritten-test left right alist ; &extra formals
                        rdepth step-limit
                        type-alist obj geneqv wrld state fnstack ancestors
                        backchain-limit
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
   (cond
    ((and (nvariablep test)
          (not (fquotep test))
          (eq (ffn-symb test) 'if)
          (equal (fargn test 2) *nil*)
          (equal (fargn test 3) *t*))

; Note: In Nqthm the equality test against *t* was a known-whether-nil check.
; But unrewritten-test has been rewritten under equiv = 'iff.  Hence, its two
; branches were rewritten under 'iff.  Thus, if one of them is known non-nil
; under the type-alist then it was rewritten to *t*.

     (rewrite-entry (rewrite-if (fargn test 1) nil right left alist)))
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
; looping).  It was apprently due to the opening of MEMBER on a long constant
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
                                        :ttree (rw-cache-enter-context ttree))
                         (let ((ttree (rw-cache-exit-context ttree ttree1)))
                           (prepend-step-limit
                            2
                            (rewrite-if1 test
                                         rewritten-left rewritten-right
                                         type-alist geneqv ens
                                         (ok-to-force rcnst)
                                         wrld ttree))))))))))))))

(defun rewrite-args (args alist bkptr; &extra formals
                          rdepth step-limit
                          type-alist obj geneqv wrld state fnstack ancestors
                          backchain-limit
                          simplify-clause-pot-lst rcnst gstack ttree)

; Note: In this function, the extra formal geneqv is actually a list of geneqvs
; or nil denoting a list of nil geneqvs.

  (declare (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   3
   (signed-byte 30)
   (cond ((null args)
          (mv step-limit nil ttree))
         (t (sl-let
             (rewritten-arg ttree)
             (rewrite-entry (rewrite (car args) alist bkptr)
                            :geneqv (car geneqv))
             (sl-let
              (rewritten-args ttree)
              (rewrite-entry (rewrite-args (cdr args) alist (1+ bkptr))
                             :geneqv (cdr geneqv))
              (mv step-limit
                  (cons rewritten-arg rewritten-args)
                  ttree)))))))

(defun rewrite-primitive (fn args ; &extra formals
                             rdepth step-limit
                             type-alist obj geneqv wrld state fnstack ancestors
                             backchain-limit
                             simplify-clause-pot-lst rcnst gstack
                             ttree)

  (declare (ignore geneqv obj)
           (type (unsigned-byte 29) rdepth)
           (type (signed-byte 30) step-limit))
  (the-mv
   3
   (signed-byte 30)
   (cond
    ((flambdap fn) (mv step-limit (fcons-term fn args) ttree))
    ((eq fn 'equal)
     (rewrite-entry (rewrite-equal (car args) (cadr args) nil nil)
                    :obj '? ; don't-care
                    :geneqv nil))
    (t (let* ((ens (access rewrite-constant rcnst
                           :current-enabled-structure))
              (recog-tuple (most-recent-enabled-recog-tuple
                            fn
                            (global-val 'recognizer-alist wrld)
                            ens)))
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
                          type-alist obj geneqv wrld state fnstack ancestors
                          backchain-limit
                          simplify-clause-pot-lst rcnst gstack ttree)

; We rewrite and return a term equivalent to (EQUAL lhs rhs), plus a ttree.
; We keep lists lhs-ancestors and rhs-ancestors of lhs and rhs parameters from
; superior calls, in order to break loops as explained below.

  (declare (ignore obj geneqv)
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
; call of type-set-equalo, is handled by that call.

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
                                                alist
                                                1)
                                  :obj '?
                                  :geneqv nil
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
                                  :obj '?
                                  :geneqv nil
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
                                                   alist
                                                   1)
                                     :obj '?
                                     :geneqv nil
                                     :ttree new-ttree)
                      (rewrite-entry (rewrite-equal
                                      (car cdrs)
                                      (cadr cdrs)
                                      (cons lhs lhs-ancestors)
                                      (cons rhs rhs-ancestors))
                                     :obj '?
                                     :geneqv nil
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
                               (rewrite-entry (rewrite-args '((cdr lhs) (cdr rhs))
                                                            alist
                                                            1)
                                              :obj '?
                                              :geneqv nil
                                              :ttree ttree)
                               (rewrite-entry
                                (rewrite-equal
                                 (car cdrs)
                                 (cadr cdrs)
                                 (cons lhs lhs-ancestors)
                                 (cons rhs rhs-ancestors))
                                :obj '?
                                :geneqv nil
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
        type-alist obj geneqv wrld state fnstack ancestors
        backchain-limit
        simplify-clause-pot-lst rcnst gstack ttree)

; We are trying to rewrite hyp0 to true, where hyp0 is the hypothesis of rune
; at (one-based) position bkptr, and target is an instantiated term to which
; rune is being applied.

; We return six results.  Most often they are interpreted as indicated by the
; names:

; (mv step-limit wonp failure-reason unify-subst' ttree' memo'),

; but there is a special case where they are interpreted differently.  In
; general, wonp is t, nil or a term.  If it is t or nil, the interpretation of
; the results is as hinted above: Wonp indicates whether hyp0 was relieved,
; failure-reason is nil or else a token indicating why we failed, and the rest
; are extended versions of the corresponding inputs.

; But if wonp is a term then it means that hyp0 contains free-vars, it was not
; relieved, and the six results are to be interpreted as:

; (mv step-limit term typ unify-subst ttree memo)

; where the last three are unchanged.  This signals that the caller of
; relieve-hyp is responsible for relieving the hypothesis and may do so in
; either of two ways: Extend unify-subst to make term have typ in the original
; type-alist or extend unify-subst to make hyp0 true via ground units.  This is
; called the SPECIAL CASE.

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
; is a bkptr, vars is (all-vars hyp0), and ttreei is the result of succesfully
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

  (declare (ignore obj geneqv)
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
   (cond ((and (nvariablep hyp0)
               (not (fquotep hyp0))
               (eq (ffn-symb hyp0) 'synp))
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
                   (cons (list :binding-hyp hyp unify-subst)
                         ancestors)
                   :geneqv (and (not (eq (ffn-symb hyp) 'equal))
                                (cadr (geneqv-lst
                                       (ffn-symb hyp)
                                       *geneqv-iff*
                                       (access rewrite-constant rcnst
                                               :current-enabled-structure)
                                       wrld))))
                  (mv step-limit
                      t
                      nil
                      (cons (cons (fargn hyp 1) rewritten-rhs)
                            unify-subst)
                      ttree
                      memo)))
                ((free-varsp hyp unify-subst)

; See comment above about "SPECIAL CASE".

                 (mv-let (term typ)
                         (term-and-typ-to-lookup hyp wrld)
                         (mv step-limit term typ unify-subst ttree memo)))
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
                         (lookup-hyp hyp type-alist wrld unify-subst ttree)

; We know that unify-subst is not extended, since (free-varsp hyp unify-subst)
; is false, but it still seems appropriate to use the existing code in
; one-way-unify1 under search-type-alist (under lookup-hyp).

                         (cond
                          (lookup-hyp-ans
                           (mv step-limit t nil unify-subst ttree))
                          (t
                           (let ((inst-hyp (sublis-var unify-subst hyp)))
                             (mv-let
                              (on-ancestorsp assumed-true)
                              (ancestors-check inst-hyp ancestors (list rune))
                              (cond
                               (on-ancestorsp (mv step-limit
                                                  assumed-true
                                                  (if (null assumed-true)
                                                      'ancestors
                                                    nil)
                                                  unify-subst ttree))
                               (t
                                (let* ((forcer-fn (and forcep1 (ffn-symb hyp0)))
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
                                    ((backchain-limit-reachedp
                                      backchain-limit
                                      ancestors)
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
                                            (cons 'backchain-limit
                                                  backchain-limit)
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
                                                      :ancestors
                                                      (push-ancestor
                                                       (dumb-negate-lit
                                                        inst-hyp)
                                                       (list rune)
                                                       ancestors))
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
                                                     ttree)))))))))))))))))))))
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

(defun relieve-hyps1 (rune target hyps backchain-limit-lst
                           unify-subst bkptr unify-subst0
                           ttree0 allp
                           rw-cache-alist rw-cache-alist-new ; &extra formals
                           rdepth step-limit
                           type-alist obj geneqv wrld state fnstack ancestors
                           backchain-limit
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

  (declare (ignore obj geneqv)
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
                      :obj nil
                      :geneqv nil)
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
                       :obj nil
                       :geneqv nil
                       :ttree new-ttree))
       (relieve-hyp-ans

; As explained in the "SPECIAL CASE" comment in relieve-hyp, relieve-hyp
; returned (mv step-limit term typ unify-subst ttree allp).  We enter a loop in
; which we try to relieve the current hypothesis and subsequent hypotheses by
; instantiating the variables in term that are free with respect to
; unify-subst.

        (let* ((hyp (car hyps))
               (forcep1 (and (nvariablep hyp)
                             (not (fquotep hyp))
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
                   :obj nil
                   :geneqv nil)
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
        type-alist obj geneqv wrld state fnstack ancestors
        backchain-limit
        simplify-clause-pot-lst rcnst gstack
        ttree)

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

  (declare (ignore obj geneqv)
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
                         :obj nil
                         :geneqv nil
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
                 :obj nil
                 :geneqv nil
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
       :obj nil
       :geneqv nil))))))

(defun relieve-hyps1-free-2
  (hyp lemmas forcer-fn forcep ens force-flg
       rune target hyps backchain-limit-lst
       unify-subst bkptr unify-subst0
       ttree0 allp rw-cache-alist rw-cache-alist-new ; &extra formals
       rdepth step-limit
       type-alist obj geneqv wrld state fnstack ancestors
       backchain-limit
       simplify-clause-pot-lst rcnst gstack
       ttree)

; We search ground units in an attempt to extend unify-subst to make term true,
; As with relieve-hyps1-free-1, we return a relieve-hyps-ans, a
; failure-reason-lst that is a list of pairs (cons new-unify-subst
; failure-reason), a unify-subst extending the given unify-subst, a ttree, and
; a resulting allp.

  (declare (ignore obj geneqv)
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
              (rewrite-entry (relieve-hyps1 rune target (cdr hyps)
                                            (cdr backchain-limit-lst)
                                            fully-bound-unify-subst
                                            (1+ bkptr)
                                            unify-subst0 ttree0 allp
                                            (cdr cached-failure-reason-free)
                                            nil)
                             :obj nil
                             :geneqv nil)
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
      (search-ground-units1
       hyp unify-subst lemmas type-alist
       ens force-flg wrld ttree)
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
                           :obj nil
                           :geneqv nil
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
                   :obj nil
                   :geneqv nil
                   :ttree (accumulate-rw-cache t ttree1 ttree)))))))))))
       (t (mv step-limit nil
              nil ; failure-reason-lst
              unify-subst0

; We believe that new-ttree is unlikely to have rw-cache entries that are not
; already in ttree0, as they would generally (always?) come from type-set
; computations.  But we expect the following call to be cheap, so we make it.

              (accumulate-rw-cache t new-ttree ttree0)
              allp rw-cache-alist-new))))))))

(defun relieve-hyps (rune target hyps backchain-limit-lst
                          unify-subst allp ; &extra formals
                          rdepth step-limit
                          type-alist obj geneqv wrld state fnstack ancestors
                          backchain-limit
                          simplify-clause-pot-lst rcnst gstack ttree)

; We return t or nil indicating success, a token indicating why we failed (or
; nil if we succeeded), an extended unify-subst and a new ttree.  Allp is
; either t or nil, according to whether or not we are to attempt all free
; variable matches until we succeed.

; This function is a No-Change Loser modulo rw-cache: only the values of
; 'rw-cache-any-tag and 'rw-cache-nil-tag may differ between the input and
; output ttrees.

  (declare (ignore obj geneqv)
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
                    :obj nil
                    :geneqv nil

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
; Prime-property-lemma, in distributed book
; workshops/2006/cowles-gamboa-euclid/Euclid/ed3.lisp, fails with
; :rw-cache-state :atom.

                                  (note-relieve-hyp-failure
                                   rune unify-subst failure-reason
                                   ttree hyps

; See comment above about regarding our formerly saving the step-limit only in
; debug mode.

                                   step-limit-saved)))))))))))))

(defun rewrite-with-lemma (term lemma ; &extra formals
                                rdepth step-limit
                                type-alist obj geneqv wrld state
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

              (let ((args
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
                                   :ttree ttree)
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
                   (ev-fncall-meta (access rewrite-rule lemma :lhs)
                                   args
                                   state))
                  (declare (ignore latches))
                  (cond
                   (erp
                    (mv step-limit nil term ttree))
                   ((equal term val)
                    (mv step-limit nil term ttree))
                   ((termp val wrld)
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
                        ((termp evaled-hyp wrld)
                         (let* ((vars (all-vars term))
                                (hyps (flatten-ands-in-lit

; Note: The sublis-var below normalizes the explicit constant
; constructors in evaled-hyp, e.g., (cons '1 '2) becomes '(1 . 2).

                                       (sublis-var nil evaled-hyp)))
                                (rule-backchain-limit
                                 (access rewrite-rule lemma 
                                         :backchain-limit-lst))
                                (bad-synp-hyp-msg
                                 (bad-synp-hyp-msg hyps vars nil wrld)))
                           (cond
                            (bad-synp-hyp-msg
                             (mv step-limit
                                 (er hard 'rewrite-with-lemma
                                     "The hypothesis metafunction ~x0, when ~
                                      applied to the input term ~x1, produced ~
                                      a term whose use of synp is illegal ~
                                      because ~@2"
                                     hyp-fn
                                     term
                                     bad-synp-hyp-msg)
                                 term ttree))
                            (t
                             (sl-let
                              (relieve-hyps-ans failure-reason unify-subst ttree)
                              (rewrite-entry (relieve-hyps

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

                                              (pairlis$ vars vars)
                                              nil ; allp=nil for meta rules
                                              )
                                             :obj nil
                                             :geneqv nil)

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

; Note: The sublis-var below normalizes the explicit constant
; constructors in val, e.g., (cons '1 '2) becomes '(1 . 2).

                                                  (sublis-var nil val)

; At one point we ignored the unify-subst constructed above and used a
; nil here.  That was unsound if val involved free vars bound by the
; relief of the evaled-hyp.  We must rewrite val under the extended
; substitution.  Often that is just the identity substitution.

                                                  unify-subst
                                                  'meta)
                                                 :ttree

; Should we be pushing executable counterparts into ttrees when we applying
; metafunctions on behalf of meta rules?  NO:  We should only do that if the
; meta-rule's use is sensitive to whether or not they're enabled, and it's not
; -- all that matters is if the rule itself is enabled.

                                                 (push-lemma
                                                  (geneqv-refinementp
                                                   (access rewrite-rule lemma :equiv)
                                                   geneqv
                                                   wrld)
                                                  (push-lemma rune ttree)))
                                  :conc
                                  hyps)
                                 (mv step-limit t rewritten-rhs ttree)))
                               (t (mv step-limit nil term ttree))))))))
                        (t (mv step-limit
                               (er hard 'rewrite-with-lemma
                                   "The hypothesis function ~x0 produced the ~
                                    non-termp ~x1 on the input term ~x2.  Our ~
                                    implementation requires that ~x0 produce ~
                                    a term."
                                   hyp-fn
                                   evaled-hyp
                                   term
                                   (access rewrite-rule lemma :lhs))
                               term ttree))))))
                   (t (mv step-limit
                          (er hard 'rewrite-with-lemma
                              "The metafunction ~x0 produced the non-termp ~
                               ~x1 on the input term ~x2. The proof of the ~
                               correctness of ~x0 establishes that the ~
                               quotations of these two s-expressions have the ~
                               same value, but our implementation ~
                               additionally requires that ~x0 produce a term."
                              (access rewrite-rule lemma :lhs)
                              val
                              term)
                          term ttree)))))))
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
                     (not (being-openedp (ffn-symb term) fnstack
                                         (recursivep (ffn-symb term) wrld)))
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
                                           gstack state)))
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
                            (rewrite-entry (relieve-hyps
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
                                           :obj nil
                                           :geneqv nil)
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
                                    (push-lemma (geneqv-refinementp
                                                 (access rewrite-rule lemma :equiv)
                                                 geneqv
                                                 wrld)
                                                (push-lemma
                                                 rune
                                                 ttree))))))
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
                                  type-alist obj geneqv wrld state
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
                       type-alist obj geneqv wrld state fnstack ancestors
                       backchain-limit
                       simplify-clause-pot-lst rcnst gstack ttree)

; Rule is a :REWRITE rule of subclass DEFINITION or else it is nil.  Rule is
; nil iff term is a lambda application.  The three values returned by this
; function are the new step-limit, the (possibly) rewritten term, and the new
; ttree.  We assume rule is enabled.

; Term is of the form (fn . args).

; Nqthm Discrepancy: In nqthm, the caller of rewrite-fncall,
; rewrite-with-lemmas, would ask whether the result was different from term and
; whether it contained rewriteable calls.  If so, it called the rewriter on the
; result.  We have changed that here so that rewrite-fncall, in the case that
; it is returning the expanded body, asks about rewriteable calls and possibly
; calls rewrite again.  In the implementation below we ask about rewriteable
; calls only for recursively defined fns.  The old code asked the question on
; all expansions.  It is possible the old code sometimes found a rewriteable
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
                 (or (being-openedp fn fnstack recursivep)
                     (fnstack-term-member term fnstack)))
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
; them) and contains-rewriteable-callp.

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
                                    ttree gstack state)))
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
                          :obj nil
                          :geneqv nil)))
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
                                (brkpt2 nil 'too-many-ifs-post-rewrite unify-subst
                                        gstack rewritten-body ttree1 rcnst state)
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
                                      (push-lemma rune ttree1))))))
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
; rewritten body if it contained rewriteable calls.  This allows Nqthm to open
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

                              ((contains-rewriteable-callp
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
                                       (rewrite-entry (rewrite rewritten-body nil
                                                               'rewritten-body)
                                                      :fnstack

; See the reference to fnstack in the comment above.

                                                      (cons (cons :TERM term)
                                                            fnstack)
                                                      :ttree (push-lemma rune
                                                                         ttree1))
                                       (let ((ttree2
                                              (restore-rw-cache-any-tag ttree2
                                                                        ttree1)))
                                         (prog2$
                                          (brkpt2 t nil unify-subst gstack
                                                  rewritten-body ttree2 rcnst state)
                                          (mv step-limit rewritten-body ttree2)))))
                              (t
                               (prog2$
                                (brkpt2 t nil unify-subst gstack rewritten-body
                                        ttree1 rcnst state)
                                (mv step-limit
                                    rewritten-body
                                    (push-lemma rune ttree1))))))
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
                            type-alist obj geneqv wrld state fnstack ancestors
                            backchain-limit
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
                       :geneqv nil)
        (cond
         (rewrittenp
          (mv step-limit rewritten-term ttree))
         (t
          (sl-let
           (rewrittenp rewritten-term ttree)
           (rewrite-entry
            (rewrite-with-lemmas1 term
                                  (getprop (ffn-symb term) 'lemmas nil
                                           'current-acl2-world wrld)))
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

                  (sl-let
                   (rewritten-test ttree)
                   (rewrite-entry (rewrite hyp alist 'expansion)
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
                        (rewrite-entry
                         (rewrite new-term alist 'expansion)
                         :type-alist true-type-alist
                         :ttree (cons-tag-trees ts-ttree ttree)))
                       (must-be-false
                        (mv step-limit
                            (fcons-term* 'hide term)
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
                                        :ttree (rw-cache-enter-context ttree))
                         (prepend-step-limit
                          2
                          (rewrite-if11 (fcons-term* 'if
                                                     rewritten-test
                                                     rewritten-left
                                                     (fcons-term* 'hide term))
                                        type-alist geneqv wrld
                                        (push-lemma (fn-rune-nume 'hide nil
                                                                  nil wrld)
                                                    (rw-cache-exit-context
                                                     ttree ttree1)))))))))))
                 (new-term
                  (rewrite-entry (rewrite new-term alist 'expansion)
                                 :ttree (push-lemma? rune ttree)))
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
                                 type-alist obj geneqv wrld state
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

  (declare (ignore obj geneqv)
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
                (not (fquotep atm))
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

; If we have enabled non-linear arithmetic, we change theories here,
; so that we can have a different normal form for polys and linear- and
; non-linear-arithmetic than when rewriting.

                                    :rcnst rcnst1)
                     (sl-let (rhs ttree)
                             (rewrite-entry (rewrite (fargn atm 2) alist 2)
                                            :obj '?
                                            :geneqv nil ; geneqv equal
                              
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
                                         type-alist obj geneqv wrld state
                                         fnstack ancestors
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

  (declare (ignore obj geneqv ttree)
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
                     :obj nil
                     :geneqv nil
                     :type-alist (cleanse-type-alist type-alist
                                                     (collect-parents
                                                      (car ttrees)))
                     :ttree (car ttrees))
      (sl-let (term-lst ttree-lst)
              (rewrite-entry (rewrite-linear-term-lst (cdr term-lst)
                                                      (cdr ttrees))
                             :obj nil
                             :geneqv nil
                             :ttree nil)
              (mv step-limit
                  (cons term1 term-lst)
                  (cons ttree1 ttree-lst)))))))

(defun add-linear-lemma (term lemma ; &extra formals
                              rdepth step-limit
                              type-alist obj geneqv wrld state fnstack ancestors
                              backchain-limit
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

  (declare (ignore obj geneqv ttree)
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
    (unify-ans unify-subst)
    (one-way-unify (access linear-lemma lemma :max-term)
                   term)
    (cond
     (unify-ans
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
                         :obj nil
                         :geneqv nil
                         :ttree nil)
          (declare (ignore failure-reason))
          (cond
           (relieve-hyps-ans
            (sl-let
             (rewritten-concl ttree2)
             (with-accumulated-persistence
              rune
              ((the (signed-byte 30) step-limit) rewritten-concl ttree2)
              t ; considered a success unless the parent with-acc-p fails
              (rewrite-entry (rewrite-linear-term
                              (access linear-lemma lemma :concl)
                              unify-subst)
                             :obj nil
                             :geneqv nil
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
; linearize to nil, but a regression test using the books distributed
; with ACL2 actually shows a slight improvement in speed (about a
; minute and a half, out of 158 and a half minutes), so we conclude
; that this is not a problem in practice.

; We thank Robert Krug for providing this improvement.

             (let* ((force-flg (ok-to-force rcnst))
                    (temp-lst (linearize rewritten-concl
                                         t
                                         type-alist
                                         (access rewrite-constant rcnst
                                                 :current-enabled-structure)
                                         force-flg
                                         wrld
                                         (push-lemma
                                          rune
                                          ttree2)
                                         state))
                    (lst (or temp-lst
                             (linearize (sublis-var
                                         unify-subst 
                                         (access linear-lemma lemma :concl))
                                        t
                                        type-alist
                                        (access rewrite-constant rcnst
                                                :current-enabled-structure)
                                        force-flg
                                        wrld
                                        (push-lemma
                                         rune
                                         (accumulate-rw-cache t ttree2 ttree1))
                                        state))))
               (cond
                ((and (null (cdr lst))
                      (not (new-and-ugly-linear-varsp
                            (car lst)
                            (<= *max-linear-pot-loop-stopper-value*
                                (loop-stopper-value-of-var 
                                 term
                                 simplify-clause-pot-lst))
                            term)))
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
                   (contradictionp (mv step-limit contradictionp nil))
                   (t (mv step-limit
                          nil
                          (set-loop-stopper-values 
                           (new-vars-in-pot-lst new-pot-lst
                                                simplify-clause-pot-lst
                                                nil)
                           new-pot-lst
                           term
                           (loop-stopper-value-of-var
                            term simplify-clause-pot-lst)))))))
                (t (mv step-limit nil simplify-clause-pot-lst))))))
           (t (mv step-limit nil simplify-clause-pot-lst)))))))
     (t (mv step-limit nil simplify-clause-pot-lst))))))

(defun add-linear-lemmas (term linear-lemmas ; &extra formals
                               rdepth step-limit
                               type-alist obj geneqv wrld state
                               fnstack ancestors
                               backchain-limit
                               simplify-clause-pot-lst rcnst gstack ttree)

; Linear-lemmas is a list of linear-lemmas.  We look for those lemmas
; in linear-lemmas that match term and, if their hyps can be relieved
; and the resulting polys don't contain new and ugly vars, add them to
; the simplify-clause-pot-lst.

; We return two values.  The first is the standard contradictionp.
; The second is the possibly new pot-lst.

  (declare (ignore obj geneqv ttree)
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
                    :obj nil
                    :geneqv nil
                    :ttree nil))
    (t (sl-let
        (contradictionp new-pot-lst)
        (rewrite-entry (add-linear-lemma term
                                         (car linear-lemmas))
                       :obj nil
                       :geneqv nil
                       :ttree nil)
        (cond (contradictionp (mv step-limit contradictionp nil))
              (t (rewrite-entry
                  (add-linear-lemmas term (cdr linear-lemmas))
                  :obj nil
                  :geneqv nil
                  :ttree nil
                  :simplify-clause-pot-lst new-pot-lst))))))))

(defun multiply-alists2 (alist-entry1 alist-entry2 poly ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv wrld state fnstack
                                      ancestors backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)

; We are in the middle of multiplying two polys.  Poly is the result
; so far.  Alist-entry1 is an alist entry from the first poly, and
; alist-entry2 is an alist entry from the second poly.  See multiply-alists.

; Here, we perform the actual multiplication of the two alist entries
; and add the result to poly.  Note that each entry is of the form
; (term . coeff).

  (declare (ignore obj geneqv ttree)
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
                                     type-alist obj geneqv wrld state fnstack
                                     ancestors backchain-limit
                                     simplify-clause-pot-lst
                                     rcnst gstack ttree)

; We are in the middle of multiplying two polys.  Poly is the result
; so far.  Alist-entry is an alist entry from the first poly, and
; alist2 is the alist from the second poly.  See multiply-alists.

; Here, we cdr down alist2 multiplying alist-entry by each entry in
; alist2 and adding the result to poly.

  (declare (ignore obj geneqv ttree)
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
       :obj nil
       :geneqv nil
       :ttree nil)
      (rewrite-entry (multiply-alists1 alist-entry
                                       (cdr alist2)
                                       temp-poly)
                     :obj nil
                     :geneqv nil
                     :ttree nil))))))

(defun multiply-alists (alist1 alist2 poly ; &extra formals
                               rdepth step-limit
                               type-alist obj geneqv wrld state fnstack
                               ancestors backchain-limit
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

  (declare (ignore obj geneqv ttree)
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
       :obj nil
       :geneqv nil
       :ttree nil)
      (rewrite-entry (multiply-alists (cdr alist1)
                                      alist2
                                      temp-poly)
                     :obj nil
                     :geneqv nil
                     :ttree nil))))))

(defun multiply-polys1 (alist1 const1 rel1 alist2 const2 rel2 
                               poly ; &extra formals
                               rdepth step-limit
                               type-alist obj geneqv wrld state fnstack
                               ancestors backchain-limit
                               simplify-clause-pot-lst
                               rcnst gstack ttree)

; We are in the middle of multiplying two polys.  Poly is the result so far.
; Initially, it has an empty alist which we need to fill in.  Alist1 and const1
; are the alist and constant from the first poly, and alist2 and const2 are
; from the second poly.  We assume that at least one of these two polys is
; rational-poly-p.  Here we constuct the alist for poly, finishing the process.

; If one thinks of the initial polys as

; 0 < const1 + alist1 and 0 < const2 + alist2, 

; poly initially contains 0 < const1*const2 + () and our job is to successively
; add things to the ().  We wish to form const1*alist2 + const2*alist1 +
; alist1*alist2.  The first two steps are performed by the successive
; multiply-alist-and-consts in the let* below, accumulating their answers
; into the growing alist.  We finish with multiply-alists.

  (declare (ignore obj geneqv ttree rel1 rel2)
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
; stricly weaker than the thm's conclusion: consider x=13 and y=1, which makes
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
     (rewrite-entry (multiply-alists alist1 alist2 temp-poly2)
                    :obj nil
                    :geneqv nil
                    :ttree nil))))

(defun multiply-polys (poly1 poly2 ; &extra formals
                             rdepth step-limit
                             type-alist obj geneqv wrld state fnstack
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

  (declare (ignore obj geneqv ttree)
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
        (rewrite-entry (multiply-polys1 alist1 const1 rel1
                                        alist2 const2 rel2
                                        pre-poly)
                       :obj nil
                       :geneqv nil
                       :ttree nil)
        (mv step-limit (normalize-poly poly)))))))

(defun multiply-pots2 (poly big-poly-list new-poly-list ; &extra formals
                            rdepth step-limit
                            type-alist obj geneqv wrld state fnstack
                            ancestors backchain-limit
                            simplify-clause-pot-lst
                            rcnst gstack ttree)

; Poly is a poly and we are to multiply it by the polys in
; big-poly-list, accumulating the answer into new-poly-list.  We
; assume that poly is a rational-poly-p.  Every poly in big-poly-list
; is assumed to be a rational-poly-p.

; We return a list of polys.

  (declare (ignore obj geneqv ttree)
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
              :obj nil
              :geneqv nil
              :ttree nil)
             (rewrite-entry
              (multiply-pots2 poly
                              (cdr big-poly-list)
                              (cons new-poly new-poly-list))
              :obj nil
              :geneqv nil
              :ttree nil)))
    (t

; Since neither poly is known to be rational, we skip this multiplication.

     (rewrite-entry
      (multiply-pots2 poly
                      (cdr big-poly-list)
                      new-poly-list)
      :obj nil
      :geneqv nil
      :ttree nil)))))

(defun multiply-pots1 (poly-list big-poly-list new-poly-list ; &extra formals
                                 rdepth step-limit
                                 type-alist obj geneqv wrld state fnstack
                                 ancestors backchain-limit
                                 simplify-clause-pot-lst
                                 rcnst gstack ttree)

; Both poly-list and big-poly-list are lists of polys.  We are to
; multiply the polys in poly-list by those in big-poly-list.
; New-poly-list is initially nil, and is where we accumulate our
; answer.  We assume every element of big-poly-lst is a
; rational-poly-p.

; We return a list of polys.

  (declare (ignore obj geneqv ttree)
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
       :obj nil
       :geneqv nil
       :ttree nil)
      (rewrite-entry
       (multiply-pots1 (cdr poly-list)
                       big-poly-list
                       new-new-poly-list)
       :obj nil
       :geneqv nil
       :ttree nil))))))

(defun multiply-pots-super-filter (var-list pot-lst-to-look-in ; &extra formals
                                            rdepth step-limit
                                            type-alist obj geneqv wrld state
                                            fnstack
                                            ancestors
                                            backchain-limit
                                            simplify-clause-pot-lst
                                            rcnst gstack ttree)

; This function is similar to multiply-pots, which see, except that we
; only multiply the bounds polys of the pots labeled by the vars in var-list.

; We return a list of polys.

  (declare (ignore obj geneqv ttree)
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
       :obj nil
       :geneqv nil
       :ttree nil)
      (rewrite-entry
       (multiply-pots1 (shortest-polys-with-var (car var-list)
                                                pot-lst-to-look-in
                                                (access rewrite-constant
                                                        rcnst
                                                        :pt))
                       big-poly-list
                       nil)
       :obj nil
       :geneqv nil
       :ttree nil))))))

(defun multiply-pots-filter (var-list pot-lst-to-look-in ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv wrld state fnstack
                                      ancestors backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)

; This function is similar to multiply-pots except that we assume
; var-list is of length two, and we multiply only some of the polys.
; in particular, we multiply the bounds polys of one pot by the polys
; in the other pot, and vice-versa.

; We return a list of polys.

  (declare (ignore obj geneqv ttree)
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
     :obj nil
     :geneqv nil
     :ttree nil)
    (rewrite-entry
     (multiply-pots1 (bounds-polys-with-var (cadr var-list)
                                            pot-lst-to-look-in
                                            (access rewrite-constant
                                                    rcnst
                                                    :pt))
                     (polys-with-var (car var-list)
                                     pot-lst-to-look-in)
                     poly-list1)
     :obj nil
     :geneqv nil
     :ttree nil))))

(defun multiply-pots (var-list pot-lst-to-look-in ; &extra formals
                               rdepth step-limit
                               type-alist obj geneqv wrld state fnstack
                               ancestors backchain-limit
                               simplify-clause-pot-lst
                               rcnst gstack ttree)

; Var-list is a list of pot-labels in pot-lst-to-look-in.  We are
; about to multiply the polys of the labeled pots.  We recur down
; var-list and as we unwind the recursion we multiply the polys
; corresponding to the first pot-label in var-list by the result
; of multiplying the polys corresponding to the rest of the pot-labels.
; Multiply-pots1 is responsible for carrying out the actual multiplication.

; We return a list of polys.

  (declare (ignore obj geneqv ttree)
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
       :obj nil
       :geneqv nil
       :ttree nil)
      (rewrite-entry
       (multiply-pots1 (polys-with-var (car var-list)
                                       pot-lst-to-look-in)
                       big-poly-list
                       nil)
       :obj nil
       :geneqv nil
       :ttree nil))))))

(defun add-multiplied-polys-filter (var-list products-already-tried
                                             pot-lst-to-look-in ; &extra formals
                                             rdepth step-limit
                                             type-alist obj geneqv wrld state fnstack
                                             ancestors backchain-limit
                                             simplify-clause-pot-lst
                                             rcnst gstack ttree)

; This function assumes that var-list is of length two.  It is similar to
; add-multiply-pots, which see, except that we only multiply some of the polys
; corresponding to the pots labeled by the vars in var-list.

  (declare (ignore obj geneqv ttree)
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
       :obj nil
       :geneqv nil
       :ttree nil)

; By filtering the polys so that we avoid creating new pots, we can
; dramatically speed up proofs, for example the failure of the following.  (The
; result is reversed, but no matter.)  Robert Krug contributed this
; modification, and expresses the opinoion that the extra consing done by
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
                                      type-alist obj geneqv wrld state fnstack
                                      ancestors backchain-limit
                                      simplify-clause-pot-lst
                                      rcnst gstack ttree)

; Var-list is a list of pot labels.  If we have not yet multiplied
; the polys corresponding to those labels, we do so and add them to the
; the simplify-clause-pot-lst.  Products-already-tried is a list of the
; factors we have already tried, and pot-lst-to-look-in is the pot-lst
; from which we get our polys.

  (declare (ignore obj geneqv ttree)
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
       :obj nil
       :geneqv nil
       :ttree nil)
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
       :obj nil
       :geneqv nil
       :ttree nil)
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
                                           type-alist obj geneqv wrld state fnstack
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

  (declare (ignore obj geneqv ttree)
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
        :obj nil
        :geneqv nil
        :ttree nil)))
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
                :obj nil
                :geneqv nil
                :ttree nil)
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
                       :obj nil
                       :geneqv nil
                       :ttree nil
                       :simplify-clause-pot-lst new-pot-list)))))
             (t
              (rewrite-entry
               (deal-with-product1 part-of-new-var
                                   var-list
                                   pot-lst-to-look-in
                                   (cdr pot-lst-to-step-down)
                                   products-already-tried)
               :obj nil
               :geneqv nil
               :ttree nil))))))))

(defun deal-with-product (new-var pot-lst-to-look-in
                                  pot-lst-to-step-down
                                  products-already-tried ; &extra formals
                                  rdepth step-limit
                                  type-alist obj geneqv wrld state fnstack
                                  ancestors backchain-limit
                                  simplify-clause-pot-lst
                                  rcnst gstack ttree)

; If new-var is a product, we try to find a set of pots whose labels,
; when multiplied together, form new-var.  If we are succesful at
; gathering such a set of pot labels, we will multiply the polys in those
; pots and add them to the simplify-clause-pot-lst.

; All the deal-with-xxx functions return four values: a new step-limit, the
; standard contradictionp, a potentially augmented pot-lst (or nil if
; contradictionp is true), and the accumulated list of products we have already
; tried.

  (declare (ignore obj geneqv ttree)
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
      :obj nil
      :geneqv nil
      :ttree nil))
    (t
     (mv step-limit nil simplify-clause-pot-lst products-already-tried)))))

(defun deal-with-factor (new-var pot-lst-to-look-in
                                 pot-lst-to-step-down
                                 products-already-tried ; &extra formals
                                 rdepth step-limit
                                 type-alist obj geneqv wrld state fnstack
                                 ancestors backchain-limit
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
; If we are succesful at gathering such a set of pot labels, we will
; multiply the polys in those pots and add them to the simplify-clause-pot-lst.

; All the deal-with-xxx functions return four values: a new step-limit, the
; standard contradictionp, a potentially augmented pot-lst (or nil if
; contradictionp is true), and the accumulated list of products we have already
; tried.

  (declare (ignore obj geneqv ttree)
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
                :obj nil
                :geneqv nil
                :ttree nil)
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
                       :obj nil
                       :geneqv nil
                       :ttree nil
                       :simplify-clause-pot-lst new-pot-list)))))
             (t
              (rewrite-entry
               (deal-with-factor new-var
                                 pot-lst-to-look-in
                                 (cdr pot-lst-to-step-down)
                                 products-already-tried)
               :obj nil
               :geneqv nil
               :ttree nil))))))))

(defun deal-with-division (new-var inverse-var 
                                   pot-lst-to-look-in
                                   pot-lst-to-step-down
                                   products-already-tried ; &extra formals
                                   rdepth step-limit
                                   type-alist obj geneqv wrld state fnstack
                                   ancestors backchain-limit
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

  (declare (ignore obj geneqv ttree)
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
                     :obj nil
                     :geneqv nil
                     :ttree nil)
                    (cond (contradictionp (mv step-limit contradictionp nil nil))
                          (t
                           (rewrite-entry
                            (deal-with-division new-var inverse-var
                                                pot-lst-to-look-in
                                                (cdr pot-lst-to-step-down)
                                                products-already-tried)
                            :obj nil
                            :geneqv nil
                            :ttree nil
                            :simplify-clause-pot-lst new-pot-lst)))))
                  (t
                   (rewrite-entry
                    (deal-with-division new-var inverse-var
                                        pot-lst-to-look-in
                                        (cdr pot-lst-to-step-down)
                                        products-already-tried)
                    :obj nil
                    :geneqv nil
                    :ttree nil))))))))

(defun non-linear-arithmetic1 (new-vars pot-lst ;;; to look-in/step-down
                                        products-already-tried ; &extra formals
                                        rdepth step-limit type-alist obj geneqv
                                        wrld state
                                        fnstack ancestors backchain-limit
                                        simplify-clause-pot-lst
                                        rcnst gstack ttree)

; This is the recursive version of function non-linear-arithmetic.  See the
; comments and documentation there.

  (declare (ignore obj geneqv ttree)
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
             :obj nil
             :geneqv nil
             :ttree nil)
          (mv step-limit nil simplify-clause-pot-lst products-already-tried))
        (cond (contradictionp (mv step-limit contradictionp nil))
              (t
               (sl-let (contradictionp new-pot-lst2 products-already-tried)
                       (rewrite-entry
                        (deal-with-product (car new-vars)
                                           pot-lst ; to-look-in
                                           pot-lst ; to-step-down
                                           products-already-tried)
                        :obj nil
                        :geneqv nil
                        :ttree nil
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
                           :obj nil
                           :geneqv nil
                           :ttree nil
                           :simplify-clause-pot-lst new-pot-lst2)
                          (cond
                           (contradictionp (mv step-limit contradictionp nil))
                           (t
                            (rewrite-entry
                             (non-linear-arithmetic1
                              (cdr new-vars)
                              pot-lst ; to look-in/step-down
                              products-already-tried)
                             :obj nil
                             :geneqv nil
                             :ttree nil
                             :simplify-clause-pot-lst
                             new-pot-lst3)))))))))))))))

(defun non-linear-arithmetic (new-vars pot-lst ;;; to look-in/step-down
                                       products-already-tried ; &extra formals
                                       rdepth step-limit
                                       type-alist obj geneqv wrld state fnstack
                                       ancestors backchain-limit
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

  ":Doc-Section Miscellaneous

  Non-linear Arithmetic~/~/

  This documentation topic is divided into two parts.  We first discuss the
  practical aspect of how to use the non-linear arithmetic extension to ACL2,
  and then the theory behind it.  We assume that the reader is familiar with
  the material in ~ilc[linear-arithmetic] and that on ~c[:]~ilc[linear] rules.

  We begin our discussion of how to use non-linear arithmetic with a simple
  example.  Assume that we wish to prove:
  ~bv[]
  (thm
   (implies (and (rationalp x)
                 (rationalp y)
                 (rationalp z)
                 (< 0 y)
                 (< x (* y z)))
            (< (floor x y) z)))
  ~ev[]

  Note that ~c[(floor x y) <= (/ x y)].  Note also that if we divide both sides
  of ~c[x < (* y z)] by ~c[y], since ~c[0 < y], we obtain ~c[(/ x y) < z].  By
  chaining these two inequalities together, we get the inequality we desired to
  prove.

  We now proceed with our example session:

  ~bv[]
  (skip-proofs
   (progn

  ; Since the truth of this theorem depends on the linear properties
  ; of floor, we will need the linear lemma:

     (defthm floor-bounds-1
         (implies (and (rationalp x)
                       (rationalp y))
                  (and (< (+ (/ x y) -1)
                          (floor x y))
                       (<= (floor x y)
                           (/ x y))))
         :rule-classes ((:linear :trigger-terms ((floor x y)))))

  ; We now disable floor, so that the linear lemma will be used.

     (in-theory (disable floor))

  ; We create five rewrite rules which we will use during non-linear
  ; arithmetic.  The necessity for these is due to one of the differences in
  ; ACL2's behaviour when non-linear arithmetic is turned on.  Although
  ; the conclusions of linear lemmas have always been rewritten before
  ; they are used, now, when non-linear arithmetic is turned on, the
  ; conclusions are rewritten under a different theory than under ``normal''
  ; rewriting.  This theory is also used in other, similar, circumstances
  ; described below.

     (defthm |arith (* -1 x)|
         (equal (* -1 x)
                (- x)))

     (defthm |arith (* 1 x)|
         (equal (* 1 x)
                (fix x)))

     (defthm |arith (* x (/ x) y)|
         (equal (* x (/ x) y)
                (if (equal (fix x) 0)
                    0
                    (fix y))))

     (defthm |arith (* y x)|
         (equal (* y x)
                (* x y)))

     (defthm |arith (fix x)|
         (implies (acl2-numberp x)
                  (equal (fix x)
                         x))))
   )  ; End skip-proofs.

  ; We disable the above rewrite rules from normal use.

  (in-theory (disable |arith (* -1 x)|
                      |arith (* 1 x)|
                      |arith (* x (/ x) y)|
                      |arith (* y x)|
                      |arith (fix x)|))

  ; We create an arithmetic-theory.  Note that we must give a quoted
  ; constant for the theory ~-[] none of the normal ~ilc[theory-functions]
  ; are applicable to in-arithmetic-theory.

  (in-arithmetic-theory '(|arith (* -1 x)|
                          |arith (* 1 x)|
                          |arith (* x (/ x) y)|
                          |arith (* y x)|
                          |arith (fix x)|))

  ; We turn non-linear arithmetic on.

  (set-non-linearp t)

  ; We can now go ahead and prove our theorem.

  (thm
   (implies (and (rationalp x)
                 (rationalp y)
                 (rationalp z)
                 (< 0 y)
                 (< x (* y z)))
            (< (floor x y) z)))
  ~ev[]

  The above example illustrates the two practical requirements for using
  non-linear arithmetic in ACL2.  First, one must set up an arithmetic-theory.
  Usually, one would not set up an arithmetic-theory on one's own but would
  instead load a library book or books which do so.  Second, one must turn the
  non-linear arithmetic extension on.  This one must do explicitly ~-[] no book
  can do this for you.

  For a brief discussion of why this is so, even though ~c[(set-non-linearp t)]
  is an embeddable event, ~pl[acl2-defaults-table] (in particular, the final
  paragraph).  (Note that ~c[(set-non-linearp t)] modifies the
  ~c[acl2-defaults-table].)  Also ~pl[set-non-linearp],
  ~pl[embedded-event-form], and ~pl[events].

  You can also enable non-linear arithmetic with the hint ~c[:nonlinearp t].
  ~l[hints].  We, in fact, recommend the use of a hint which will enable
  nonlinear arithmetic only when the goal has stabilized under rewriting.
  Using ~ilc[default-hints] can make this easier.

  ~bv[]
  (defun nonlinearp-default-hint (stable-under-simplificationp hist pspv)
    (cond (stable-under-simplificationp
           (if (not (access rewrite-constant
                            (access prove-spec-var pspv :rewrite-constant)
                            :nonlinearp))
               '(:computed-hint-replacement t :nonlinearp t)
             nil))
          ((access rewrite-constant
                   (access prove-spec-var pspv :rewrite-constant)
                   :nonlinearp)
           (if (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE))
               '(:computed-hint-replacement t :nonlinearp nil)
             nil))
          (t nil)))

  (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                                hist pspv)))
  ~ev[]

  This has proven to be a helpful strategy which allows faster proof times.

  We now proceed to briefly describe the theory behind the non-linear extension
  to ACL2.  In ~ilc[linear-arithmetic] it was stated that, ``[L]inear
  polynomial inequalities can be combined by cross-multiplication and addition
  to permit the deduction of a third inequality....''  That is, if
  ~bv[]
  0 < poly1,
  0 < poly2,
  ~ev[]
  and ~c[c] and ~c[d] are positive rational constants, then
  ~bv[]
  0 < c*poly1 + d*poly2.
  ~ev[]

  Similarly, given the above,
  ~bv[]
  0 < poly1*poly2.
  ~ev[]

  In the linear arithmetic case, we are taking advantage of the facts that
  multiplication by a positive rational constant does not change the sign of a
  polynomial and that the sum of two positive polynomials is itself positive.
  In the non-linear arithmetic case, we are using the fact that the product of
  two positive polynomials is itself positive.

  For example, suppose we have the three assumptions:
  ~bv[]
  p1:  3*x*y + 7*a < 4
  p2:            3 < 2*x  or p2': 0 < -3 + 2*x
  p3:            1 < y    or p3': 0 < -1 + y,
  ~ev[]
  and we wish to prove that ~c[a < 0].  As described elsewhere
  (~pl[linear-arithmetic]), we proceed by assuming the negation of our goal:
  ~bv[]
  p4:            0 <= a,
  ~ev[]
  and looking for a contradiction.

  There are no cancellations which can be performed by linear arithmetic in the
  above situation.  (Recall that two polynomials are cancelled against each
  other only when they have the same largest unknown.)  However, ~c[p1] has a
  product as its largest unknown, and for each of the factors of that product
  there is a poly that has that factor as a largest unknown.  When non-linear
  arithmetic is enabled, ACL2 will therefore multiply ~c[p1'] and ~c[p2']
  obtaining
  ~bv[]
  p5:            0 < 3 + -2*x + -3*y + 2*x*y.
  ~ev[]
  The addition of this polynomial will allow cancelation to continue and, in
  this case, we will prove our goal.  Thus, just as ACL2 adds two polynomials
  together when they have the same largest unknown of opposite signs in order
  to create a new ``smaller'' polynomial; so ACL2 multiplies polynomials
  together when the product of their largest unknowns is itself the largest
  unknown of another polynomial.  As the use of ~c[:]~ilc[linear] lemmas to
  further seed the arithmetic data base may allow cancellation to proceed, so
  may the use of non-linear arithmetic.

  This multiplication of polynomials is the motivation for an arithmetic-theory
  distinct from than the normal one.  Because this may be done so often, and
  because the individual factors have presumably already been rewritten, it is
  important that this be done in an efficient way.  The use of a small,
  specialized, theory helps avoid the repeated application of rewrite rules to
  already stabilized terms.~/"

  (declare (ignore obj geneqv ttree)
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
        :obj    nil ; ignored
        :geneqv nil ; ignored
        :ttree  nil ; ignored
        ))))))

(defun add-polys-and-lemmas2-nl (new-vars old-pot-lst ; &extra formals
                                          rdepth step-limit
                                          type-alist obj geneqv wrld state
                                          fnstack
                                          ancestors backchain-limit
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

  (declare (ignore obj geneqv ttree)
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
                 :obj nil
                 :geneqv nil
                 :ttree nil)))))
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
                  (not (flambda-applicationp (car new-vars))))
             (rewrite-entry
              (add-linear-lemmas (car new-vars)
                                 (getprop (ffn-symb (car new-vars))
                                          'linear-lemmas nil
                                          'current-acl2-world wrld))
              :obj nil
              :geneqv nil
              :ttree nil
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
                             :obj nil
                             :geneqv nil
                             :ttree nil
                             :simplify-clause-pot-lst new-pot-lst))))))))))))))

(defun add-polys-and-lemmas1-nl (old-pot-lst cnt ; &extra formals
                                             rdepth step-limit
                                             type-alist obj geneqv wrld state
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

  (declare (ignore obj geneqv ttree)
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
           :obj nil
           :geneqv nil
           :ttree nil)))
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
                       :obj nil
                       :geneqv nil
                       :ttree nil
                       :simplify-clause-pot-lst new-pot-lst1)
                      (cond 
                       (contradictionp (mv step-limit contradictionp nil))
                       (t
                        (rewrite-entry
                         (add-polys-and-lemmas1-nl new-pot-lst1 (1+ cnt))
                         :obj nil
                         :geneqv nil
                         :ttree nil
                         :simplify-clause-pot-lst new-pot-lst2)))))))))))))))

(defun add-polys-and-lemmas1 (new-vars old-pot-lst ; &extra formals
                                       rdepth step-limit
                                       type-alist obj geneqv wrld state fnstack
                                       ancestors
                                       backchain-limit
                                       simplify-clause-pot-lst
                                       rcnst gstack ttree)

; To the simplify-clause-pot-lst, we add lemmas for every var
; in new-vars, generating a new pot-lst.  Then if that new pot-lst has
; new vars in it (relative to old-pot-lst) we repeat for those vars.
; We return the standard contradictionp and a new pot-lst.

  (declare (ignore obj geneqv ttree)
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
                 :obj nil
                 :geneqv nil
                 :ttree nil)))))
    (t (sl-let
        (contradictionp new-pot-lst)
        (cond
         ((flambda-applicationp
           (car new-vars))
          (mv step-limit nil simplify-clause-pot-lst))
         (t
          (rewrite-entry
           (add-linear-lemmas (car new-vars)
                              (getprop
                               (ffn-symb (car new-vars))
                               'linear-lemmas nil
                               'current-acl2-world
                               wrld))
           :obj nil
           :geneqv nil
           :ttree nil)))
        (cond (contradictionp (mv step-limit contradictionp nil))
              (t (rewrite-entry
                  (add-polys-and-lemmas1 (cdr new-vars)
                                         old-pot-lst)
                  :obj nil
                  :geneqv nil
                  :ttree nil
                  :simplify-clause-pot-lst new-pot-lst))))))))

(defun add-polys-and-lemmas (lst disjunctsp ; &extra formals
                                 rdepth step-limit
                                 type-alist obj geneqv wrld state
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

  (declare (ignore obj geneqv ttree)
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
       :obj nil
       :geneqv nil
       :ttree nil
       :simplify-clause-pot-lst new-pot-lst))
     (t
      (rewrite-entry
       (add-polys-and-lemmas1 (new-vars-in-pot-lst new-pot-lst
                                                   simplify-clause-pot-lst
                                                   nil)
                              new-pot-lst)
       :obj nil
       :geneqv nil
       :ttree nil
       :simplify-clause-pot-lst new-pot-lst))))))

(defun add-disjunct-polys-and-lemmas (lst1 lst2 ; &extra formals
                                           rdepth step-limit
                                           type-alist obj geneqv wrld state
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
; of the poly before we added them to te pot-lst.  If lst2 gave a
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

  (declare (ignore obj geneqv ttree)
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
    (rewrite-entry (add-polys-and-lemmas lst1 t)
                   :obj nil
                   :geneqv nil
                   :ttree nil)

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
       :obj nil
       :geneqv nil
       :ttree nil))
     (t

; The first disjunct did not lead to a contradiction.  Perhaps the
; second one will...

      (sl-let
       (contradictionp new-pot-lst2)
       (rewrite-entry
        (add-polys-and-lemmas lst2 t)
        :obj nil
        :geneqv nil
        :ttree nil)
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
                                                 geneqv wrld state
                                                 fnstack ancestors
                                                 backchain-limit
                                                 simplify-clause-pot-lst
                                                 rcnst gstack ttree)

; Each element of split-lst is a doublet, (lst1 lst2).  Logically, we
; wish to conjoin to the simplify-clause-pot-lst the conjunction
; across split-lst of the disjunctions of each lst1 and lst2.  I.e.,
; we wish to assume (and ... (or lst1 lst2) ...) and we wish to
; express this assumption as a pot-lst.  No way Jose.  Pot-lsts
; represent conjunctions of assumptions.  So instead we'll conjoin
; lst1 into the pot list and lst2 into the pot list and hope one or
; the other gives a contradiction.  If not, we'll just discard that
; doublet and try the others.  But if one gives a contradiction, then
; we can go with the assumption of the other as the assumption of
; their disjunction.  There is a subtlety here however: the assumption
; of lst2 in place of (or lst1 lst2) depends upon the refutation of
; lst1 and hence we must infect the polys from lst2 with the ttree
; arising from the refutation of lst1.  And vice versa.  See
; add-disjunct-polys-and-lemma.

; We return two values, the standard contradictionp, and a new
; pot-lst.

; The to-do-later list was first present in Version 1.6, and
; represents an attempt to make the order of the split-lst irrelevant.
; The idea is that if a doublet in the split-lst must be "discarded"
; as noted above, then we actually save that doublet on to-do-later
; and try it again after processing the others.  Here is a long
; message that explains the problem; the message was sent to Bishop
; Brock, who first reported the problem, on March 31, 1994,

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

; The arithmetic hyps are stored in the linear inequalities data base
; by the linear arithmetic package.  That database represents a
; conjunction of inequalities.  The first two inequalities give us

;  0 <= N <= 4

; Now we come to the hard part.  In general, we cannot represent (NOT
; (EQUAL x y)) as a conjunction of inequalities.  It turns into a
; DISjunction, namely, either x < y or y < x.  Thus, if we are asked
; to add (NOT (EQUAL x y)) to the linear data base we try adding x <
; y.  If that gives us a contradiction, then we know y < x and we add
; that.  Alternatively, if x < y doesn't give us a contradiction, but
; y < x does, we can assume x < y.  If neither gives us a
; contradiction, we simply can't represent (NOT (EQUAL x y)) in the
; linear data base.  Note that to get any linear information out of
; (NOT (EQUAL x y)) we must get a contradiction from one of the two
; disjuncts.

; When you process the hypotheses in the "wrong" order, you don't
; always get a contradiction and so we effectively drop one or more of
; the inequalities and lose.

; Consider one of the many "right" orders first, in particular the
; proof that works above.  The first NOT EQUAL we process is (NOT
; (EQUAL N 0)).  Because N is an integer, this is equivalent to either
; N <= -1 or 1 <= N.  The linear data base we have initially is

;  0 <= N <= 4.

; When we add N <= -1 we get a contradiction, by clashing 0 <= N with
; N <= -1 and deriving 0 <= -1.  Since we got a contradiction on one
; disjunct we can assume the other.  Adding 1 <= N to the above data
; base gives us

;  1 <= N <= 4.

; Note that we are now in a position to successfully process (NOT
; (EQUAL N 1)), because it becomes either N <= 0 (contradiction) or 2
; <= N, and thus we get

;  2 <= N <= 4.

; As you can see, we can keep narrowing the known interval as long as
; the hyp we process is beyond the current known endpoints.  We can
; work at either endpoint and so there are many "right" orders.  (In
; the case of the 5-way case split on N=0,1,2,3,4, there are 90 right
; orders and 30 wrong ones out of the 120 permutations.)

; Now consider one of the "wrong" orders.  If we know

;  0 <= N <= 4

; and we first process (NOT (EQUAL N 1)) then we must get a
; contradiction from either N <= 0 or from 2 <f= N.  But neither of
; these is contradictory yet.  So in Version 1.5 (and Nqthm!) we just
; ignore that NOT EQUAL hyp (as far as linear arithmetic is
; concerned).  Once we've ignored any one hyp, the game is lost.

; In Version 1.6 the success of linear is independent of the order in
; which the inequalities are presented.  I do this by keeping a list
; of the ones I had tried to add but couldn't, i.e., the ones that
; Version 1.5 decided to ignore.  Call that list the "to-do-later
; list".  I process all the hyps and get a data base and a to-do-later
; list.  Then I reprocess the to-do-later list and see if any can be
; added now.  I iterate until either I've added them all or no changes
; happen.

; In the case of inequalities about variable symbols this is very very
; fast.  In the case of inequalities about arbitrary terms, e.g., (NOT
; (EQUAL (FOO (BAR X Y)) 2)), it can be slow because every time we add
; an inequality we go look in the :LINEAR lemmas data base for more
; facts about that term.  But I think this problem doesn't arise too
; often and I think we'll find Version 1.6 better than Version 1.5 and
; seldom any slower.

; Thank you very much Bishop for noticing this problem.  It is amazing
; to me that it survived all those years in Nqthm without coming to
; our attention.

  (declare (ignore obj geneqv ttree)
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
    ((null split-lst)
     (cond ((or (equal pot-lst0 simplify-clause-pot-lst)
                (null to-do-later))
            (mv step-limit nil simplify-clause-pot-lst))
           (t (rewrite-entry
               (add-disjuncts-polys-and-lemmas to-do-later nil
                                               simplify-clause-pot-lst)
               :obj nil
               :geneqv nil
               :ttree nil))))
    (t (sl-let (contradictionp new-pot-lst)
               (rewrite-entry
                (add-disjunct-polys-and-lemmas (car (car split-lst))
                                               (cadr (car split-lst)))
                :obj nil
                :geneqv nil
                :ttree nil)
               (cond (contradictionp (mv step-limit contradictionp nil))
                     (t (rewrite-entry
                         (add-disjuncts-polys-and-lemmas
                          (cdr split-lst)
                          (if (equal new-pot-lst simplify-clause-pot-lst)
                              (cons (car split-lst) to-do-later)
                            to-do-later)
                          pot-lst0)
                         :obj nil
                         :geneqv nil
                         :ttree nil
                         :simplify-clause-pot-lst new-pot-lst))))))))

(defun add-terms-and-lemmas (term-lst ttrees positivep
                                      ; &extra formals
                                      rdepth step-limit
                                      type-alist obj geneqv wrld state
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

; This function returns 2 values.  The first indicates that a linear
; contradiction arises from the assumption of term-lst as above.  When non-nil
; the first result is the impossible-poly generated.  Its tag-tree contains all
; the necessary information.  In particular, if a contradiction is indicated
; then there is a proof of NIL from type-alist, the assumption of the terms in
; term-lst (as per positivep), the assumptions in the final tag-tree and some
; subset of the polys in the simplify-clause-pot-lst.

; If no contradiction is indicated then the second value is the new
; simplify-clause-pot-lst.  For each poly p in the new pot list there is a
; proof of p from type-alist, the assumption of the terms in term-lst (as per
; positivep) and the polys in the original pot list.

  (declare (ignore geneqv ttree)
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
      (if (access rewrite-constant rcnst :nonlinearp)

; This call to rewrite-linear-term-lst is new to Version_2.7.
; We wish to be able to have a different normal form when doing
; linear and non-linear arithmetic than when doing normal rewriting.
; The terms in term-lst eventually get passed on to rewrite-linear-term
; where they are rewritten under a possibly changed current-enabled-structure.
; See the comments in cleanse-type-alist for a couple of oddities
; associated with this.

          (rewrite-entry (rewrite-linear-term-lst term-lst ttrees)
                         :obj nil
                         :geneqv nil
                         :ttree nil)
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
              (sl-let (contradictionp basic-pot-lst)
                      (rewrite-entry
                       (add-polys-and-lemmas poly-lst nil)
                       :obj nil
                       :geneqv nil
                       :ttree nil)
                      (cond
                       (contradictionp (mv step-limit contradictionp nil))
                       (t (rewrite-entry
                           (add-disjuncts-polys-and-lemmas
                            split-lst
                            nil
                            basic-pot-lst)
                           :obj nil
                           :geneqv nil
                           :ttree nil
                           :simplify-clause-pot-lst
                           basic-pot-lst)))))))))

(defun rewrite-with-linear (term ; &extra formals
                            rdepth step-limit
                            type-alist obj geneqv wrld state fnstack ancestors
                            backchain-limit
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

  (declare (ignore geneqv)
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
                              :obj nil
                              :geneqv nil
                              :ttree nil)
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

)
