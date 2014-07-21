; ACL2 Version 6.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2014, Regents of the University of Texas

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

;=================================================================

; This file defines the basics of the linear arithmetic decision
; procedure.  We also include clause histories, parent trees,
; tag-trees, and assumptions; all of which are needed by add-poly
; and friends.


;=================================================================

; Clause Histories

; Clauses carry with them their histories, which describe which processes
; have produced them.  A clause history is a list of history-entry records.
; A process, such as simplify-clause, might inspect the history of its
; input clause to help decide whether to perform a certain transformation.

(defrec history-entry

; Important Note: This record is laid out this way so that we can use
; assoc-eq on histories to detect the presence of a history-entry for
; a given processor.  Do not move the processor field!

  (processor ttree clause signal . cl-id)
  t)

; Processor is a waterfall processor (e.g., 'simplify-clause).  The
; ttree and signal are, respectively, the ttree and signal produced by
; the processor on clause.  Each history-entry is built in the
; waterfall, but we inspect them for the first time in this file.

;=================================================================

; Essay on Parent Trees

; Structurally, a "parent tree" or pt is either nil, a number, or the cons
; of two parent trees.  Parent trees are used to represent sets of
; literals.  In particular, every number in a pt is the position of some
; literal in the current-clause variable of simplify-clause1 and the tree
; may be thought of as representing that set of literals.  Pts are used
; to avoid tail biting.  An earlier implementation of this used "clause-tails."
; We explain everything below.

; "Tail biting" is our name for the insidious phenomenon that occurs when
; one assumes p false while trying to prove p and then, carelessly,
; rewrites the goal p to false on the basis of that assumption.  Observe
; that this is sound but detrimental to success.  One way to prevent
; tail biting is to not assume p false while trying to prove it, but we
; found that too weak.  The way we avoid tail biting is to keep careful
; track of what we're trying to prove, which literal we are working on,
; and what assumptions have been used to derive what results; we never use
; the assumption that p is false (or anything derived from it) to rewrite
; p to false.  Despite our efforts, tail biting by simplify-clause is
; possible.  See "On Tail Biting by Simplify-clause" for more.

; The easiest to understand use of parent trees in this regard is in
; linear arithmetic.  In simplify-clause1 we setup the
; simplify-clause-pot-lst, by expressing all the arithmetic hypotheses of
; the conjecture as polynomial inequalities.  When new inequalities are
; introduced, as when trying to relieve the hypothesis of some rule, we
; can combine them with the preprocessed "polys" to quickly settle certain
; arithmetic statements.  To avoid duplication of effort, our
; simplify-clause-pot-lst contains polys derived from all possible
; literals of the current clause.  This is because a great deal of work
; may be done (via linear lemmas and rewriting) to derive a poly about a
; given suggestive subterm of a given literal and we do not want to do it
; each time we assume that literal false.  Note the ease with which we
; could bite our tail: the list of inequalities is derived from the
; negations of every literal so we might easily use an inequality to
; falsify the literal from which it was derived.  To avoid this, each poly
; is tagged with one or more parent trees.  Intuitively the poly derived
; from an inequality literal is tagged with that literal.  But other
; literals may have been used, e.g., to establish certain terms rational,
; so one must think of the polys as being tagged with sets of literals.
; Then, when we are rewriting a particular literal we tell ourselves (by
; making a note in the :pt field of the rcnst) to avoid any poly
; descending from the goal literal.  Similar use is made of parent trees
; in the fc-pair-lst -- a list of preprocessed conclusions obtained by
; forward chaining from the current clause.

; The problem is made subtle by the fact that the literals we are
; rewriting change before we get to them and thus cannot be recognized by
; their structure alone.  Consider the clause {lit1 lit2 lit3}.  Now
; suppose we forward chain from ~lit3 and deduce concl.  Then fc-pair-lst
; will contain (concl . ttree) where ttree contains a parent tree
; acknowledging our dependence on lit3.  We may thus use concl when we are
; working on lit1 and lit2.  But suppose that in simplifying lit1 we
; produce the literal (not (equal var 27)).  Then we can substitute 27 for
; var everywhere and will actually do so.  Thus, by the time we get to
; work on the third literal of the clause above it will not be lit3 but
; some reduced instance, lit3', of lit3.  If the parent tree literally
; contained lit3, it would be impossible to recognize that concl was to be
; avoided.

; Therefore, we actually refer to literals by their position in the
; current-clause of simplify-clause1 (from which the preprocessing was
; done) and we keep careful track as we simplify what the original pt for
; each literal was.  As we scan over the literals to simplify we maintain
; a map, an enumeration of pts, giving the pt for each literal.  Thus,
; while we actually go to work on lit3' above, we will actually have in
; our hand the fact that lit3 is its parent.  Keeping track of the parents
; of the literals we are working on is made harder by the fact that
; sometimes literal merge.  For example, in {lit1 lit2 lit3} lit1 may
; simplify to lit3 and thus we may merge them.  The surviving literal is
; given the parent tree that contains both 1 and 3 so we know not to use
; conclusions derived from either.  The rewrite-constant, rcnst, in use
; below simplify-clause1 contains as one of its fields the
; :current-clause.  Thus, given the rewrite-constant and a pt it is
; possible to recover the original parent literals.

; We generally use "pt" to refer to a single parent tree.  "Pts" is a list
; of parent trees, implicitly in "weak 1:1 correspondence" with some list
; of terms.  By "weak" we mean pts may be shorter than the list of terms
; and "excess terms" have the nil pt.  That is, it is ok to cdr pts as you
; cdr down the list of terms and every time you need a pt for a term you
; take the car of pts.  There is no need to store the nil pt in tag-trees,
; so we don't.  Thus, a commonly used convention is to supply a pts of nil
; to a function that stores 'pts, causing it to store no pts.

; In the early days we did not use parent trees but "clause-tails" -- the
; tail of clause starting with the parent literal.  This was adopted to
; avoid the confusion caused by duplicate literals.  But it was rendered
; unworkable when we implemented the Satriani hacks and started
; substituting for variables as we went.  It also suffered other problems
; due to sloppy implementation.

(defun pt-occur (n pt)

; Determine whether n occurs in the set denoted by pt.

  (cond ((null pt) nil)
        ((consp pt) (or (pt-occur n (car pt)) (pt-occur n (cdr pt))))
        (t (= n pt))))

(defun pt-intersectp (pt1 pt2)

; Determine whether the intersection of the sets denoted by pt1 and pt2
; is nonempty.

  (cond ((null pt1) nil)
        ((consp pt1)
         (or (pt-intersectp (car pt1) pt2)
             (pt-intersectp (cdr pt1) pt2)))
        (t (pt-occur pt1 pt2))))


(defun pts-to-ttree-lst (pts)
  (cond ((null pts) nil)
        (t (cons (add-to-tag-tree! 'pt (car pts) nil)
                 (pts-to-ttree-lst (cdr pts))))))

; Previously, we stored the parents of a poly in the poly's :ttree field
; and used to-be-ignoredp.  However, tests have shown that under certain
; conditions to-be-ignoredp was taking up to 80% of the time spent by
; add-poly.  We now store the poly's parents in a seperate field and
; use ignore-polyp.  The next few functions are used in the implementation
; of this change.

(defun marry-parents (parents1 parents2)

; We return the 'eql union of the two arguments.  When we create a
; new poly from two other polys via cancellation, we need to ensure
; that the new poly depends on all the literals that either of the
; others do.

  (if (null parents1)
      parents2
    (marry-parents (cdr parents1)
                   (add-to-set-eql (car parents1) parents2))))

(defun collect-parents1 (pt ans)
  (cond ((null pt)
         ans)
        ((consp pt)
         (collect-parents1 (car pt)
                           (collect-parents1 (cdr pt) ans)))
        (t
         (add-to-set-eql pt ans))))

(defun collect-parents0 (pts ans)
  (cond
   ((null pts) ans)
   (t
    (collect-parents0 (cdr pts)
                      (collect-parents1 (car pts) ans)))))

(defun collect-parents (ttree)

; We accumulate in reverse order all the objects (parents) in the pts in the
; ttree.  When we create a new poly via linearize, we extract a list of all its
; parents from the poly's 'ttree and store this list in the poly's 'parents
; field.  This function does the extracting.

  (collect-parents0 (tagged-objects 'pt ttree) nil))

(defun ignore-polyp (parents pt)

; Consider the set, P, of all parents mentioned in the list parents.
; Consider the set, B, of all parents mentioned in the parent tree pt.  We
; return t iff P and B have a non-empty intersection.  From a more applied
; perspective, assuming parents is the parents list associated with some
; poly, P is the set of literals upon which the poly depends.  B is
; generally the set of literals we are to avoid dependence upon.  The poly
; should be ignored if it depends on some literal we are to avoid.

  (if (null parents)
      nil
    (or (pt-occur (car parents) pt)
        (ignore-polyp (cdr parents) pt))))

(defun to-be-ignoredp1 (pts pt)
  (cond ((endp pts) nil)
        (t (or (pt-intersectp (car pts) pt)
               (to-be-ignoredp1 (cdr pts) pt)))))

(defun to-be-ignoredp (ttree pt)

; Consider the set, P, of all parents mentioned in the 'pt tags of ttree.
; Consider the set, B, of all parents mentioned in the parent tree pt.  We
; return t iff P and B have a non-empty intersection.  From a more applied
; perspective, assuming ttree is the tree associated with some poly, P is the
; set of literals upon which the poly depends.  B is generally the set of
; literals we are to avoid dependence upon.  The poly should be ignored if it
; depends on some literal we are to avoid.

; This function was originally written to do the job described above.  But then
; Robert Krug suggested the efficiency of maintaining the parents list and
; introduced ignore-polyp.  Now this function is only used elsewhere, but the
; above comments still apply mutatis mutandis.

  (to-be-ignoredp1 (tagged-objects 'pt ttree) pt))


;=================================================================


; Assumptions

; We are prepared to force assumptions of certain terms by adding
; them to the tag-tree under the 'assumption tag.  This is always done
; via force-assumption.  All assumptions are embedded in an
; assumption record:

(defrec assumnote (cl-id rune . target) t)

; The cl-id is the clause id (as maintained by the waterfall) of the clause
; currently being worked upon.  Rune is either the rune (or a symbol, as per
; force-assumption) that forced this assumption.  Target is the term to which
; rune was being applied.  Because the :assumnotes field of an assumption is
; always non-nil, there is at least one assumnote in it, but the cl-id field in
; that assumnote might be nil because we do not know the clause id just yet.
; We fill in the :cl-id field later so that we don't have to pass such static
; information all the way down to the places where assumptions are forced.
; When an assumption is generated, it has exactly one assumnote.  But later we
; will "merge" assumptions together (actually, delete some via subsumption) and
; when we do we will union the assumnotes together to keep track of why we are
; dealing with that assumption.

(defrec assumption
  ((type-alist . term) immediatep rewrittenp . assumnotes)
  t)

; An assumption record records the fact that we must prove term under
; the assumption of type-alist.  Immediatep indicates whether it is
; the user's desire to split the main goal on term immediately
; (immediatep = 'case-split), prove the term under alist immediately
; (t) or delay the proof to a forcing round (nil).

; WARNING: The system can be unsound if immediatep takes on any but
; these three values.  In functions like collect-assumptions we assume
; that collecting all the 'case-splits and then collecting all the t's
; gets all the non-nils!

; Assumnotes is involved with explaining to the user what we are doing.  It is
; a non-empty list of assumnote records.

; We now turn to the question of whether term has been rewritten or not.  If it
; has not been, and we know the context in which rewriting should be tried, it
; is presumably a good idea to try to rewrite term before we try a full-fledged
; proof: a proof requires converting the type-alist and term into a clause and
; then simplifying all the literals of that clause, whereas we expect many
; times that the type-alist will allow term to rewrite to t.  One might ask why
; we don't always rewrite before forcing.  The answer is simple: type-set
; forces and cannot use the rewriter because it is defined well before the
; rewriter.  So type-set forces unrewritten terms often.  The problem with the
; simple idea of trying first to prove those terms by rewriting is that REWRITE
; takes many additional context-specifying arguments, the most complicated
; being the simplify-clause-pot-lst.  Having set the stage for an explanation,
; we now give it:

; Rewrittenp indicates whether we have already tried to rewrite term.  Recall
; that relieve-hyp first rewrites and forces the rewritten term only if
; rewriting fails.  Thus, at least within the rewriter, we will see both
; rewritten and unrewritten assumptions coming back in the ttrees we generate.
; Rewrittenp is either a term or nil.  If it is a term, forced-term, then it is
; the term we were asked to force and term is the result of rewriting
; forced-term.  We use the unrewritten term in a heuristic that sometimes
; throws out supposedly irrelevant hypotheses from the clauses we ultimately
; prove to establish the assumptions.  See the discussion of "disguarding."  If
; rewrittenp is nil, we have not yet tried to rewrite term and term is
; literally what was forced.  The simplifier will collect the unrewritten
; assumptions generated during rewrite and will rewrite them in the
; "appropriate context" as discussed below.

; The view we take is that from within the rewriter, all assumptions are
; rewritten before being forced.  That cannot be implemented directly, so
; we do it cleverly, by rewriting them after the force but not telling
; the user.  It just seems like a good idea for the rewriter, of all the
; processes, to produce only rewritten assumptions.  Now those rewritten
; assumptions aren't maximally rewritten.  For example, an assumption
; might rewrite to an if and normalization etc. might produce a provable
; set of assumptions.  But we do not use normalization or clausification on
; assumptions until it is time to hit them with the full prover.

; The following record definition is decidedly out of place, belonging as it
; does to the code for forward-chaining.  But we must make it now to allow
; us to define contain-assumptionp.  This record is documented in comments
; in the essay entitled:  "Forward Chaining Derivations - fc-derivation - fcd"

(defrec fc-derivation
  (((concl . ttree) . (fn-cnt . p-fn-cnt))
   .
   ((inst-trigger . rune) . (fc-round . unify-subst)))
  t)

; WARNING: If you change fc-derivation, go visit the "virtual" declaration of
; the record in simplify.lisp and update the comments.  See the essay "Forward
; Chaining Derivations - fc-derivation - fcd".

(mutual-recursion

(defun contains-assumptionp (ttree)

; We return t iff ttree contains an assumption "at some level" where we
; know that 'fc-derivations contain ttrees that may contain assumptions.
; See the discussion in force-assumption.

  (or (tagged-objectsp 'assumption ttree)
      (contains-assumptionp-fc-derivations
       (tagged-objects 'fc-derivation ttree))))

(defun contains-assumptionp-fc-derivations (lst)
  (cond ((endp lst) nil)
        (t (or (contains-assumptionp (access fc-derivation (car lst) :ttree))
               (contains-assumptionp-fc-derivations (cdr lst))))))
)

(defun remove-assumption-entries-from-type-alist (type-alist)

; We delete from type-alist any entry, (term ts . ttree), whose ttree contains
; an assumption.  Thus, if ttree2 below is the
; only one of the three to contain an assumption, the type-alist
; ((v1 ts1 . ttree1)(v2 ts2 . ttree2)(v3 ts3 . ttree3))
; is transformed into
; ((v1 ts1 . ttree1)(v3 ts3 . ttree3)).

; It is always sound to delete a hypothesis.  See the discussion in
; force-assumption.

  (cond
   ((endp type-alist) nil)
   ((contains-assumptionp (cddar type-alist))
    (remove-assumption-entries-from-type-alist (cdr type-alist)))
   (t (cons (car type-alist)
            (remove-assumption-entries-from-type-alist (cdr type-alist))))))

(defun force-assumption1
  (rune target term type-alist rewrittenp immediatep ttree)

  (let* ((term (cond ((equal term *nil*)
                      (er hard 'force-assumption
                          "Attempt to force nil!"))
                     ((null rune)
                      (er hard 'force-assumption
                          "Attempt to force the nil rune!"))
                     (t term))))
    (cond ((not (member-eq immediatep '(t nil case-split)))
           (er hard 'force-assumption1
               "The :immediatep of an ASSUMPTION record must be ~
                t, nil, or 'case-split, but we have tried to create ~
                one with ~x0."
               immediatep))
          (t
           (add-to-tag-tree 'assumption
                            (make assumption
                                  :type-alist type-alist
                                  :term term
                                  :rewrittenp rewrittenp
                                  :immediatep immediatep
                                  :assumnotes
                                  (list (make assumnote
                                              :cl-id nil
                                              :rune rune
                                              :target target)))
                            ttree)))))


(defconst *force-xrune*
  '(:EXECUTABLE-COUNTERPART FORCE))

(defun force-assumption
  (rune target term type-alist rewrittenp immediatep force-flg ttree)

; Warning:  Rune may not be a rune!  It may be a function symbol.

; This function adds (implies type-alist' term) as an 'assumption to ttree.
; Rewrittenp is either nil, meaning term has not yet been rewritten, or is the
; term that was rewritten to obtain term.  Rune is the name of the rule in
; whose behalf term is being assumed, and rune is being applied to the target
; term target.  If rune is a symbol then it is actually a primitive
; function symbol and this is a split on the guard of that symbol.  There is
; even an exception to that: sometimes rune is the function symbol equal.  But
; the guard of equal is t and so is never forced!  What is going on?  In
; linearize we force term2 to be real if term1 is real and we are
; linearizing (equal term1 term2).

; The type-alist actually stored in the assumption record, type-alist', is not
; type-alist!  We remove from type-alist all the entries depending upon
; assumptions.  It is legitimate to throw away any hypothesis, thus we can
; delete the entries we choose.  Why do we throw out the type-alist entries
; depending on assumptions?  The reason is that in the forcing round we
; actually generate a formula representing (implies type-alist' term) and this
; formula does not encode the fact that a given hyp depends upon certain
; assumptions.

; Because assumptions can be generated during forward chaining, the type-alist
; may contain 'fc-derivations tags among its ttrees.  These records record how
; a given hypothesis was derived and may itself have 'assumptions in its ttree.
; We therefore consider a ttree to "contain assumptions" if it contains an
; fc-derivation that contains assumptions.

; It could be thought that the creation of type-alist' from type-alist is
; merely an efficiency aimed at saving a few conses.  This is not correct.
; This change has a dramatic effect on the size of our ttrees.  Before we did
; this, it was possible for a ttree to contain an assumption which (by virtue
; of the :type-alist) contained a ttree which contained an assumption which
; contained a ttree, etc.  We have seen this sort of thing nested to depth 9.
; Furthermore, it was frequently the case that a ttree contained some proper
; subttree x which occurred also in an assumption contained in the parent
; ttree.  Thus, the ttree x was duplicated.  While the parent ttree was small
; (in the sense that it contained on a few nodes) the tree was very large when
; printed, because of this duplication.  We have seen a ttree that contained 5
; million nodes (when explored in this root-and-branch way through 'assumptions
; and 'fc-derivations) but which actually was composed of only 100 distinct
; (non-equal) subtrees.  Again, one might think this was a problem only if one
; printed out the ttree, but some processes, such as expunge-fc-derivations, do
; root-and-branch exploration.  On the tree in question the system simply hung
; up and appeared to be in an infinite loop.  This fix keeps ttrees small (even
; when viewed in the root-and-branch way) and is crucial to our practice of
; using them.

; Once upon a time, we allowed rune to be nil.  We have since changed that and
; now use the *fake-rune-for-anonymous-enabled-rule* when we don't know a
; better rune.  But we have put a check in here to make sure no one uses the
; nil "rune" anymore.  Wanting a genuine rune here is just a reflection of the
; output routine that explains the origins of each forcing round.

; Force-flg is known to be non-nil; it may be either t or 'weak.  It's tempting
; to allow force-flg = nil and handle that case here (trivially), but the case
; structure in functions like type-set-binary-+ suggests that it's better to
; deal with that case up front, in order to avoid lots of tests that are
; irrelevant (since the same trivial thing happens in all cases when force-flg
; is nil).

; This function is a No-Change Loser, meaning that if it fails and returns nil
; as its first result, it returns the unmodified ttree as its second.  Note
; that either force-flg or nil is returned as the first argument; hence, a
; "successful" force with force-flg = 'weak will result in an unchanged
; force-flg being returned.  If the first value returned is nil, we are to
; pretend that we weren't allowed to force in the first place.

; At the time of this writing we have temporarily abandoned the idea of
; allowing force-flg to be 'weak:  it will always be t or nil.  See the comment
; in ok-to-force.

  (let ((type-alist (remove-assumption-entries-from-type-alist type-alist))
        (ttree (push-lemma *force-xrune* ttree)))
    (cond
     ((not force-flg)
      (mv force-flg
          (er hard 'force-assumption
              "Force-assumption called with null force-flg!")))

; We experimented with allowing force-flg to be 'weak.  However, currently
; force-flg is known to be t or nil.  See the comment in ok-to-force.

;    ((or (eq force-flg t)
;         (all-dumb-occur-in-type-alist (all-vars term) type-alist))
;     (mv force-flg
;         (force-assumption1
;          rune target term type-alist rewrittenp immediatep ttree)))
;    (t
;     (mv nil ttree))

     (t (mv force-flg
            (force-assumption1
             rune target term type-alist rewrittenp immediatep ttree))))))

(defun tag-tree-occur-assumption-nil-1 (lst)
  (cond ((endp lst) nil)
        ((equal (access assumption (car lst) :term)
                *nil*)
         t)
        (t (tag-tree-occur-assumption-nil-1 (cdr lst)))))

(defun tag-tree-occur-assumption-nil (ttree)

; This is just (tag-tree-occur 'assumption <*nil*> ttree) where by <*nil*> we
; mean any assumption record with :term *nil*.

  (tag-tree-occur-assumption-nil-1 (tagged-objects 'assumption ttree)))

(defun assumption-free-ttreep (ttree)

; This is a predicate that returns t if ttree contains no 'assumption tag.  It
; also checks for 'fc-derivation tags, since they could hide 'assumptions.  An
; error-causing version of this function is chk-assumption-free-ttree.  Keep
; these two in sync.

; This check is stronger than necessary, of course, since an fc-derivation
; object need not contain an assumption.  See also contains-assumptionp (and
; chk-assumption-free-ttree-1) for a slightly more expensive, but more precise,
; check.

  (cond ((tagged-objectsp 'assumption ttree) nil)
        ((tagged-objectsp 'fc-derivation ttree) nil)
        (t t)))

; The following assumption is impossible to satisfy and is used as a marker
; that we sometimes put into a ttree to indicate to our caller that the
; attempted force should be abandoned.

(defconst *impossible-assumption*
  (make assumption
        :type-alist nil
        :term *nil*
        :rewrittenp *nil*
        :immediatep nil ; must be t, nil, or 'case-split
        :assumnotes (list (make assumnote
                                :cl-id nil
                                :rune *fake-rune-for-anonymous-enabled-rule*
                                :target *nil*))))


;=================================================================


; We are about to get into the linear arithmetic stuff quite heavily.
; This code started in Nqthm in 1979 and migrated more or less
; untouched into ACL2, with the exception of the addition of the
; rationals.  However, around 1998, Robert Krug began working on an
; improved arithmetic book and after a year or so realized he wanted
; to make serious changes in the linear arithmetic procedures.
; Robert's hand is now felt all over this code.


; Essay on the Logical Basis for Linear Arithmetic.

; This essay was written for some early version of ACL2.  It still
; applies to the linear arithmetic decision procedure as of Version_2.7,
; although some of the details may need revision.

; We list here the "algebraic laws" we assume.  We point back to this
; list from the places we assume them.  It is crucial to realize that
; by < and + here we do not mean the familiar "guarded" functions of
; Common Lisp and algebra, but rather the "completed" functions of the
; ACL2 logic.  In particular, nonnumeric arguments to + are defaulted
; to 0 and complex numbers may be added to rational ones to yield
; complex ones, etc.  The < relation coerces nonnumeric arguments to 0
; and then compares the resulting numbers lexicographically on the
; real and imaginary parts, using the familiar less-than relation on
; the rationals.

; Let us use << as the "familiar" less-than.  Then
; (< x y) = (let ((x1 (if (acl2-numberp x) x 0))
;                 (y1 (if (acl2-numberp y) y 0)))
;            (or (<< (realpart x1) (realpart y1))
;                (and (= (realpart x1) (realpart y1))
;                     (<< (imagpart x1) (imagpart y1)))))

; The wonderful thing about this definition, is that it enjoys the algebraic
; laws we need to support linear arithmetic.  The "box" below contains the
; complete listing of the algegraic laws supporting linear arithmetic
; ("alsla").

; However, interspersed around them in the box are some events that ACL2's
; completed < and + have the ALSLA properties.  To enable us to use the theorem
; prover, we define some new symbols like < and + and prove that those symbols
; have the desired properties.  This is a bit tricky because the completed <
; and + must be defined in terms of the partial < and + which work on the
; rationals and complexes, respectively, and we do not want to rely on any
; built in properties of those primitive symbols.

; Therefore, we constrain three new symbols, PLUS, TIMES, and LESSP which you
; may think of as being the familiar, partial versions of +, *, and <.
; (Indeed, the witnesses in the constraints are those primitives.  The
; encapsulate below merely exports the properties that we are going to assume.)
; Then we define completed versions of these functions, called CPLUS, CTIMES,
; and CLESSP and we prove the ALSLA properties of those functions.

; Note: This exercise is still suspicious because it involves equality
; goals between arithmetic terms and there is no reason to believe that our
; "untrusted" linear arithmetic isn't contributing to their proof.  Well, a
; search through the output produces no sign of "linear" after the
; encapsulation below, but that could indicate an io bug.  A more convincing
; proof would be to eliminate the use of the arithmetic data types altogether
; but that would be a little nasty, faking rationals and complexes.  A still
; more convincing proof would be to construct the proof formally, as we hope to
; do when we have proof objects.

; (progn
;
; ; Perhaps this axiom can be proved from given ones, but I haven't taken the
; ; time to work it out.  I will add it.  I believe it!
;
; (defaxiom *-preserves-<
;   (implies (and (rationalp c)
;                 (rationalp x)
;                 (rationalp y)
;                 (< 0 c))
;            (equal (< (* c x) (* c y))
;                   (< x y))))
;
; (defthm realpart-rational
;   (implies (rationalp x) (equal (realpart x) x)))
;
; (defthm imagpart-rational
;   (implies (rationalp x) (equal (imagpart x) 0)))
;
; (encapsulate (((plus * *) => *)
;               ((times * *) => *)
;               ((lessp * *) => *))
;
; ; Plus and lessp here are the rational versions of those functions.  They are
; ; intended to be the believable, intuitive, functions.  You should read the
; ; properties we export to make sure you believe that the high school plus and
; ; lessp have those properties.  We prove the properties, but we prove them from
; ; witnesses of plus and lessp that are ACL2's completed + and < supported by
; ; ACL2's linear arithmetic and hence, if the soundness of ACL2's arithmetic is
; ; in doubt, as it is in this exercise, then no assurrance can be drawn from the
; ; constructive nature of this axiomatization of rational arithmetic.
;
;              (local (defun plus (x y)
;                       (declare (xargs :verify-guards nil))
;                       (+ x y)))
;              (local (defun times (x y)
;                       (declare (xargs :verify-guards nil))
;                       (* x y)))
;              (local (defun lessp (x y)
;                       (declare (xargs :verify-guards nil))
;                       (< x y)))
;              (defthm rationalp-plus
;                (implies (and (rationalp x)
;                              (rationalp y))
;                         (rationalp (plus x y)))
;                :rule-classes (:rewrite :type-prescription))
;              (defthm plus-0
;                (implies (rationalp x)
;                         (equal (plus 0 x) x)))
;              (defthm plus-commutative-and-associative
;                (and (implies (and (rationalp x)
;                                   (rationalp y))
;                              (equal (plus x y) (plus y x)))
;                     (implies (and (rationalp x)
;                                   (rationalp y)
;                                   (rationalp z))
;                              (equal (plus x (plus y z))
;                                     (plus y (plus x z))))
;                     (implies (and (rationalp x)
;                                   (rationalp y)
;                                   (rationalp z))
;                              (equal (plus (plus x y) z)
;                                     (plus x (plus y z))))))
;              (defthm rationalp-times
;                (implies (and (rationalp x)
;                              (rationalp y))
;                         (rationalp (times x y))))
;              (defthm times-commutative-and-associative
;                (and (implies (and (rationalp x)
;                                   (rationalp y))
;                              (equal (times x y) (times y x)))
;                     (implies (and (rationalp x)
;                                   (rationalp y)
;                                   (rationalp z))
;                              (equal (times x (times y z))
;                                     (times y (times x z))))
;                     (implies (and (rationalp x)
;                                   (rationalp y)
;                                   (rationalp z))
;                              (equal (times (times x y) z)
;                                     (times x (times y z)))))
;                :hints
;                (("Subgoal 2"
;                  :use ((:instance associativity-of-*)
;                        (:instance commutativity-of-* (x x)(y (* y z)))))))
;              (defthm times-distributivity
;                (implies (and (rationalp x)
;                              (rationalp y)
;                              (rationalp z))
;                         (equal (times x (plus y z))
;                                (plus (times x y) (times x z)))))
;              (defthm times-0
;                (implies (rationalp x)
;                         (equal (times 0 x) 0)))
;              (defthm times-1
;                (implies (rationalp x)
;                         (equal (times 1 x) x)))
;              (defthm plus-inverse
;                (implies (rationalp x)
;                         (equal (plus x (times -1 x)) 0))
;                :hints
;                (("Goal"
;                  :use ((:theorem (implies (rationalp x)
;                                           (not (< 0 (+ x (* -1 x))))))
;                        (:theorem (implies (rationalp x)
;                                           (not (< (+ x (* -1 x)) 0))))))))
;              (defthm plus-inverse-unique
;                (implies (and (rationalp x)
;                              (rationalp y)
;                              (equal (plus x (times -1 y)) 0))
;                         (equal x y))
;                :rule-classes nil)
;              (defthm lessp-irreflexivity
;                (implies (rationalp x)
;                         (not (lessp x x))))
;              (defthm lessp-antisymmetry
;                (implies (and (rationalp x)
;                              (rationalp y)
;                              (lessp x y))
;                         (not (lessp y x))))
;              (defthm lessp-trichotomy
;                (implies (and (rationalp x)
;                              (rationalp y)
;                              (not (equal x y))
;                              (not (lessp x y)))
;                         (lessp y x)))
;              (defthm lessp-plus
;                (implies (and (rationalp x)
;                              (rationalp y)
;                              (rationalp u)
;                              (rationalp v)
;                              (lessp x y)
;                              (not (lessp v u)))
;                         (lessp (plus x u) (plus y v))))
;              (defthm not-lessp-plus
;                (implies (and (rationalp x)
;                              (rationalp y)
;                              (rationalp u)
;                              (rationalp v)
;                              (not (lessp y x))
;                              (not (lessp v u)))
;                         (not (lessp (plus y v) (plus x u)))))
;              (defthm 1+trick-for-lessp
;                (implies (and (integerp x)
;                              (integerp y)
;                              (lessp x y))
;                         (not (lessp y (plus 1 x)))))
;              (defthm times-positive-preserves-lessp
;                (implies (and (rationalp c)
;                              (rationalp x)
;                              (rationalp y)
;                              (lessp 0 c))
;                         (equal (lessp (times c x) (times c y))
;                                (lessp x y)))))
;
; ; Now we "complete" +, *, <, and <= to the complex rationals and thence to the
; ; entire universe.  The results are CPLUS, CTIMES, CLESSP, and CLESSEQP.  You
; ; should buy into the claim that these functions are what we intended in ACL2's
; ; completed arithmetic.
;
; ; Note: At first sight it seems odd to do it this way.  Why not just assume
; ; plus, above, is the familiar operation on the complex rationals?  We tried
; ; it and it didn't work very well, because ACL2 does not reason very well
; ; about complex arithmetic.  It seemed more direct to make the definition of
; ; complex addition and multiplication be explicit for the purposes of this
; ; proof.
;
; (defun cplus (x y)
;   (declare (xargs :verify-guards nil))
;   (let ((x1 (fix x))
;         (y1 (fix y)))
;     (complex (plus (realpart x1) (realpart y1))
;              (plus (imagpart x1) (imagpart y1)))))
;
; (defun ctimes (x y)
;   (declare (xargs :verify-guards nil))
;   (let ((x1 (fix x))
;         (y1 (fix y)))
;     (complex (plus (times (realpart x1) (realpart y1))
;                    (times -1 (times (imagpart x1) (imagpart y1))))
;              (plus (times (realpart x1) (imagpart y1))
;                    (times (imagpart x1) (realpart y1))))))
;
; (defun clessp (x y)
;   (declare (xargs :verify-guards nil))
;   (let ((x1 (fix x))
;         (y1 (fix y)))
;     (or (lessp (realpart x1) (realpart y1))
;         (and (equal (realpart x1) (realpart y1))
;              (lessp (imagpart x1) (imagpart y1))))))
;
; (defun clesseqp (x y)
;   (declare (xargs :verify-guards nil))
;   (not (clessp y x)))
;
; ; A trivial theorem about fix, allowing us hereafter to disable it.
;
; (defthm fix-id (implies (acl2-numberp x) (equal (fix x) x)))
;
; (in-theory (disable fix))
;
; ;-----------------------------------------------------------------------------
; ; The Algebraic Laws Supporting Linear Arithmetic (ALSLA)
;
; ; All the operators FIX their arguments
; ; (equal (+ x y) (+ (fix x) (fix y)))
; ; (equal (* x y) (* (fix x) (fix y)))
; ; (equal (< x y) (< (fix x) (fix y)))
; ; (fix x) = (if (acl2-numberp x) x 0)
;
; (defthm operators-fix-their-arguments
;   (and (equal (cplus x y) (cplus (fix x) (fix y)))
;        (equal (ctimes x y) (ctimes (fix x) (fix y)))
;        (equal (clessp x y) (clessp (fix x) (fix y)))
;        (equal (fix x) (if (acl2-numberp x) x 0)))
;   :rule-classes nil
;   :hints (("Subgoal 1" :in-theory (enable fix))))
;
; ; + Associativity, Commutativity, and Zero
; ; (equal (+ (+ x y) z) (+ x (+ y z)))
; ; (equal (+ x y) (+ y x))
; ; (equal (+ 0 y) (fix y))
;
; (defthm cplus-associativity-etc
;   (and (equal (cplus (cplus x y) z) (cplus x (cplus y z)))
;        (equal (cplus x y) (cplus y x))
;        (equal (cplus 0 y) (fix y))))
;
; ; * Distributes Over +
; ; (equal (+ (* c x) (* d x)) (* (+ c d) x))
;
; (defthm ctimes-distributivity
;   (equal (cplus (ctimes c x) (ctimes d x)) (ctimes (cplus c d) x)))
;
; ; * Associativity, Commutativity, Zero and One
; ; (equal (* (* x y) z) (* x (* y z)))   ; See note below
; ; (equal (* x y) (* y x))
; ; (equal (* 0 x) 0)
; ; (equal (* 1 x) (fix x))
;
; (defthm ctimes-associativity-etc
;   (and (equal (ctimes (ctimes x y) z) (ctimes x (ctimes y z)))
;        (equal (ctimes x y) (ctimes y x))
;        (equal (ctimes 0 y) 0)
;        (equal (ctimes 1 x) (fix x))))
;
; ; + Inverse
; ; (equal (+ x (* -1 x)) 0)
;
; (defthm cplus-inverse
;   (equal (cplus x (ctimes -1 x)) 0))
;
; ; Reflexivity of <=
; ; (<= x x)
;
; (defthm clesseqp-reflexivity
;   (clesseqp x x))
;
; ; Antisymmetry
; ; (implies (< x y) (not (< y x)))   ; (implies (< x y) (<= x y))
;
; (defthm clessp-antisymmetry
;   (implies (clessp x y)
;            (not (clessp y x))))
;
; ; Trichotomy
; ; (implies (and (acl2-numberp x)
; ;               (acl2-numberp y))
; ;          (or (< x y)
; ;              (< y x)
; ;              (equal x y)))
;
; (defthm clessp-trichotomy
;   (implies (and (acl2-numberp x)
;                 (acl2-numberp y))
;            (or (clessp x y)
;                (clessp y x)
;                (equal x y)))
;   :rule-classes nil)
;
; ; Additive Properties of < and <=
; ; (implies (and (<  x y) (<= u v)) (<  (+ x u) (+ y v)))
; ; (implies (and (<= x y) (<= u v)) (<= (+ x u) (+ y v)))
;
; ; We have to prove three lemmas first.  But then we nail these suckers!
;
;  (defthm not-lessp-plus-instance-u=v
;    (implies (and (rationalp x)
;                  (rationalp y)
;                  (rationalp u)
;                  (not (lessp y x)))
;             (not (lessp (plus y u) (plus x u)))))
;
;  (defthm lessp-plus-commuted1
;    (implies (and (rationalp x)
;                  (rationalp y)
;                  (rationalp u)
;                  (rationalp v)
;                  (lessp x y)
;                  (not (lessp v u)))
;             (lessp (plus u x) (plus v y)))
;    :hints (("goal" :use (:instance lessp-plus))))
;
;  (defthm irreflexive-revisited-and-commuted
;    (implies (and (rationalp x)
;                  (rationalp y)
;                  (lessp y x))
;             (equal (equal x y) nil)))
;
; (defthm clessp-additive-properties
;   (and (implies (and (clessp x y)
;                      (clesseqp u v))
;                 (clessp (cplus x u) (cplus y v)))
;        (implies (and (clesseqp x y)
;                      (clesseqp u v))
;                 (clesseqp (cplus x u) (cplus y v)))))
;
; ; The 1+ Trick
; ; (implies (and (integerp x)
; ;               (integerp y)
; ;               (< x y))
; ;          (<= (+ 1 x) y))
;
; (defthm cplus-1-trick
;   (implies (and (integerp x)
;                 (integerp y)
;                 (clessp x y))
;            (clesseqp (cplus 1 x) y)))
;
; ; Cross-Multiplying Allows Cancellation
; ; (implies (and (< c1 0)
; ;               (< 0 c2))
; ;          (equal (+ (* c1 (abs c2)) (* c2 (abs c1))) 0))
;
; ; Three lemmas lead to the result.
;
;  (defthm times--1--1
;    (equal (times -1 -1) 1)
;    :hints
;    (("goal"
;      :use ((:instance plus-inverse-unique (x (times -1 -1)) (y 1))))))
;
;  (defthm times--1-times--1
;    (implies (rationalp x)
;             (equal (times -1 (times -1 x)) x))
;    :hints (("Goal"
;             :use (:instance times-commutative-and-associative
;                             (x -1)
;                             (y -1)
;                             (z x)))))
;  (defthm reassocate-to-cancel-plus
;    (implies (and (rationalp x)
;                  (rationalp y))
;             (equal (plus x (plus y (plus (times -1 x) (times -1 y))))
;                    0))
;    :hints
;    (("Goal" :use ((:instance plus-commutative-and-associative
;                              (x y)
;                              (y (times -1 x))
;                              (z (times -1 y)))))))
;
; ; Multiplication by Positive Preserves Inequality
; ;(implies (and (rationalp c)     ; see note below
; ;              (< 0 c))
; ;         (iff (< x y)
; ;              (< (* c x) (* c y))))
;
; (defthm multiplication-by-positive-preserves-inequality
;   (implies (and (rationalp c)
;                 (clessp 0 c))
;            (iff (clessp x y)
;                 (clessp (ctimes c x) (ctimes c y)))))
;
; ; The Zero Trichotomy Trick
; ; (implies (and (acl2-numberp x)
; ;               (not (equal x 0))
; ;               (not (equal x y)))
; ;          (or (< x y) (< y x)))
;
;  (defthm complex-equal-0
;    (implies (and (rationalp x)
;                  (rationalp y))
;             (equal (equal (complex x y) 0)
;                    (and (equal x 0)
;                         (equal y 0)))))
;
; (defthm zero-trichotomy-trick
;  (implies (and (acl2-numberp x)
;                (not (equal x 0))
;                (not (equal x y)))
;           (or (clessp x y) (clessp y x)))
;  :rule-classes nil :hints (("goal" :in-theory (enable fix))))
;
;
; ; The Find Equational Poly Trick
; ; (implies (and (<= x y) (<= y x)) (equal (fix x) (fix y)))
;
; (defthm find-equational-poly-trick
;   (implies (and (clesseqp x y)
;                 (clesseqp y x))
;
;            (equal (fix x) (fix y)))
;   :hints (("Goal" :in-theory (enable fix))))
;
; )

;-----------------------------------------------------------------------------
; Thus ends the ALSLA.  However, there are, no doubt, a few more that we
; will discover when we implement proof objects!

; Note that in Multiplication by Positive Preserves Inequality we require the
; positive to be rational.  Multiplication by a "positive" complex rational
; does not preserve the inequality.  For example, the following evaluates
; to nil:
; (let ((c #c(1 -10))
;       (x #c(1 1))
;       (y #c(2 -2)))
;  (implies (and ; (rationalp c)          ; omit the rationalp hyp
;                  (< 0 c))
;           (iff (< x y)                  ; t
;                (< (* c x) (* c y)))))   ; nil

; Thus, the coefficients in our polys must be rational.

; End of Essay on the Logical Basis for Linear Arithmetic.

;=================================================================

; Polys

; Historical note: Polys are now
; (<  0 (+ constant (* k1 t1) ... (* kn tn)))
; rather than
; (<  (+ constant (* k1 t1) ... (* kn tn)) 0)
; as in Version_2.6 and before.

(defrec poly
    (((alist parents . ttree)
      .
      (constant relation rational-poly-p . derived-from-not-equalityp)))
    t)

; A poly represents an implication hyps -> concl, where hyps is the
; conjunction of the terms in the 'assumptions of the ttree and concl is

; (<  0 (+ constant (* k1 t1) ... (* kn tn))), if relation = '<
; (<= 0 (+ constant (* k1 t1) ... (* kn tn))), otherwise.

; Constant is an ACL2 numberp, possibly complex-rationalp but usually
; rationalp.  Alist is an alist of pairs of the form (ti . ki) where ti is a
; term and ki is a rationalp.  The alist is kept ordered by arith-term-order on
; the ti.  The largest ti is at the front.  Relation is either '< or '<=.

; The ttree in a poly is a tag-tree.
; There are three tags we use here: lemma, assumption, and pt.  The lemma tag
; indicates a lemma name used to produce the poly.  The assumption tag
; indicates a term assumed true to produce the poly.  For example, an
; assumption might be (rationalp (foo a b)).  The pt tag indicates literals of
; current-clause used in the production of the poly.

; The parents field is generally a list of parents and is set-eql to the union
; over all 'pt tags in ttree of the tips of the pts.  (But see the comment
; labeled ":parent wart" in linear-b.lisp for an exception.)  It is used in the
; code that ignores polynomials descended from the current literal.  (This used
; to be done by to-be-ignoredp, which used to take up to 80% of the time spent
; by add-poly.)  See collect-parents and marry-parents for how we establish and
; maintain this relationship, and ignore-polyp for its use.

; Rational-poly-p is a booolean flag used in non-linear arithmetic.  When it is
; true, then the right-hand side of the inequality (the polynomial) is known to
; have a rational number value.  (But note that for ACL2(r), i.e. for
; #+:non-standard-analysis, the value need only be real.  Through the linear
; and non-linear arithmetic code, references to "rational" should be considered
; as references to "real".)  The flag is needed because of the presence of
; complex numbers in ACL2's logic.  Note that sums and products of rational
; polys are rational.  When rational-poly-p is true we know that the product of
; two positive polys is also positive.

; Derived-from-not-equalityp keeps track of whether the poly in question was
; derived directly from a top-level negated equality.  This field is new to
; v2_8 --- previously its value was calculated as needed.  In the rest of this
; comment, we address two issues --- (1) What derived-from-not-equalityp is
; used for.  (2) Differences from earlier behavior.

; (1) What derived-from-not-equalityp is used for: In process-equational-polys,
; we scan through the simplify-clause-pot-lst and look for complementary pairs
; of inequalities from which we can derive an equality.  Example: from (<= x y)
; and (<= y x) we can derive (equal x y).  However, the two inequalities could
; have themselves been derived from the very equality we are about to generate,
; and this could lead to looping.  Thus, we tag those inequalities which stem
; directly from the linearization of a (negated) equality with
; :derived-from-not-equalityp = t.  This field is then examined in
; process-equational-polys (or rather its sub-functions), and the result is
; used to prune the list of candidate inequalities.

; (2) Differences from earlier behavior:
; Previously, the function descends-from-not-equalityp played the role of the
; new field :derived-from-not-equalityp.  This function was much more
; conservative in its judgement and threw out any poly which descended from an
; inequality in any way, rather than only those which were derived directly
; from a (negated) equality.  Matt Kaufmann noticed difference and provoked an
; email exchange with Robert Krug, who did the research and initial coding
; leading to this version of linear).  Here is Robert's reply.

;   Matt is right, I did inadvertantly change ACL2's meaning for
;   descends-from-not-equalityp.  Perhaps this change is also responsible
;   for some of the patches required for the regression suite.  However,
;   this change was inadvertant only because I did not properly understand
;   the old behaviour which seems odd to me.  I believe that the new
;   behaviour is the ``correct'' one.  Let us look at an example:
;
;   Input:
;
;   x = y       (1)
;   a + y >= b  (2)
;   a + x <= b  (3)
;
;   After cancellation:
;
;   y: x <= y      (1a)
;      b <= y + a  (2)
;
;      y <= x      (1b)
;
;   x: x + a <= b  (3)
;
;      b <= x + a  (4) = (1b + 2)
;
;   I think that some form of x + a = b should be generated and added to
;   the clause.  Under the new order, (3) and (4) would be allowed to
;   combine, because neither of them descended \emph{directly} from an
;   inequality.  This seems like the kind of fact that I, as a user, would
;   expect ACL2 to know and use.  Under the old regime however, since (1b)
;   was used in the derivation of (4), this was not allowed.
;
;   This raises the qestion of whether the new test is too liberal.  For
;   example, from
;
;   input:
;   x = y
;   a + x = b + y
;
;   We would now generate the equality a = b.  I do not see any harm in
;   this.  Perhaps another example will convince me that we need to
;   tighten the heuristic up.

; [End of Robert's reply.]

; Note: In Nqthm, we thought of polynomials being inequalities in a different
; logic, or at least, in an extension of the Nqthm logic that included the
; rationals.  In ACL2, we think of a poly as simply being an alternative
; represention of a term, in which we have normalized by the use of certain
; algebraic laws governing the ACL2 function symbols <, <=, +, and *.  We
; noted these above (see ALSLA).  In addition, we think of the operations
; performed upon polys being just ordinary inferences within the logic,
; justified by still other algebraic laws, such as that allowing the addition
; of inequalities.  The basic idea behind the linear arithmetic procedure is
; to convert the (arithmetic) assumptions in a problem (including the
; negation of the conclusion) to their normal forms, make a bunch of ordinary
; forward-chaining-like inferences from those assumptions guided by certain
; principles, and if a contradiction is found, deduce that the original
; assumptions imply the original conclusion.  The point is that linear
; arithmetic is not some model-theoretic step appealing to the correspondence
; of theorems in two different theories but rather an entirely
; proof-theoretic step.

(defabbrev first-var (p) (caar (access poly p :alist)))

(defabbrev first-coefficient (p) (cdar (access poly p :alist)))

; We expect polys to meet the following invariant implied in the discussion
; above:
; 1. The leading coefficient is +/-1
; 2. The leading unknown:
;    a. Is not a quoted constant --- Not much of an unknown/variable
;    b. Is not itself a sum --- A poly represents a sum of terms
;    c. Is not of the form (* c x), where c is a rational constant ---
;       The c should have been ``pulled out''.
;    d. Is not of the form (- c), (* c d), or (+ c d) where c and d are
;       rational constants --- These terms should be evaluated and added
;       onto the constant, not used as an unknown.
;    Some of these are implied by others, but we check them each
;    independently.

; The following three functions (weakly) capture this notion.

; Note: These invariants are referred to elsewhere by number, e.g.,
; ``2.a'' If you change the above, search for occurrences of
; ``good-polyp''.  If you refer to these invariants, be sure to
; include the string ``good-polyp'' somewhere nearby.

(defun good-coefficient (c)
  (equal (abs c) 1))

(defun good-pot-varp (x)
  (and (not (quotep x))
       (not (equal (fn-symb x) 'BINARY-+))
       (not (and (equal (fn-symb x) 'BINARY-*)
                 (quotep (fargn x 1))
                 (real/rationalp (unquote (fargn x 1)))))
       (not (and (equal (fn-symb x) 'UNARY--)
                 (quotep (fargn x 1))
                 (real/rationalp (unquote (fargn x 1)))))))

(defun good-polyp (p)
  (and (good-coefficient (first-coefficient p))
       (good-pot-varp (first-var p))))

; We need to define executable versions of the logical functions for <, <=,
; and abs.  We know, however, that we will only apply them to acl2-numberps
; so we do not need to consider fixing the arguments.

;; RAG - I changed rational to real in the test to use < as the comparator.

(defun logical-< (x y)
  (declare (xargs :guard (and (acl2-numberp x) (acl2-numberp y))))
  (cond ((and (real/rationalp x)
              (real/rationalp y))
         (< x y))
        ((< (realpart x) (realpart y))
         t)
        (t (and (= (realpart x) (realpart y))
                (< (imagpart x) (imagpart y))))))

;; RAG - Another change of rational to real in the test to use <= as the
;; comparator.

(defun logical-<= (x y)
  (declare (xargs :guard (and (acl2-numberp x) (acl2-numberp y))))
  (cond ((and (real/rationalp x)
              (real/rationalp y))
         (<= x y))
        ((< (realpart x) (realpart y))
         t)
        (t (and (= (realpart x) (realpart y))
                (<= (imagpart x) (imagpart y))))))

(defun evaluate-ground-poly (p)

; We assume the :alist of poly p is nil and thus p is a ground poly.
; We compute its truth value.

  (if (eq (access poly p :relation) '<)
      (logical-< 0 (access poly p :constant))
      (logical-<= 0 (access poly p :constant))))

(defun impossible-polyp (p)
  (and (null (access poly p :alist))
       (eq (evaluate-ground-poly p) nil)))

(defun true-polyp (p)
  (and (null (access poly p :alist))
       (evaluate-ground-poly p)))

(defun silly-polyp (poly)

; For want of a better name, we say a poly is "silly" if it contains
; the *nil* assumption among its 'assumptions.

  (tag-tree-occur-assumption-nil (access poly poly :ttree)))

(defun impossible-poly (ttree)
  (make poly
        :alist nil
        :parents (collect-parents ttree)
        :rational-poly-p t
        :derived-from-not-equalityp nil
        :ttree ttree
        :constant -1
        :relation '<))

(defun base-poly0 (ttree parents relation rational-poly-p derived-from-not-equalityp)

; Warning: Keep this in sync with base-poly.

  (make poly
        :alist nil
        :parents parents
        :rational-poly-p rational-poly-p
        :derived-from-not-equalityp derived-from-not-equalityp
        :ttree ttree
        :constant 0
        :relation relation))

(defun base-poly (ttree relation rational-poly-p derived-from-not-equalityp)

; Warning: Keep this in sync with base-poly0.

  (make poly
        :alist nil
        :parents (collect-parents ttree)
        :rational-poly-p rational-poly-p
        :derived-from-not-equalityp derived-from-not-equalityp
        :ttree ttree
        :constant 0
        :relation relation))

(defun poly-alist-equal (alist1 alist2)

; This function is essentially EQUAL for two alists, but is faster
; (at least with poly alists).

  (cond ((null alist1)
         (null alist2))
        ((null alist2)
         nil)
        (t
         (and (eql (cdar alist1) (cdar alist2))
              (equal (caar alist1) (caar alist2))
              (poly-alist-equal (cdr alist1) (cdr alist2))))))

(defun poly-equal (poly1 poly2)

; This function is essentially EQUAL for two polys, but is faster.

  (and (eql (access poly poly1 :constant)
            (access poly poly2 :constant))
       (eql (access poly poly1 :relation)
            (access poly poly2 :relation))
       (poly-alist-equal (access poly poly1 :alist)
                         (access poly poly2 :alist))))

(defun poly-weakerp (poly1 poly2 parents-check)

; We return t if poly1 is ``weaker'' than poly2.

; Pseudo-examples:
; (<= 3 (* x y)) is weaker than both (< 3 (* x y)) and (<= 17/5 (* x y));
; but is not weaker than (< 17 (+ w (* x y))), (< 17 (* 5 x y)),
; or (< 17 (* y x)).

; Normally parents-check is t; if poly2 has a parent not in the parents of
; poly1, then poly1 might be usable in a context where poly2 is not usable.
; Use parents-check = nil if such a consideration does not apply.

  (let ((c1 (access poly poly2 :constant))
        (c2 (access poly poly1 :constant)))
    (and (or (logical-< c1 c2)

; The above inequality test is potentially confusing.  In the comments, it is
; said that (<= 3 (* x y)) is weaker than (<= 17/5 (* x y)).  Recall that the
; polys are stored in a format suggested by: (< (+ constant (* k1 t1) ... (* kn
; tn)) 0).  Thus, the two constants would be stored as a -3 and a -17/5, and
; the above test is correct.  -17/5 < -3.

             (and (eql c1 c2)
                  (or (eq (access poly poly1 :relation) '<=)
                      (eq (access poly poly2 :relation) '<))))
         (poly-alist-equal (access poly poly1 :alist)
                           (access poly poly2 :alist))
         (if parents-check
             (subsetp (access poly poly2 :parents)
                      (access poly poly1 :parents))
           t))))

(defun poly-member (p lst)

; P is a poly and lst is a list of polys.  This function used to return t if p
; was in lst (ignoring tag-trees).  Now, it returns t if p is weaker than
; some poly in lst.

; This change was motivated by an observation that after several linear rules
; have fired and a couple of rounds of cancellation have occurred, one will
; occasionally see the linear pot fill up with weak polys.  In most cases
; this idea makes no real performance difference; but Robert Krug has seen
; examples where it makes a tremendous difference.

  (and (consp lst)
       (or (poly-weakerp p (car lst) t)
           (poly-member p (cdr lst)))))

(defun new-and-ugly-linear-varsp (lst flag term)

; Lst is a list of polys, term is the linear var which triggered the
; addition of the polys in lst, and flag is a boolean indicating
; whether we have maxed out the the loop-stopper-value associated
; with term.  If flag is true, we check whether any of the polys are
; arith-term-order worse than term.

; Historical Note: Once upon a time, in Version_2.5 and earlier, this
; function actually insured that term wasn't in lst, i.e., that term was
; "new".  But in Version_2.6, we changed the meaning of the function without
; changing its name.  The word "new" in the name is now a mere artifact.

; This is intended to catch certain loops that can arise from linear
; lemmas.  See the "Mini-essay on looping and linear arithmetic" below.


  (cond ((not flag)
         nil)
        ((null lst)
         nil)
        ((arith-term-order term
                           (first-var (car lst)))
         t)
        (t (new-and-ugly-linear-varsp (cdr lst) flag term))))

(defun filter-polys (lst ans)

; We scan the list of polys lst.  If we find an impossible one, we
; return it as our first result.  If we find a true one we skip it.
; If we find a poly that is ``weaker'' (see poly-member and poly-weakerp)
; than one of those already filtered, we skip it.
; Otherwise we just accumulate them into ans.  We return two values:
; the standard indication of contradiction and, otherwise in the
; second, the filtered list.  This list in the reverse order from that
; produced by nqthm.

  (cond ((null lst)
         (mv nil ans))
        ((impossible-polyp (car lst))
         (mv (car lst) nil))
        ((true-polyp (car lst))
         (filter-polys (cdr lst) ans))
        ((poly-member (car lst) ans)
         (filter-polys (cdr lst) ans))
        (t
         (filter-polys (cdr lst) (cons (car lst) ans)))))


;=================================================================

; Here we define some functions for constructing polys.

(defun add-linear-variable1 (n var alist)

; N is a rational constant and var is an arbitrary term -- a linear "variable".
; Alist is a polynomial alist and we are to add the new pair (var . n) to it.
; We keep the alist sorted on term-order on the terms with the largest var
; first.  Furthermore, if there is already an entry for var we merely add n to
; it.  If the resulting coefficient is 0 we delete the pair.

; We assume n is not 0 to begin with.

  (cond ((null alist)
         (cons (cons var n) nil))
        ((arith-term-order var (caar alist))
         (cond ((equal var (caar alist))
                (let ((k (+ (cdar alist)
                            n)))
                  (cond ((= k 0) (cdr alist))
                        (t (cons (cons var k) (cdr alist))))))
               (t (cons (car alist)
                        (add-linear-variable1 n var
                                              (cdr alist))))))
        (t (cons (cons var n)
                 alist))))

(defun zero-factor-p (term)

; The following code recognizes terms of the form (* a1 ... 0 ... ak)
; so that we can treat them as though they were 0.  Two sources of these
; 0-factor terms are: the original clause for which we are
; constructing a pot-lst, and a term introduced by forward chaining,
; which doesn't use rewrite.  (The latter might commonly occur via an
; fc rule like (implies (and (< 0 x) (< y y+)) (< (* x y) (* x y+)))
; triggered by (* x y+).  The free var y might be chosen to be 0, as
; would happen if (< 0 y+) were available.  The result would be the
; term (* 0 y).)

  (cond ((variablep term) nil)
        ((fquotep term)
         (equal term *0*))
        ((eq (ffn-symb term) 'BINARY-*)
         (or (zero-factor-p (fargn term 1))
             (zero-factor-p (fargn term 2))))
        (t
         nil)))

(defun get-coefficient (term acc)

; We are about to add term onto a poly.  We want to enforce the
; poly invariant 2.c. (Described shortly before the definition of
; good-polyp.)  We therefore accumulate onto acc any leading constant
; coefficients.  We return the (possibly) stripped term and its
; coefficient.

  (if (and (eq (fn-symb term) 'BINARY-*)
           (quotep (fargn term 1))
           (real/rationalp (unquote (fargn term 1))))
      (get-coefficient (fargn term 2) (* (unquote (fargn term 1)) acc))
    (mv acc term)))

(defun add-linear-variable (term side p)
  (mv-let (n term)
    (cond ((zero-factor-p term)
           (mv 0 nil))
          ((and (eq (fn-symb term) 'BINARY-*)
                (quotep (fargn term 1))
                (real/rationalp (unquote (fargn term 1))))
           (mv-let (coeff new-term)
             (get-coefficient term 1)
             (if (eq side 'lhs)
                 (mv (- coeff) new-term)
               (mv coeff new-term))))
          ((eq side 'lhs)
           (mv -1 term))
          (t
           (mv 1 term)))
    (if (= n 0)
        p
      (change poly p
              :alist
              (add-linear-variable1 n term (access poly p :alist))))))

(defun dumb-eval-yields-quotep (term)

; We are about to add term onto a poly.  We want to enforce the poly invariant
; 2.d. (Described shortly before the definition of good-polyp.)   Here, we
; check whether we should evaluate term.  If so, we do the evaluation in
; dumb-eval immediately below.

  (cond ((variablep term)
         nil)
        ((fquotep term)
         t)
        ((equal (ffn-symb term) 'BINARY-*)
         (and (dumb-eval-yields-quotep (fargn term 1))
              (dumb-eval-yields-quotep (fargn term 2))))
        ((equal (ffn-symb term) 'BINARY-+)
         (and (dumb-eval-yields-quotep (fargn term 1))
              (dumb-eval-yields-quotep (fargn term 2))))
        ((equal (ffn-symb term) 'UNARY--)
         (dumb-eval-yields-quotep (fargn term 1)))
        (t
         nil)))

(defun dumb-eval (term)

; See dumb-eval-yields-quotep, above.  This function evaluates (fix
; ,term) and produces the corresponding evg, not a term.  Thus,
; (binary-+ '1 '2) dumb-evals to 3 not '3, and (quote abc) dumb-evals
; to 0.

  (cond ((variablep term)
         (er hard 'dumb-eval
             "Bad term. We were expecting a constant, but encountered
              the variable ~x."
             term))
        ((fquotep term)
         (if (acl2-numberp (unquote term))
             (unquote term)
           0))
        ((equal (ffn-symb term) 'BINARY-*)
         (* (dumb-eval (fargn term 1))
            (dumb-eval (fargn term 2))))
        ((equal (ffn-symb term) 'BINARY-+)
         (+ (dumb-eval (fargn term 1))
            (dumb-eval (fargn term 2))))
        ((equal (ffn-symb term) 'UNARY--)
         (- (dumb-eval (fargn term 1))))
        (t
         (er hard 'dumb-eval
             "Bad term. The term ~x was not as expected by dumb-eval."
             term))))

(defun add-linear-term (term side p)

; Side is either 'rhs or 'lhs.  This function adds term to the
; indicated side of the poly p.  It is the main way we construct a
; poly.  See linearize.

  (cond
   ((variablep term)
    (add-linear-variable term side p))

; We enforce poly invariant 2.d.   (Described shortly before the
; definition of good-polyp.)

   ((dumb-eval-yields-quotep term)
    (let ((temp (dumb-eval term)))
      (if (eq side 'lhs)
          (change poly p
                  :constant
                  (+ (access poly p :constant) (- temp)))
        (change poly p
                :constant
                (+ (access poly p :constant) temp)))))

   (t
    (let ((fn1 (ffn-symb term)))
      (case fn1
            (binary-+
             (add-linear-term (fargn term 1) side
                              (add-linear-term (fargn term 2) side p)))
            (unary--
             (add-linear-term (fargn term 1)
                              (if (eq side 'lhs) 'rhs 'lhs)
                              p))
            (binary-*

; We enforce the poly invariants 2.b. and 2.c.  (Described shortly
; before the definition of good-polyp.)

             (cond
              ((and (quotep (fargn term 1))
                    (real/rationalp (unquote (fargn term 1)))
                    (equal (fn-symb (fargn term 2)) 'BINARY-+))
               (add-linear-term
                (mcons-term* 'BINARY-+
                             (mcons-term* 'BINARY-*
                                          (fargn term 1)
                                          (fargn (fargn term 2) 1))
                             (mcons-term* 'BINARY-*
                                          (fargn term 1)
                                          (fargn (fargn term 2) 2)))
                side
                p))
              ((and (quotep (fargn term 1))
                    (real/rationalp (unquote (fargn term 1)))
                    (equal (fn-symb (fargn term 2)) 'BINARY-*)
                    (quotep (fargn (fargn term 2) 1))
                    (real/rationalp (unquote (fargn (fargn term 2) 1))))
               (add-linear-term
                (mcons-term* 'BINARY-*
                             (kwote (* (unquote (fargn term 1))
                                       (unquote (fargn (fargn term 2) 1))))
                             (fargn (fargn term 2) 2))
                side
                p))
              (t
               (add-linear-variable term side p))))

            (otherwise
             (add-linear-variable term side p)))))))

(defun add-linear-terms-fn (rst)
  (cond ((null (cdr rst))
         (car rst))
        ((eq (car rst) :lhs)
         `(add-linear-term ,(cadr rst) 'lhs
                           ,(add-linear-terms-fn (cddr rst))))
        ((eq (car rst) :rhs)
         `(add-linear-term ,(cadr rst) 'rhs
                           ,(add-linear-terms-fn (cddr rst))))
        (t
         (er hard 'add-linear-terms-fn
             "Bad term ~x0"
             rst))))

(defmacro add-linear-terms (&rest rst)

; There are a couple of spots where we wish to add several pieces at
; a time to a poly.  This macro and its associated function enable us
; to circumvent ACL2's requirement that all functions take a fixed
; number of arguments.

; Example usage:
; (add-linear-terms :lhs term1
;                   :lhs ''1
;                   :rhs term2
;                   (base-poly ts-ttree
;                             '<=
;                             t
;                             nil))

  (add-linear-terms-fn rst))

(defun normalize-poly1 (coeff alist)
  (cond ((null alist)
         nil)
        (t
         (acons (caar alist) (/ (cdar alist) coeff)
                (normalize-poly1 coeff (cdr alist))))))

(defun normalize-poly (p)

; P is a poly.  We normalize it, so that the leading coefficient is +/-1.

  (if (access poly p :alist)
      (let ((c (abs (first-coefficient p))))
        (cond ((eql c 1)
               p)
              (t
               (change poly p
                       :alist (normalize-poly1 c (access poly p :alist))
                       :constant (/ (access poly p :constant) c)))))
    p))

(defun normalize-poly-lst (poly-lst)
  (cond ((null poly-lst)
         nil)
        (t
         (cons (normalize-poly (car poly-lst))
               (normalize-poly-lst (cdr poly-lst))))))


;=================================================================


; Linear Pots

(defrec linear-pot ((loop-stopper-value . negatives) . (var . positives)) t)

; Var is a "linear variable", i.e., any term.  Positives and negatives are
; lists of polys with the properties that var is the first (heaviest) linear
; variable in each poly in each list and var occurs positively in the one and
; negatively in the other.  Loop-stopper-value is a natural number counter that
; is used to avoid looping, starting at 0 and incremented, using
; *max-linear-pot-loop-stopper-value* as a bound.

(defun modify-linear-pot (pot pos neg)

; We do the equivalent of:

; (change linear-pot pot :positives pos :negatives neg)

; except that we avoid unnecessary consing.

  (if (equal neg (access linear-pot pot :negatives))
      (if (equal pos (access linear-pot pot :positives))
          pot
        (change linear-pot pot :positives pos))
    (if (equal pos (access linear-pot pot :positives))
        (change linear-pot pot :negatives neg)
      (change linear-pot pot
              :positives pos
              :negatives neg))))

; Mini-essay on looping and linear arithmetic

; Robert Krug has written code to solve a problem with infinite loops related
; to linear arithmetic.  The following example produces the loop in ACL2
; Versions 2.4 and earlier.

;  (defaxiom *-strongly-monotonic
;    (implies (and (< a b))
;             (< (* a c) (* b c)))
;    :rule-classes :linear)
;
;  (defaxiom commutativity-2-of-*
;    (equal (* x y z)
;           (* y x z)))
;
;  (defstub foo (x) t)
;
;  (thm
;   (implies (and (< a (* a c))
;                 (< 0 evil))
;            (foo x)))

; The defconst below stops the loop.  We may want to increase it in the future,
; but it appears to be sufficient for certifying ACL2 community books.  It is
; used together with the field loop-stopper-value of the record linear-pot.
; When a linear-pot is first created, its loop-stopper-value is 0 (see
; add-poly).  See add-linear-lemma for how loop-stopper-value is used to detect
; loops.

; Robert has provided the following trace, in which one can still see the first
; few iterations of the loop before it is caught by the loop-stopping mechanism
; now added.  He suggests tracing new-and-ugly-linear-varp and worse-than to
; get some idea as to why this loop was not caught before due to the presence
; of the inequality (< 0 evil).

; (trace (add-linear-lemma
;         :entry (list (list 'term (nth 0 si::arglist))
;                      (list 'lemma (access linear-lemma
;                                           (nth 1 si::arglist)
;                                           :rune))
;                      (list 'max-term (access linear-lemma
;                                              (nth 1 si::arglist)
;                                              :max-term))
;                      (list 'conclusion (access linear-lemma
;                                                (nth 1 si::arglist)
;                                                :concl))
;                      (list 'type-alist (show-type-alist
;                                         (nth 2 si::arglist))))
;         :exit (if (equal (nth 9 si::arglist)
;                          (mv-ref 1))
;                   '(no change)
;                   (list (list 'old-pot-list
;                               (show-pot-lst (nth 9 si::arglist)))
;                         (list 'new-potlist
;                               (show-pot-lst (mv-ref 1)))))))

(defconst *max-linear-pot-loop-stopper-value* 3)

(defun loop-stopper-value-of-var (var pot-lst)

; We return the value of loop-stopper-value associated with var in the
; pot-lst.  If var does not appear we return 0.

  (cond ((null pot-lst) 0)
        ((equal var (access linear-pot (car pot-lst) :var))
         (access linear-pot (car pot-lst) :loop-stopper-value))
        (t
         (loop-stopper-value-of-var var (cdr pot-lst)))))

(defun set-loop-stopper-values (new-vars new-pot-lst term value)

; New-vars is a list of new variables in new-pot-lst.  Term is the trigger-term
; which caused the new pots to be added, and value is the loop-stopper-value
; associated with it.  If a new-var is term-order greater than term, we set its
; loop-stopper-value to value + 1.  Otherwise, we set it to value.

; Note that new-vars is in the same order as the vars of new-pot-lst.

  (cond ((null new-vars) new-pot-lst)
        ((equal (car new-vars) (access linear-pot (car new-pot-lst) :var))
           (cond ((arith-term-order term (car new-vars))
                    (cons (change linear-pot (car new-pot-lst)
                                  :loop-stopper-value (1+ value))
                          (set-loop-stopper-values (cdr new-vars)
                                                   (cdr new-pot-lst)
                                                   term
                                                   value)))
                 (t
                    (cons (change linear-pot (car new-pot-lst)
                                  :loop-stopper-value value)
                          (set-loop-stopper-values (cdr new-vars)
                                                   (cdr new-pot-lst)
                                                   term
                                                   value)))))
        (t
           (cons (car new-pot-lst)
                 (set-loop-stopper-values new-vars
                                          (cdr new-pot-lst)
                                          term
                                          value)))))

(defun var-in-pot-lst-p (var pot-lst)

; Test whether var is the label of any of the pots in pot-lst.

  (cond ((null pot-lst) nil)
        ((equal var (access linear-pot (car pot-lst) :var))
         t)
        (t
         (var-in-pot-lst-p var (cdr pot-lst)))))

(defun bounds-poly-with-var (poly-lst pt bounds-poly)

; We cdr down poly-lst, looking for a bounds poly.  Poly-lst is either the
; :positives or :negatives from a pot.  We would like to believe that the first
; bounds poly we find is, in fact, the strongest one present in poly-lst
; because we filter out any ones that are weaker than one already present with
; poly-member before adding it.  However, that filtering was done using
; poly-weakerp with parameter parents-check = t, yet here we do not have any
; preference based on parents, other than that they do not disqualify the poly
; (based on argument pt) -- we just want the strongest bounds poly.

  (cond ((null poly-lst)
         bounds-poly)
        ((and (null (cdr (access poly (car poly-lst) :alist)))
              (rationalp (access poly (car poly-lst) :constant))
              (not (ignore-polyp (access poly (car poly-lst) :parents) pt)))
         (bounds-poly-with-var
          (cdr poly-lst)
          pt
          (cond ((and bounds-poly
                      (poly-weakerp (car poly-lst) bounds-poly nil))
                 bounds-poly)
                (t (car poly-lst)))))
        (t
         (bounds-poly-with-var (cdr poly-lst) pt bounds-poly))))

(defun bounds-polys-with-var (var pot-lst pt)

; A bounds poly is one in which the there is only one var in the
; alist.  Such a poly can be regarded as "bounding" said var.

; Pseudo-examples:
; 3 < x is a bounds poly.
; 3 < x + y is not.
; #(1,1) < x is not.

; We insist that the constant c be rational.

; We return a list of the strongest bounds polys in the pot labeled
; with var.  If there are no such polys, we return nil.

  (cond ((null pot-lst) nil)
        ((equal var (access linear-pot (car pot-lst) :var))
         (let ((neg (bounds-poly-with-var
                     (access linear-pot (car pot-lst) :negatives) pt nil))
               (pos (bounds-poly-with-var
                     (access linear-pot (car pot-lst) :positives) pt nil)))
           (cond (neg (if pos (list neg pos) (list neg)))
                 (t   (if pos (list     pos) nil)))))
        (t (bounds-polys-with-var var (cdr pot-lst) pt))))

(defun polys-with-var1 (var pot-lst)
  (cond ((null pot-lst) nil)
        ((equal var (access linear-pot (car pot-lst) :var))
         (append (access linear-pot (car pot-lst) :negatives)
                 (access linear-pot (car pot-lst) :positives)))
        (t (polys-with-var1 var (cdr pot-lst)))))

(defun polys-with-var (var pot-lst)

; We return a list of all the polys in the pot labeled with var.
; If there is no pot in pot-lst labeled with var, we return nil.
; We may occasionally be calling this function with an improper
; var.  We catch this early, rather than stepping through the whole
; pot (see add-inverse-polys and add-inverse-polys1).

  (if (eq (fn-symb var) 'BINARY-+)
      nil
    (polys-with-var1 var pot-lst)))

(defun polys-with-pots (polys pot-lst ans)

; We filter out those polys in polys which do not have a pot in
; pot-lst to hold them.  Ans is initially nil.

  (cond ((null polys)
         ans)
        ((var-in-pot-lst-p (first-var (car polys)) pot-lst)
         (polys-with-pots (cdr polys) pot-lst (cons (car polys) ans)))
        (t
         (polys-with-pots (cdr polys) pot-lst ans))))

(defun new-vars-in-pot-lst (new-pot-lst old-pot-lst include-variableps)

; We return all the new vars of new-pot-lst.  A "var" of a pot-lst is the :var
; component of a linear-pot in the pot-lst.  A var is considered "new" if the
; var is not a var of the old-pot-lst and moreover, if include-variableps is
; false then it is not a variablep (i.e., is a function application).
; New-pot-lst is an extension of old-pot-lst, obtained by successive calls of
; add-poly.  Every variable of old-pot-lst is in the new, but not vice versa.
; Since both lists are ordered by the vars we can recur down both the new and
; the old pot lists simultaneously.

  (cond ((null new-pot-lst)
         nil)

; This function used to be wrong!  We incorrectly optimized the case for a pot
; with a variablep :var.  Consider an old-pot-lst with one pot, (foo x), and a
; new-pot-lst with two pots, x and (foo x).  Previously, since (variablep
; (access linear-pot (car new-pot-lst) :var)) would be true, we would recur on
; the cdr of both pots and then determine that (foo x) was new.  I suspect that
; the variablep test was added to the function after the rest had been written
; (and, the include-variablesp argument was definitely added more recently than
; any of the rest of this comment).  Here is the old code.  This bug was
; discovered by Robert Krug.

;               (or all-new-flg
;                   (null old-pot-lst)
;                   (not (equal (access linear-pot (car new-pot-lst) :var)
;                               (access linear-pot (car old-pot-lst) :var)))))
;          (cons (access linear-pot (car new-pot-lst) :var)
;                (new-vars-in-pot-lst (cdr new-pot-lst)
;                                     old-pot-lst all-new-flg)))

        ((or (null old-pot-lst)
             (not (equal (access linear-pot (car new-pot-lst) :var)
                         (access linear-pot (car old-pot-lst) :var))))
         (if (or include-variableps
                 (not (variablep (access linear-pot (car new-pot-lst) :var))))
             (cons (access linear-pot (car new-pot-lst) :var)
                   (new-vars-in-pot-lst (cdr new-pot-lst)
                                        old-pot-lst
                                        include-variableps))
           (new-vars-in-pot-lst (cdr new-pot-lst)
                                old-pot-lst
                                include-variableps)))
        (t (new-vars-in-pot-lst (cdr new-pot-lst)
                                (cdr old-pot-lst)
                                include-variableps))))

(defun changed-pot-vars (new-pot-lst old-pot-lst to-be-ignored-lst)

; New-pot-lst is an extension of old-pot-lst. To-be-ignored-lst is a
; list of pots which we are to ignore.  We return the list of pot
; labels (i.e., vars) of the pots which are changed with respect to
; old-pot-lst (a new pot is considered changed) which are not in
; to-be-ignored-lst.

  (cond ((null new-pot-lst)
         nil)
        ((equal (access linear-pot (car new-pot-lst) :var)
                (access linear-pot (car old-pot-lst) :var))
         (if (or (equal (car new-pot-lst)
                        (car old-pot-lst))
                 (member-equal (access linear-pot (car new-pot-lst) :var)
                               to-be-ignored-lst))
             (changed-pot-vars (cdr new-pot-lst) (cdr old-pot-lst)
                               to-be-ignored-lst)
           (cons (access linear-pot (car new-pot-lst) :var)
                 (changed-pot-vars (cdr new-pot-lst) (cdr old-pot-lst)
                                   to-be-ignored-lst))))
        (t
         (cons (access linear-pot (car new-pot-lst) :var)
               (changed-pot-vars (cdr new-pot-lst) old-pot-lst
                                 to-be-ignored-lst)))))

(defun infect-polys (lst ttree parents)

; We extend the :ttree of every poly in lst with ttree.  We similarly
; expand :parents with parents.

  (cond ((null lst) nil)
        (t (cons (change poly (car lst)
                         :ttree
                         (cons-tag-trees ttree
                                         (access poly (car lst) :ttree))
                         :parents (marry-parents
                                   parents
                                   (access poly (car lst) :parents)))
                 (infect-polys (cdr lst) ttree parents)))))

(defun infect-first-n-polys (lst n ttree parents)

; We assume that parents is always (collect-parents ttree) when this is called.
; See infect-new-polys.

  (cond ((int= n 0) lst)
        (t (cons (change poly (car lst)
                         :ttree
                         (cons-tag-trees ttree
                                         (access poly (car lst) :ttree))
                         :parents (marry-parents
                                   parents
                                   (access poly (car lst) :parents)))
                 (infect-first-n-polys (cdr lst) (1- n) ttree parents)))))

(defun infect-new-polys (new-pot-lst old-pot-lst ttree)

; We must infect with ttree every poly in new-pot-lst that is not in
; old-pot-lst.  By "infect" we mean cons ttree onto the ttree of the
; poly.  However, we know that new-pot-lst is an extension of
; old-pot-lst via add-poly.  For every linear-pot in old-pot-lst there
; is a pot in the new pot-lst with the same var.  Furthermore, the
; linear pots are ordered so that by cdring down both new and old
; simultaneously when they have equal vars we keep them in step.
; Finally, every list of polys in new is an extension of its
; corresponding list in old.  I.e., the positives of some pot in new
; with the same var as a pot in old is an extension of the positives
; of that pot in old.  Hence, to visit every new poly in that list it
; suffices to visit just the first n, where n is the difference in the
; lengths of the new and old positives.

; See add-disjunct-polys-and-lemmas.

  (cond ((null new-pot-lst) nil)
        ((or (null old-pot-lst)
             (not (equal (access linear-pot (car new-pot-lst) :var)
                         (access linear-pot (car old-pot-lst) :var))))
         (let ((new-new-pot-lst
                (infect-new-polys (cdr new-pot-lst)
                                  old-pot-lst
                                  ttree)))
           (cons (modify-linear-pot
                  (car new-pot-lst)
                  (infect-polys (access linear-pot (car new-pot-lst)
                                        :positives)
                                ttree
                                (collect-parents ttree))
                  (infect-polys (access linear-pot (car new-pot-lst)
                                        :negatives)
                                ttree
                                (collect-parents ttree)))
                 new-new-pot-lst)))
        (t
         (let ((new-new-pot-lst
                (infect-new-polys (cdr new-pot-lst)
                                  (cdr old-pot-lst)
                                  ttree)))
           (cons (modify-linear-pot
                  (car new-pot-lst)
                  (infect-first-n-polys
                   (access linear-pot (car new-pot-lst) :positives)
                   (- (length (access linear-pot (car new-pot-lst)
                                      :positives))
                      (length (access linear-pot (car old-pot-lst)
                                      :positives)))
                   ttree
                   (collect-parents ttree))
                  (infect-first-n-polys
                   (access linear-pot (car new-pot-lst) :negatives)
                   (- (length (access linear-pot (car new-pot-lst)
                                      :negatives))
                      (length (access linear-pot (car old-pot-lst)
                                      :negatives)))
                   ttree
                   (collect-parents ttree)))
                 new-new-pot-lst)))))

;=================================================================


; Process-equational-polys

; Having set up the simplify-clause-pot-lst simplify clause we take
; advantage of it to find derived equalities that can help simplify
; the clause.  In this section we develop process-equational-polys.

(defun fcomplementary-multiplep1 (alist1 alist2)

; Both alists are polynomial alists, e.g., the car of each pair is a
; term and the cdr of each pair is a rational.  We determine whether
; negating each cdr in alist2 yields alist1.

  (cond ((null alist1) (null alist2))
        ((null alist2) nil)
        ((and (equal (caar alist1) (caar alist2))
              (= (cdar alist1) (- (cdar alist2))))
         (fcomplementary-multiplep1 (cdr alist1) (cdr alist2)))
        (t nil)))

(defun fcomplementary-multiplep (poly1 poly2)

; We determine whether multiplying poly2 by some negative rational
; produces poly1.  We assume that both polys have the same relation,
; e.g., <=, and the same first-var.

; Since we now normalize polys so that their first coefficient is
; +/-1.  That makes this function simpler.  In particular, we now need
; only check whether poly2 is the (arithmetic) negation of poly1.

    (and (= (access poly poly1 :constant)
            (- (access poly poly2 :constant)))
         (fcomplementary-multiplep1 (cdr (access poly poly1 :alist))
                                    (cdr (access poly poly2 :alist)))))

(defun already-used-by-find-equational-polyp-lst (poly1 lst)
  (cond ((endp lst) nil)
        (t (or (poly-equal (car (car lst)) poly1)
               (already-used-by-find-equational-polyp-lst poly1 (cdr lst))))))

(defun already-used-by-find-equational-polyp (poly1 hist)

; Poly1 is a positive poly.  Let poly2 be its negative version.  We are
; considering using them to create an equation as part of
; find-equational-poly.  We wish to know whether they have ever been
; so used before.  The answer is found by looking into the history of
; the clause being worked on, hist, for every 'simplify-clause entry.
; Each such entry is of the form (simplify-clause clause ttree).  We
; search ttree for (poly1 . poly2) tagged with 'find-equational-poly.

; Historical Note: Once upon a time, polys were not normalized in the
; sense that the leading coefficient is 1.  Thus, 2x <= 6 and 3 <= x
; were complementary.  To discover whether a poly had been used
; before, we had to know both the positive and the negative form
; involved.  But now polys are normalized and the only complement to 3
; <= x is x <= 3.  Thus, we could change the tag value to be a single
; positive poly instead of both.  You will note that we never actually
; need poly2.

  (cond ((null hist) nil)
        ((and (eq (access history-entry (car hist) :processor)
                  'simplify-clause)
              (already-used-by-find-equational-polyp-lst
               poly1
               (tagged-objects 'find-equational-poly
                               (access history-entry (car hist) :ttree))))
         t)
        (t (already-used-by-find-equational-polyp poly1 (cdr hist)))))

(defun cons-term-binary-+-constant (x term)

; x is an acl2-numberp, possibly complex, term is a rational type term.  We
; make a term equivalent to (binary-+ 'x term).

  (cond ((= x 0) term)
        ((quotep term) (kwote (+ x (cadr term))))
        (t (fcons-term* 'binary-+ (kwote x) term))))

(defun cons-term-unary-- (term)
  (cond ((variablep term) (fcons-term* 'unary-- term))
        ((fquotep term) (kwote (- (cadr term))))
        ((eq (ffn-symb term) 'unary--) (fargn term 1))
        (t (fcons-term* 'unary-- term))))

(defun cons-term-binary-*-constant (x term)

; x is a number (possibly complex), term is a rational type term.  We make a
; term equivalent to (binary-* 'x term).

  (cond ((= x 0) (kwote 0))
        ((= x 1) term)
        ((= x -1) (cons-term-unary-- term))
        ((quotep term) (kwote (* x (cadr term))))
        (t (fcons-term* 'binary-* (kwote x) term))))

(defun find-equational-poly-rhs1 (alist)

; See find-equational-poly-rhs.

  (cond ((null alist) *0*)
        ((null (cdr alist))
         (cons-term-binary-*-constant (- (cdar alist))
                                      (caar alist)))
        (t (cons-term 'binary-+
                      (list
                       (cons-term-binary-*-constant (- (cdar alist))
                                                    (caar alist))
                       (find-equational-poly-rhs1 (cdr alist)))))))

(defun find-equational-poly-rhs (poly1)

; Suppose poly1 and poly2 are complementary multiple <= polys, as
; described in find-equational-poly.  We wish to form the rhs term
; returned by that function.  We know the two polys have the form

; poly1:   k0 + k1*t1 + k2*t2 ... <= 0,      k1 positive
; poly2    j0 + j1*t1 + j2*t2 ... <= 0,      j1 negative

; and if q = k1/j1 then q is negative and ji*q = -ki for each i.

; Thus, k0 + k1*t1 + k2*t2 ... = 0.

; The equation created by find-equational-poly will be lhs = rhs, where lhs
; is t1.  We are to create rhs.  That is:

; rhs = -k0/k1 - k2/k1*t2 ...

; which, if we let c be -1/k1

; rhs = (+ c*k0 (+ c*k2*t2 ...))

; which is what we return.

; However now that we normalize polys, k1 = 1 and j1 = -1, so that q =
; -1 and c = -1.  Hence we now negate, rather than multiplying by c.

  (cons-term-binary-+-constant (- (access poly poly1 :constant))
                               (find-equational-poly-rhs1
                                (cdr (access poly poly1 :alist)))))

(defun find-equational-poly3 (poly1 poly2 hist)

; See find-equational-poly.  This is the function that actually builds
; the affirmative answer returned by that function.  Between this function
; and that one are two others whose only job is to iterate across all the
; potentially acceptable positives and negatives and give to this function
; a potentially appropriate poly1 and poly2.

; We know that poly1 is a positive <= poly that does not descend from
; a (not (equal & &)).  We know that poly2 is a negative <= poly that
; does not descend from a (not (equal & &)).  We know they have the same
; first-var.

; We first determine whether they are complementary multiples of eachother
; and have not been used by find-equational-poly already.  If so, we
; return a ttree and two terms, as described by find-equational-poly.

  (cond ((and (fcomplementary-multiplep poly1 poly2)
              (not (already-used-by-find-equational-polyp poly1 hist)))
         (mv (add-to-tag-tree
              'find-equational-poly
              (cons poly1 poly2)
              (cons-tag-trees (access poly poly1 :ttree)
                              (access poly poly2 :ttree)))
             (first-var poly1)
             (find-equational-poly-rhs poly1)))
        (t (mv nil nil nil))))

(defun find-equational-poly2 (poly1 negatives hist)

; See find-equational-poly.  Poly1 is a positive <= poly with the same
; first var as all the members of negatives.  We scan negatives looking
; for a poly2 that is acceptable.

  (cond
   ((null negatives)
    (mv nil nil nil))
   ((or (not (eq (access poly (car negatives) :relation) '<=))
        (access poly (car negatives) :derived-from-not-equalityp))
    (find-equational-poly2 poly1 (cdr negatives) hist))
   (t
    (mv-let (msg lhs rhs)
      (find-equational-poly3 poly1 (car negatives) hist)
      (cond
       (msg (mv msg lhs rhs))
       (t (find-equational-poly2 poly1 (cdr negatives)
                                 hist)))))))

(defun find-equational-poly1 (positives negatives hist)

; See find-equational-poly.  Positives and negatives are the
; appropriate fields of the same linear pot.  All the first-vars are
; equal.  We scan the positives and for each <= poly there we look for
; an acceptable member of the negatives.

  (cond
   ((null positives)
    (mv nil nil nil))
   ((or (not (eq (access poly (car positives) :relation) '<=))
        (access poly (car positives) :derived-from-not-equalityp))
    (find-equational-poly1 (cdr positives) negatives hist))
   (t
    (mv-let (msg lhs rhs)
      (find-equational-poly2 (car positives) negatives hist)
      (cond
       (msg (mv msg lhs rhs))
       (t (find-equational-poly1 (cdr positives) negatives hist)))))))

(defun find-equational-poly (pot hist)

; Look for an equation to be derived from this pot.  We look for a
; weak inequality in positives whose negation is a member of
; negatives, which was not the result of linearizing a (not (equal lhs
; rhs)), and which has never been found (and recorded in hist) before.
; The message we look for is our business (we generate and recognize
; them) but they must be in the tag-tree stored in the 'simplify-clause
; entries of hist.

; We return three values.  If we find no acceptable poly, we return
; three nils.  Otherwise we return a non-nil ttree and two terms, lhs
; and rhs.  In this case, it is a truth (assuming pot and the
; 'assumptions in the ttree) that lhs = rhs.  As a matter of fact, lhs
; will be the var of the linear-pot pot and rhs will be a +-tree of
; lighter vars.  Of course, the equation can be rearranged and used
; arbitrarily by the caller.

; If the equation is used in the current simplification, the ttree we
; return must find its way into the hist entry for that
; simplify-clause.

; Historical note: The affect of the newly (v2_8) introduced field,
; :derived-from-not-equalityp, is different from that of the
; earlier function descends-from-not-equalityp.  We are now more
; liberal about the polys we can generate here.  See the discussion
; accompanying the definition of a poly.  (Search for ``(defrec poly''.))

  (find-equational-poly1 (access linear-pot pot :positives)
                         (access linear-pot pot :negatives)
                         hist))

;=================================================================


; Add-polys

(defun get-coeff-for-cancel1 (alist1 alist2)

; Alist1 and alist2 are the alists from two polys which we are about
; to cancel.  We calculate the absolute value of what would be the
; leading coefficient if we added the two alists.  This is in support
; of cancel, which see.

  (cond ((null alist1)
         (if (null alist2)
             1
           (abs (cdar alist2))))
        ((null alist2)
         (abs (cdar alist1)))
        ((not (arith-term-order (caar alist1) (caar alist2)))
         (abs (cdar alist1)))
        ((equal (caar alist1) (caar alist2))
         (let ((temp (+ (cdar alist1)
                        (cdar alist2))))
           (if (eql temp 0)
               (get-coeff-for-cancel1 (cdr alist1) (cdr alist2))
             (abs temp))))
        (t
         (abs (cdar alist2)))))

(defun cancel2 (alist coeff)
  (cond ((null alist)
         nil)
        (t
         (cons (cons (caar alist)
                     (/ (cdar alist) coeff))
               (cancel2 (cdr alist) coeff)))))

(defun cancel1 (alist1 alist2 coeff)

; Alist1 and alist2 are the alists from two polys which we are about
; to cancel.  We create a new alist by adding alist1 and alist2, using
; coeff to normalize the result.

  (cond ((null alist1)
         (cancel2 alist2 coeff))
        ((null alist2)
         (cancel2 alist1 coeff))
        ((not (arith-term-order (caar alist1) (caar alist2)))
         (cons (cons (caar alist1)
                     (/ (cdar alist1) coeff))
               (cancel1 (cdr alist1) alist2 coeff)))
        ((equal (caar alist1) (caar alist2))
         (let ((temp (/ (+ (cdar alist1)
                           (cdar alist2))
                        coeff)))
           (cond ((= temp 0)
                  (cancel1 (cdr alist1) (cdr alist2) coeff))
                 (t (cons (cons (caar alist1) temp)
                          (cancel1 (cdr alist1) (cdr alist2) coeff))))))
        (t (cons (cons (caar alist2)
                       (/ (cdar alist2) coeff))
                 (cancel1 alist1 (cdr alist2) coeff)))))

(defun cancel (p1 p2)

; P1 and p2 are polynomials with the same first var and opposite
; signs.  We construct the poly obtained by cross-multiplying and
; adding p1 and p2 so as to cancel out the first var.

; Polys are now normalized such that the leading coefficients are
; +/-1.  Hence we no longer need to cross-multiply before adding
; p1 and p2.  (The variables co1 and co2 in the original version
; are now guaranteed to be 1.)  We do add a twist to the naive
; implementation though.  Rather than adding the two alists, and
; then normalizing the result, we calculate what would have been
; the leading coeficient and normalize as we go (dividing by its
; absolute value).

; We return two values.  The first indicates whether we have
; discovered a contradiction.  If the first result is non-nil then it
; is the impossible poly formed by cancelling p1 and p2.  The ttree of
; that poly will be interesting to our callers because it contains
; such things as the assumptions made and the lemmas used to get the
; contradiction.  When we return a contradiction, the second result is
; always nil.  Otherwise, the second result is either nil (meaning that
; the cancellation yeilded a trivially true poly) or is the newly
; formed poly.

; Historical note: The affect of the newly (v2_8) introduced field,
; :derived-from-not-equalityp, is different from that of the
; earlier function descends-from-not-equalityp.  See the discussion
; accompanying the definition of a poly.  (Search for ``(defrec poly''.))

; Note:  It is sometimes convenient to trace this function with

;   (trace (cancel
;           :entry (list (show-poly (car si::arglist))
;                        (show-poly (cadr si::arglist)))
;           :exit (let ((flg (car values))
;                       (val (car (mv-refs 1))))
;                   (cond (flg (append values (mv-refs 1)))
;                         (val (list nil (show-poly val)))
;                         (t (list nil nil))))))

; Since we now normalize polys, the cars of the two alists will
; cancel each other out and all we have to concern ourselves with
; are their cdrs.

  (let* ((alist1 (cdr (access poly p1 :alist)))
         (alist2 (cdr (access poly p2 :alist)))
         (coeff (get-coeff-for-cancel1 alist1 alist2))
         (p (make poly
                  :constant (/ (+ (access poly p1 :constant)
                                  (access poly p2 :constant))
                               coeff)
                  :alist (cancel1 alist1
                                  alist2
                                  coeff)
                  :relation  (if (or (eq (access poly p1 :relation) '<)
                                     (eq (access poly p2 :relation) '<))
                                 '<
                               '<=)
                  :ttree (cons-tag-trees (access poly p1 :ttree)
                                         (access poly p2 :ttree))
                  :rational-poly-p (and (access poly p1 :rational-poly-p)
                                        (access poly p2 :rational-poly-p))
                  :parents (marry-parents (access poly p1 :parents)
                                          (access poly p2 :parents))
                  :derived-from-not-equalityp nil)))
    (cond ((impossible-polyp p) (mv p nil))
          ((true-polyp p) (mv nil nil))
          (t (mv nil p)))))

(defun cancel-poly-against-all-polys (p polys pt ans)

; P is a poly, polys is a list of polys, the first var of p is the same
; as the first of every poly in polys and has opposite sign.  We are to
; cancel p against each member of polys, getting in each case a
; contradiction, a true poly (which we discard) or a new shorter poly.
; Pt is a parent tree indicating literals we are to avoid.

; We return two answers.  The first is either nil or the first
; contradiction we find.  When the first is a contradiction, the
; second is nil.  Otherwise, the second is the list of all newly
; produced polys.

; Ans is supposed to be nil initially and is the site at which we
; accumulate the new polys.  This is a No-Change Loser.

  (cond ((null polys)
         (mv nil ans))
        ((ignore-polyp (access poly (car polys) :parents) pt)
         (cancel-poly-against-all-polys p (cdr polys) pt ans))
        (t (mv-let (contradictionp new-p)
             (cancel p (car polys))
             (cond (contradictionp
                    (mv contradictionp nil))
                   (t
                    (cancel-poly-against-all-polys
                     p
                     (cdr polys)
                     pt

; We discard polys which are ``weaker'' (see poly-member and
; poly-weakerp) than one already accumulated into ans.

                     (if (and new-p
                              (not (poly-member new-p ans)))
                         (cons new-p ans)
                       ans))))))))

; Historical note:

; The following functions --- add-polys0 and its callees --- have been
; substantially rewritten.  Previous to Version_2.8 the following
; two comments were in add-poly and add-poly1 (which no longer exists)
; respectively:

; Add-poly historical comment

; ; This is the fundamental function for changing a pot-lst.  It adds a
; ; single poly p to pot-lst.  All the other functions which construct
; ; pot lists do it, ultimately, via calls to add-poly.
;
; ; In nqthm this function was called add-equation but since its argument
; ; is a poly we renamed it.
;
; ; This function adds a poly p to the pot-lst.  Since the pot-lst is
; ; ordered by term-order on the vars, we recurse down the pot-lst just
; ; far enough to find where p fits.  There are three cases: p goes
; ; before the current pot, p goes in the current pot, or p goes after
; ; the current pot.  The first is simplest: make a pot for p and stick
; ; it at the front of the pot-lst.  The second is not too bad: cancel p
; ; against every poly of opposite sign in this pot to generate a bunch
; ; of new polys that belong earlier in the pot-lst and then add p to
; ; the current pot.  The third is the worst: Recursively add p to the
; ; rest of the pot-lst, get back a bunch of polys that need processing,
; ; process the ones that belong where you're standing and pass up the
; ; ones that go earlier.

; Add-poly1 historical comment

; ; This is a subroutine of add-poly.  See the comment there.  Suppose
; ; we've just gotten back from a recursive call of add-poly and it
; ; returned to us a bunch of polys that belong earlier in the pot-lst
; ; (from it).  Some of those polys may belong here where we are
; ; standing.  Others should be passed up.
;
; ; To-do is the list of polys produced by the recursive add-poly.  Var,
; ; positives, and negatives are the appropriate components of the pot
; ; that add-poly is standing on.  We process those polys in to-do that
; ; go here, producing new positives and negatives, and set aside those
; ; that don't go here.  The processing of the ones that do go here may
; ; create some additional polys that don't go here.  To-do-next is the
; ; accumulation site for the to-do's we don't handle and the ones our
; ; processing creates.

; Add-poly is still the fundamental routine for adding a poly to the
; pot-lst.  However, we now merely gather up newly generated polys and
; pass them back out to add-polys --- changing the routines which
; add polys to the pot list from a depth-first search to a
; breadth-first search.

(defun add-poly (p pot-lst to-do-next pt nonlinearp)

; This is the fundamental function for changing a pot-lst.  It adds a
; single poly p to pot-lst.  All the other functions which construct
; pot lists do it, ultimately, via calls to add-poly.

; This function adds a poly p to the pot-lst and returns 3 values.
; The first is the standard contradictionp.  The second value, of
; interest only when we don't find a contradiction, is the new pot-lst
; obtained by adding p to pot-lst.  The third value is a list of new
; polys generated by the adding of p to pot-lst, which must be
; processed.  We cons our own generated polys onto the incoming
; to-do-next to form this result.

; An invariant exploited by infect-new-polys is that all of the new
; polys in any linear pot occur at the front of the list and no polys
; are ever deleted.  That is, if this or any other function wants to
; add a poly to the positives, say, it must cons it onto the front.
; In general, if we have an old linear pot and a new one produced from
; it and we want to process all the polys in the positives, say, of the
; new pot that are not in the old one, it suffices to process the first
; n elements of the new positives, where n is the difference in their
; lengths.

; Note:  If adding a poly creates a new pot, its loop-stopper value is set to
; 0.  This is changed to the correct value (if necessary) in
; add-linear-lemma.

; Trace Note:
;   (trace (add-poly
;           :entry (let ((args si::arglist))
;                    (list (show-poly (nth 0 args)) ;p
;                          (show-pot-lst (nth 1 args)) ;pot-lst
;                          (show-poly-lst (nth 2 args)) ;to-do-next
;                          (nth 3 args)
;                          (nth 4 args)
;                          '|ens| (nth 6 args) '|wrld|))
;           :exit (cond ((null (car values))
;                        (list nil
;                              (show-pot-lst (mv-ref 1))
;                              (show-poly-lst (mv-ref 2))))

  (cond
   ((time-limit5-reached-p
     "Out of time in linear arithmetic (add-poly).") ; nil, or throws
    (mv nil nil nil))
   ((or (null pot-lst)
        (not (arith-term-order (access linear-pot (car pot-lst) :var)
                               (first-var p))))
    (mv nil
        (cons (if (< 0 (first-coefficient p)) ; p is normalized (below too)
                  (make linear-pot
                        :var (first-var p)
                        :loop-stopper-value 0
                        :positives (list p)
                        :negatives nil)
                (make linear-pot
                      :var (first-var p)
                      :loop-stopper-value 0
                      :positives nil
                      :negatives (list p)))
              pot-lst)
        to-do-next))
   ((equal (access linear-pot (car pot-lst) :var)
           (first-var p))
    (cond
     ((poly-member p
                   (if (< 0 (first-coefficient p))
                       (access linear-pot (car pot-lst) :positives)
                     (access linear-pot (car pot-lst) :negatives)))
      (mv nil pot-lst to-do-next))
     (t (mv-let (contradictionp to-do-next)
          (cancel-poly-against-all-polys
           p
           (if (< 0 (first-coefficient p))
               (access linear-pot (car pot-lst) :negatives)
             (access linear-pot (car pot-lst) :positives))
           pt
           to-do-next)
          (cond
           (contradictionp (mv contradictionp nil nil))

; Non-linear optimization
; Magic number.  If non-linear arithmetic is enabled, and there are
; more than 20 polys in the appropriate side of the pot, we give up
; and do not add the new poly.  This has proven to be a useful heuristic.
; Increasing this number will slow ACL2 down sometimes, but it may
; allow more proofs to go through.  So far I have not seen one which
; needs more than 20, but less than 100 --- which is too much.
; Note that the pot-lst isn't changed (i.e., poly wasn't added to its
; pot) but we will propagate the children poly and (possibly) add them
; to their pots.  These children are "orphans" because a parent is
; missing from the pot-lst.


           ((and nonlinearp
                 (>=-len (if (< 0 (first-coefficient p))
                             (access linear-pot (car pot-lst)
                                     :positives)
                           (access linear-pot (car pot-lst)
                                   :negatives))
                         21))
            (mv nil
                pot-lst
                to-do-next))
           (t (mv nil
                  (cons
                   (if (< 0 (first-coefficient p))
                       (change linear-pot (car pot-lst)
                               :positives
                               (cons p (access linear-pot (car pot-lst)
                                               :positives)))
                     (change linear-pot (car pot-lst)
                             :negatives
                             (cons p (access linear-pot (car pot-lst)
                                             :negatives))))
                   (cdr pot-lst))
                  to-do-next)))))))
   (t
    (mv-let
      (contradictionp cdr-pot-lst to-do-next)
      (add-poly p (cdr pot-lst) to-do-next pt nonlinearp)
      (cond
       (contradictionp (mv contradictionp nil nil))
       (t
        (mv nil (cons (car pot-lst) cdr-pot-lst) to-do-next)))))))

(defun prune-poly-lst (poly-lst ans)
  (cond ((null poly-lst)
         ans)
        ((endp (cddr (access poly (car poly-lst) :alist)))
         (prune-poly-lst (cdr poly-lst) (cons (car poly-lst) ans)))
        (t
         (prune-poly-lst (cdr poly-lst) ans))))

(defun add-polys1 (lst pot-lst new-lst pt nonlinearp max-rounds
                       rounds-completed)

; This function adds every element of the poly list lst to pot-lst and
; accumulates the new polys in new-lst.  When lst is exhausted it
; starts over on the ones in new-lst and iterates that until no new polys
; are produced.  It returns 2 values:  the standard contradictionp in the
; the first and the final pot-lst in the second.

  (cond ((eql max-rounds rounds-completed)
         (mv nil pot-lst))
        ((null lst)
         (cond ((null new-lst)
                (mv nil pot-lst))

; Non-linear optimization
; Magic number.  If non-linear arithmetic is enabled, and there are
; more than 100 polys in lst waiting to be added to the pot-lst, we
; try pruning the list of new polys.  This has proven to be a useful
; heuristic.  Increasing this number will slow ACL2 down sometimes,
; but it may allow more proofs to go through.  So far I have not seen
; one which needs more than 100, but less than 500 --- which is too
; much.  After Version_5.0, we eliminated the nonlinearp condition
; and prune when there are more than 100 polys in the new list.

               ((and ; nonlinearp
                     (>=-len new-lst 101))
                (add-polys1 (prune-poly-lst new-lst nil)
                            pot-lst nil pt nonlinearp
                            max-rounds (+ 1 rounds-completed)))
               (t
                (add-polys1 new-lst pot-lst nil
                            pt nonlinearp
                            max-rounds (+ 1 rounds-completed)))))
        (t (mv-let (contradictionp new-pot-lst new-lst)
             (add-poly (car lst) pot-lst new-lst pt nonlinearp)
             (cond (contradictionp (mv contradictionp nil))
                   (t (add-polys1 (cdr lst)
                                  new-pot-lst
                                  new-lst
                                  pt
                                  nonlinearp
                                  max-rounds
                                  rounds-completed)))))))

(defun add-polys0 (lst pot-lst pt nonlinearp max-rounds)

; Lst is a list of polys.  We filter out the true ones (and detect any
; impossible ones) and then normalize and add the rest to pot-lst.
; Any new polys thereby produced are also added until there's nothing
; left to do.  We return the standard contradictionp and a new pot-lst.

  (mv-let (contradictionp lst)
    (filter-polys lst nil)
    (cond (contradictionp (mv contradictionp nil))
          (t (add-polys1 lst pot-lst nil pt nonlinearp max-rounds 0)))))

;=================================================================

; "Show-" functions

; The next group of "show-" functions is convenient for system debugging and is
; used (specifically, show-poly-lst is used) by brr.  (Show-poly poly) will
; create a list structure that prints so as to show a polynomial in the
; conventional notation.  The term enclosed in an extra set of parentheses is
; the leading term of the poly.  An example show-poly is '(3 J + (I) + 77 <= 4
; M + 2 N).

(defun show-poly2 (pair lst)
  (let ((n (abs (cdr pair)))
        (x (car pair)))
    (cond ((= n 1) (cond ((null lst) (list x))
                         (t (list* x '+ lst))))
          (t (cond ((null lst) (list n x))
                   (t (list* n x '+ lst)))))))

(defun show-poly1 (alist lhs rhs)

; Note: This function ought to return (mv lhs rhs) but when it is used in
; tracing multiply valued functions that functionality hurts us: the
; computation performed during the tracing destroys the multiple value being
; manipulated by the function being traced.  So that we can use this function
; conveniently during tracing, we make it a single valued function.

  (cond ((null alist) (cons lhs rhs))
        ((logical-< 0 (cdar alist))
         (show-poly1 (cdr alist) lhs (show-poly2 (car alist) rhs)))
        (t (show-poly1 (cdr alist) (show-poly2 (car alist) lhs) rhs))))

(defun show-poly (poly)
  (let* ((pair (show-poly1
                   (cond ((null (access poly poly :alist)) nil)
                         (t (cons (cons (list (caar (access poly poly :alist)))
                                        (cdar (access poly poly :alist)))
                                  (cdr (access poly poly :alist)))))
                   (cond ((= (access poly poly :constant) 0)
                          nil)
                         ((logical-< 0 (access poly poly :constant)) nil)
                         (t (cons (- (access poly poly :constant)) nil)))
                   (cond ((= (access poly poly :constant) 0)
                          nil)
                         ((logical-< 0 (access poly poly :constant))
                          (cons (access poly poly :constant) nil))
                         (t nil))))
         (lhs (car pair))
         (rhs (cdr pair)))

; The let* above would be (mv-let (lhs rhs) (show-poly1 ...) ...) had
; show-poly1 been specified to return two values instead of a pair.
; See note above.

    (append (or lhs '(0))
            (cons (access poly poly :relation) (or rhs '(0))))))

(defun show-poly-lst (poly-lst)
  (cond ((null poly-lst) nil)
        (t (cons (show-poly (car poly-lst))
                 (show-poly-lst (cdr poly-lst))))))

;
; (defun show-pot-lst (pot-lst)
;   (cond
;    ((null pot-lst) nil)
;    (t (cons
;        (list* :var (access linear-pot (car pot-lst) :var)
;               (append (show-poly-lst
;                        (access linear-pot (car pot-lst) :negatives))
;                       (show-poly-lst
;                        (access linear-pot (car pot-lst) :positives))))
;        (show-pot-lst (cdr pot-lst))))))
;
; (defun show-type-alist (type-alist)
;   (cond ((endp type-alist) nil)
;         (t (cons (list (car (car type-alist))
;                        (decode-type-set (cadr (car type-alist))))
;                  (show-type-alist (cdr type-alist))))))
;
;
; (defun number-of-polys (pot-lst)
;   (cond ((null pot-lst) 0)
;         (t (+ (len (access linear-pot (car pot-lst) :negatives))
;               (len (access linear-pot (car pot-lst) :positives))
;               (number-of-polys (cdr pot-lst))))))

