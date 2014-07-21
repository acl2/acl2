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

; Essay on Tag-Trees

; If you add a new tag, be sure to include it in all-runes-in-ttree!

; Tags in Tag-Trees

; After Version_4.2 we switched to a representation of a tag-tree as an alist,
; associating a key with a non-empty list of values, rather than building up
; tag-trees with operations (acons tag value ttree) and (cons ttree1 ttree2).
; Note that we view these lists as sets, and are free to ignore order and
; duplications (though we attempt to avoid duplicates).   Our motivation was to
; allow the addition of a new key, associated with many values, without
; degrading performance significantly.

; Each definition of a primitive for manipulating tag-trees has the comment: "
; Note: Tag-tree primitive".

; See all-runes-in-ttree for the set of all legal tags and their associated
; values.  Some of the tags and associated values are as follows.

; 'lemma

; The tagged object is either a lemma name (a symbolp) or else is the
; integer 0 indicating the use of linear arithmetic.

; 'pt

; The tagged object is a "parent tree".  See the Essay on Parent Trees.
; The tree identifies a set of literals in the current-clause of
; simplify-clause1 used in the derivation of poly or term with which the
; tree is associated.  We need this information for two reasons.  First,
; in order to avoid tail biting (see below) we do not use any poly that
; descends from the assumption of the falsity of the literal we are trying
; to prove.  Second, in find-equational-poly we seek two polys that can be
; combined to derive an equality, and we use 'pt to identify those that
; themselves descend from equality hypotheses.

; 'assumption

; The tagged object is an assumption record containing, among other things, a
; type-alist and a term which must be true under the type-alist in order to
; assure the validity of the poly or rewrite with which the tree is associated.
; We cannot linearize (- x), for example, without knowing (rationalp x).  If we
; cannot establish it by type set reasoning, we add that 'assumption to the
; poly generated.  If we eventually use the poly in a derivation, the
; 'assumption will infect it and when we get up to the simplify-clause level we
; will split on them.

; 'find-equational-poly

; The tagged object is a pair of polynomials.  During simplify clause
; we try to find two polys that can be combined to form an equation we
; don't have explicitly in the clause.  If we succeed, we add the
; equation to the clause.  However, it may be simplified into
; unrecognizable form and we need a way to avoid re-generation of the
; equation in future calls of simplify.  We do this by infecting the
; tag-tree with this tag and the two polys used.

; Historical Note from the days when tag-trees were constructed using (acons
; tag value ttree) and (cons-tag-trees ttree1 ttree2):

; ; The invention of tag-trees came about during the designing of the linear
; ; package.  Polynomials have three "arithmetic" fields, the constant, alist,
; ; and relation.  But they then have many other fields, like lemmas,
; ; assumptions, and literals.  At the time of this writing they have 5 other
; ; fields.  All of these fields are contaminants in the sense that all of the
; ; contaminants of a poly contaminate any result formed from that poly.  The
; ; same is true with the second answer of rewrite.

; ; If we represented the 5-tuple of the ttree of a poly as full-fledged fields
; ; in the poly the best we could do is to use a balanced binary tree with 8
; ; tips.  In that case the average time to change some field (including the
; ; time to cons a new element onto any of the 5 contaminants) is 3.62 conses.
; ; But if we clump all the contaminants into a single field represented as a
; ; tag-tree, the cost of adding a single element to any one of them is 2
; ; conses and the average cost of changing any of the 4 fields in a poly is
; ; 2.5 conses.  Furthermore, we can effectively union all 5 contaminants of
; ; two different polys in one cons!

; The following function determines whether val with tag tag occurs in
; tree:

(defun tag-tree-occur (tag val ttree)

; Note: Tag-tree primitive

  (let ((pair (assoc-eq tag ttree)))
    (and pair ; optimization
         (member-equal val (cdr pair)))))

(defun remove-tag-from-tag-tree (tag ttree)

; Note: Tag-tree primitive

; In this function we do not assume that tag is a key of ttree.  See also
; remove-tag-from-tag-tree, which does make that assumption.

  (cond ((assoc-eq tag ttree)
         (delete-assoc-eq tag ttree))
        (t ttree)))

(defun remove-tag-from-tag-tree! (tag ttree)

; Note: Tag-tree primitive

; In this function we assume that tag is a key of ttree.  See also
; remove-tag-from-tag-tree, which does not make that assumption.

  (delete-assoc-eq tag ttree))

; To add a tagged object to a tree we use the following function.  Observe
; that it does nothing if the object is already present.

; Note:
; If you add a new tag, be sure to include it in all-runes-in-ttree!

(defmacro extend-tag-tree (tag vals ttree)

; Note: Tag-tree primitive

; Warning: We assume that tag is not a key of ttree and vals is not nil.

  `(acons ,tag ,vals ,ttree))

(defun maybe-extend-tag-tree (tag vals ttree)

; Warning: We assume that tag is not a key of ttree.

  (cond ((null vals) ttree)
        (t (extend-tag-tree tag vals ttree))))

(defun add-to-tag-tree (tag val ttree)

; Note: Tag-tree primitive

; See also add-to-tag-tree!, for the case that tag is known not to be a key of
; ttree.

  (cond
   ((eq ttree nil) ; optimization
    (list (list tag val)))
   (t
    (let ((pair (assoc-eq tag ttree)))
      (cond (pair (cond ((member-equal val (cdr pair))
                         ttree)
                        (t (acons tag
                                  (cons val (cdr pair))
                                  (remove-tag-from-tag-tree! tag ttree)))))
            (t (acons tag (list val) ttree)))))))

(defun add-to-tag-tree! (tag val ttree)

; Note: Tag-tree primitive

; It is legal (and more efficient) to use this instead of add-to-tag-tree if we
; know that tag is not a key of ttree.

  (extend-tag-tree tag (list val) ttree))

; A Little Foreshadowing:

; We will soon introduce the notion of a "rune" or "rule name."  To
; each rune there corresponds a numeric equivalent, or "nume," which
; is the index into the "enabled structure" for the named rule.  We
; push runes into ttrees under the 'lemma property to record their
; use.

; We have occasion for "fake-runes" which look like runes but are not.
; See the Essay on Fake-Runes below.  One such rune is shown below,
; and is the name of otherwise anonymous rules that are always considered
; enabled.  When this rune is used, its use is not recorded in the
; tag-tree.

(defconst *fake-rune-for-anonymous-enabled-rule*
  '(:FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE nil))

(defabbrev push-lemma (rune ttree)

; This is just (add-to-tag-tree 'lemma rune ttree) and is named in honor of the
; corresponding act in Nqthm.  We do not record uses of the fake rune.  Rather
; than pay the price of recognizing the *fake-rune-for-anonymous-enabled-rule*
; perfectly we exploit the fact that no true rune has
; :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE as its token.

  (cond ((eq (car rune) :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE) ttree)
        (t (add-to-tag-tree 'lemma rune ttree))))

; Historical Note from the days when tag-trees were constructed using (acons
; tag value ttree) and (cons-tag-trees ttree1 ttree2):

; ; To join two trees we use cons-tag-trees.  Observe that if the first tree is
; ; nil we return the second (we can't cons a nil tag-tree on and their union
; ; is the second anyway).  Otherwise we cons, possibly duplicating elements.

; ; But starting in Version_3.2, we keep tagged objects unique in tag-trees, by
; ; calling scons-tag-trees when necessary, unioning the tag-trees rather than
; ; merely consing them.  The immediate prompt for this change was a report
; ; from Eric Smith on getting stack overflows from tag-tree-occur, but this
; ; problem has also occurred in the past (as best Matt can recall).

(defun delete-assoc-eq-assoc-eq-1 (alist1 alist2)
  (declare (xargs :guard (and (symbol-alistp alist1)
                              (symbol-alistp alist2))))
  (cond ((endp alist2)
         (mv nil nil))
        (t (mv-let (changedp x)
                   (delete-assoc-eq-assoc-eq-1 alist1 (cdr alist2))
                   (cond ((assoc-eq (caar alist2) alist1)
                          (mv t x))
                         (changedp
                          (mv t (cons (car alist2) x)))
                         (t (mv nil alist2)))))))

(defun delete-assoc-eq-assoc-eq (alist1 alist2)
  (mv-let (changedp x)
          (delete-assoc-eq-assoc-eq-1 alist1 alist2)
          (declare (ignore changedp))
          x))

(defun cons-tag-trees1 (ttree1 ttree2 ttree3)

; Note: Tag-tree primitive supporter

; Accumulate into ttree3, whose keys are disjoint from those of ttree1, the
; values of keys in ttree1 each augmented by their values in ttree2.

; It might be more efficient to accumulate into ttree3, so that this function
; is tail-recursive.  But we prefer that the tags at the front of ttree1 are
; also at the front of the returned ttree, since presumably the values of those
; tags are more likely to be updated frequently, and an update generates fewer
; conses the closer the tag is to the front of the ttree.

  (cond ((endp ttree1) ttree3)
        (t (let ((pair (assoc-eq (caar ttree1) ttree2)))
             (cond (pair (acons (caar ttree1)
                                (union-equal (cdar ttree1) (cdr pair))
                                (cons-tag-trees1 (cdr ttree1) ttree2 ttree3)))
                   (t (cons (car ttree1)
                            (cons-tag-trees1 (cdr ttree1) ttree2 ttree3))))))))

(defun cons-tag-trees (ttree1 ttree2)

; Note: Tag-tree primitive

; We return a tag-tree whose set of keys is the union of the keys of ttree1 and
; ttree2, and whose value for each key is the union of the values of the key in
; ttree1 and ttree2 (in that order).  In addition, we attempt to avoid needless
; consing.

  (cond ((null ttree1) ttree2)
        ((null ttree2) ttree1)
        ((null (cdr ttree2))
         (let* ((pair2 (car ttree2))
                (tag (car pair2))
                (pair1 (assoc-eq tag ttree1)))
           (cond (pair1 (acons tag
                               (union-equal (cdr pair1) (cdr pair2))
                               (delete-assoc-eq tag ttree1)))
                 (t (cons pair2 ttree1)))))
        (t (let ((ttree3 (delete-assoc-eq-assoc-eq ttree1 ttree2)))
             (cons-tag-trees1 ttree1 ttree2 ttree3)))))

(defun map-cons-tag-trees (lst ttree)

; Cons-tag-tree every element of lst into ttree.

  (cond ((null lst) ttree)
        (t (map-cons-tag-trees (cdr lst)
                               (cons-tag-trees (car lst) ttree)))))

(defmacro tagged-objects (tag ttree)

; Note: Tag-tree primitive

; See also tagged-objectsp for a corresponding predicate.

  `(cdr (assoc-eq ,tag ,ttree)))

(defmacro tagged-objectsp (tag ttree)

; Note: Tag-tree primitive

; This is used instead of tagged-objects (but is Boolean equivalent to it) when
; we want to emphasize that our only concern is whether or not there is at
; least one tagged object associated with tag in ttree.

  `(assoc-eq ,tag ,ttree))

(defun tagged-object (tag ttree)

; Note: Tag-tree primitive

; This function returns obj for the unique obj associated with tag in ttree, or
; nil if there is no object with that tag.  If there may be more than one
; object associated with tag in ttree, use (car (tagged-objects tag ttree))
; instead to obtain one such object, or use (tagged-objectsp tag ttree) if you
; only want to answer the question "Is there any object associated with tag in
; ttree?".

  (let ((objects (tagged-objects tag ttree)))
    (and objects
         (assert$ (null (cdr objects))
                  (car objects)))))

; We accumulate our ttree into the state global 'accumulated-ttree so that if a
; proof attempt is aborted, we can still recover the lemmas used within it.  If
; we know a ttree is going to be part of the ttree returned by a successful
; event, then we want to store it in state.  We are especially concerned about
; storing a ttree if we are about to inform the user, via output, that the
; runes in it have been used.  (That is, we want to make sure that if a proof
; fails after the system has reported using some rune then that rune is tagged
; as a 'lemma in the 'accumulated-ttree of the final state.)  This encourages
; us to cons a new ttree into the accumulator every time we do output.

(deflock *ttree-lock*)

(defun@par accumulate-ttree-and-step-limit-into-state (ttree step-limit state)

; We add ttree to the 'accumulated-ttree in state and return an error triple
; whose value is ttree.  Before Version_3.2 we handled tag-trees a bit
; differently, allowing duplicates and using special markers for portions that
; had already been accumulated into state.  Now we keep tag-trees
; duplicate-free and avoid adding such markers to the returned value.

; We similarly save the given step-limit in state, unless its value is :skip.

  (declare (ignorable state))
  (pprogn@par
   (cond ((eq step-limit :skip) (state-mac@par))
         (t

; Parallelism no-fix: the following call of (f-put-global@par 'last-step-limit
; ...) may be overridden by another similar call performed by a concurrent
; thread.  But we can live with that because step-limits do not affect
; soundness.

          (f-put-global@par 'last-step-limit step-limit state)))
   (cond
    ((eq ttree nil) (value@par nil))
    (t (pprogn@par
        (with-ttree-lock

; In general, it is dangerous to set the same state global in two different
; threads, because the first setting is blown away by the second.  But here, we
; are _accumulating_ into a state global (namely, 'accumulated-ttree), and we
; don't care about the order in which the accumulation occurs (even though such
; nondeterminism isn't explained logically -- after all, we are modifying state
; without passing it in, so we already are punting on providing a logical story
; here).  Our only concern is that two such accumulations interfere with each
; other, but the lock just above takes care of that (i.e., provides mutual
; exclusion).

         (f-put-global@par 'accumulated-ttree
                           (cons-tag-trees ttree
                                           (f-get-global 'accumulated-ttree
                                                         state))
                           state))
        (value@par ttree))))))

(defmacro tag-tree-tags-subsetp (ttree tags)

; Note: Tag-tree primitive

  `(alist-keys-subsetp ,ttree ,tags))

