(in-package "ACL2")

(set-ignore-ok t)

(set-irrelevant-formals-ok t)

(set-state-ok t)

(program)

; And now we do generalization...

(defun collectable-fnp2 (fn ens wrld)

; A common collectable term is a non-quoted term that is an
; application of a collectable-fnp2.  Most functions are common
; collectable.  The ones that are not are cons, open lambdas, and the
; (enabled) destructors of wrld.

  t)

(mutual-recursion

(defun smallest-common-subterms12 (term1 term2 ens wrld ans)

; This is the workhorse of smallest-common-subterms, but the arguments are
; arranged so that we know that term1 is the smaller.  We add to ans
; every subterm x of term1 that (a) occurs in term2, (b) is
; collectable, and (c) has no collectable subterms in common with
; term2.

; We return two values.  The first is the modified ans.  The second is
; t or nil according to whether term1 occurs in term2 but neither it
; nor any of its subterms is collectable.  This latter condition is
; said to be the ``potential'' of term1 participating in a collection
; vicariously.  What does that mean?  Suppose a1, ..., an, all have
; potential.  Then none of them are collected (because they aren't
; collectable) but each occurs in term2.  Thus, a term such as (fn a1
; ... an) might actually be collected because it may occur in term2
; (all of its args do, at least), it may be collectable, and none of
; its subterms are.  So those ai have the potential to participate
; vicariously in a collection.

  (cond ((or (variablep term1)
             )

; Since term1 is not collectable, we don't add it to ans.  But we return
; t as our second value if term1 occurs in term2, i.e., term1 has
; potential.

         (mv ans (occur term1 term2)))
	((fquotep term1)
	 (if (occur term1 term2)
	     (mv (add-to-set-equal term1 ans)
		 nil)
	   (mv ans nil)))

        (t
	 (if (occur term1 term2)
	     (mv (add-to-set-equal term1 ans)
		 nil)
	   (mv-let
            (ans all-potentials)
            (smallest-common-subterms12-lst (fargs term1) term2 ens wrld ans)
            (cond ((null all-potentials)

; Ok, some arg did not have potential.  Either it did not occur or it
; was collected.  In either case, term1 should not be collected and
; furthermore, has no potential for participating later.

                   (mv ans nil))
                  ((not (occur term1 term2))

; Every arg of term1 had potential but term1 doesn't occur in
; term2.  That means we don't collect it and it hasn't got
; potential.
                   (mv ans nil))
                  ((collectable-fnp2 (ffn-symb term1) ens wrld)

; So term1 occurs, none of its subterms were collected, and term1
; is collectable.  So we collect it, but it no longer has potential
; (because it got collected).

                   (mv (add-to-set-equal term1 ans)
                       nil))

                  (t

; Term1 occurs, none of its subterms were collected, and term1
; was not collected.  So it has potential to participate vicariously.

                   (mv ans t))))))))

(defun smallest-common-subterms12-lst (terms term2 ens wrld ans)

; We accumulate onto ans every subterm of every element of terms
; that (a) occurs in term2, (b) is collectable, and (c) has no
; collectable subterms in common with term2.  We return the modified
; ans and the flag indicating whether all of the terms have potential.

  (cond
   ((null terms) (mv ans t))
   (t (mv-let
       (ans car-potential)
       (smallest-common-subterms12 (car terms) term2 ens wrld ans)
       (mv-let
        (ans cdr-potential)
        (smallest-common-subterms12-lst (cdr terms) term2 ens wrld ans)
        (mv ans
            (and car-potential
                 cdr-potential)))))))

)

(defun dumb-fn-count-1 (flg x acc)
  (declare (xargs :guard (and (if flg
                                  (pseudo-term-listp x)
                                (pseudo-termp x))
                              (natp acc))))
  (cond (flg (cond ((null x)
                    acc)
                   (t
                    (dumb-fn-count-1 t (cdr x)
                                     (dumb-fn-count-1 nil (car x) acc)))))
        ((or (variablep x) (fquotep x))
         acc)
        (t (dumb-fn-count-1 t (fargs x) (1+ acc)))))

(defun dumb-fn-count (x)

; Originally we had this upside-down call tree, where cons-count was a function
; that counts the number of conses in an object.

; cons-count
;   smallest-common-subterms
;     generalizable-terms-across-relations
;       generalizable-terms
;     generalizable-terms-across-literals1
;       generalizable-terms-across-literals
;         generalizable-terms
;           generalize-clause

; But the role of evgs disappears if we use dumb-occur instead of occur in our
; algorithm for finding common subterms, which seems anyhow like the right
; thing to do if the point is to generalize common subterms to variables.
; Evg-occur is called by occur but not by dumb-occur, and evg-occur is
; potentially expensive on galactic objects.  So we no longer use cons-count to
; compute the smallest-common-subterms; we use fn-count-dumb.

  (dumb-fn-count-1 nil x 0))

(defun smallest-common-subterms2 (term1 term2 ens wrld ans)

; We accumulate onto ans and return the list of every subterm x of
; term1 that is also a subterm of term2, provided x is ``collectable''
; and no subterm of x is collectable.  A term is a collectable if it
; is an application of a collectable-fnp2 and is not an explicit value.
; Our aim is to collect the ``innermost'' or ``smallest'' collectable
; subterms.

  (mv-let (ans potential)
          (cond ((> (dumb-fn-count term1) (dumb-fn-count term2))
                 (smallest-common-subterms12 term2 term1 ens wrld ans))
                (t (smallest-common-subterms12 term1 term2 ens wrld ans)))
          (declare (ignore potential))
          ans))

(defun generalizing-relationp2 (term wrld)

; Term occurs as a literal of a clause.  We want to know whether
; we should generalize common subterms occurring in its arguments.
; Right now the answer is geared to the special case that term is
; a binary relation -- or at least that only two of the arguments
; encourage generalizations.  We return three results.  The first
; is t or nil indicating whether the other two are important.
; The other two are the two terms we should explore for common
; subterms.

; For example, for (equal lhs rhs), (not (equal lhs rhs)), (< lhs
; rhs), and (not (< lhs rhs)), we return t, lhs, and rhs.  We also
; generalize across any known equivalence relation, but this code has
; built into the assumption that all such relations have arity at
; least 2 and just returns the first two args.  For (member x y), we
; return three nils.

  (mv-let (neg-flg atm)
          (strip-not term)
          (declare (ignore neg-flg))
          (cond ((or (variablep atm)
                     (fquotep atm)
                     (flambda-applicationp atm))
                 (mv nil nil nil))
                ((or (eq (ffn-symb atm) 'equal)
                     (eq (ffn-symb atm) '<)
                     (equivalence-relationp (ffn-symb atm) wrld))
                 (mv t (fargn atm 1) (fargn atm 2)))
                (t (mv nil nil nil)))))

(defun generalizable-terms-across-relations2 (cl ens wrld ans)

; We scan clause cl for each literal that is a generalizing-relationp2,
; e.g., (equal lhs rhs), and collect into ans all the smallest common
; subterms that occur in each lhs and rhs.  We return the final ans.

  (cond ((null cl) ans)
        (t (mv-let (genp lhs rhs)
                   (generalizing-relationp2 (car cl) wrld)
                   (generalizable-terms-across-relations2
                    (cdr cl) ens wrld
                    (if genp
                        (smallest-common-subterms2 lhs rhs ens wrld ans)
                        ans))))))

(defun generalizable-terms-across-literals12 (lit1 cl ens wrld ans)
  (cond ((null cl) ans)
        (t (generalizable-terms-across-literals12
            lit1 (cdr cl) ens wrld
            (smallest-common-subterms2 lit1 (car cl) ens wrld ans)))))

(defun generalizable-terms-across-literals2 (cl ens wrld ans)

; We consider each pair of literals, lit1 and lit2, in cl and
; collect into ans the smallest common subterms that occur in
; both lit1 and lit2.  We return the final ans.

  (cond ((null cl) ans)
        (t (generalizable-terms-across-literals2
            (cdr cl) ens wrld
            (generalizable-terms-across-literals12 (car cl) (cdr cl)
                                                       ens wrld ans)))))

(defun generalizable-terms2 (cl ens wrld)

; We return the list of all the subterms of cl that we will generalize.
; We look for common subterms across equalities and inequalities, and
; for common subterms between the literals of cl.

  (generalizable-terms-across-literals2
   cl ens wrld
   (generalizable-terms-across-relations2
    cl ens wrld nil)))

(mutual-recursion
 (defun quote-types (x)
   (if (atom x)
       nil
     (if (and (quotep x)
	      (acl2-numberp (cadr x)))
	 `((not (acl2-numberp ,x)))
       (quote-types-l (cdr x)))))
 (defun quote-types-l (x)
   (if (endp x)
       nil
     (append (quote-types (car x))
	     (quote-types-l (cdr x))))))

(defun generalize-clause2 (cl hist pspv wrld state)

; A standard clause processor of the waterfall.

; We return 4 values.  The first is a signal that is either 'hit, or
; 'miss.  When the signal is 'miss, the other 3 values are irrelevant.
; When the signal is 'hit, the second result is the list of new
; clauses, the third is a ttree that will become that component of the
; history-entry for this generalization, and the fourth is an
; unmodified pspv.  (We return the fourth thing to adhere to the
; convention used by all clause processors in the waterfall (q.v.).)
; The ttree we return is 'assumption-free.

  (declare (ignore state))
  (cond
   ((not (assoc-eq 'being-proved-by-induction
                   (access prove-spec-var pspv :pool)))
    (mv 'miss nil nil nil))
   (t (let* ((ens (access rewrite-constant
                          (access prove-spec-var
                                  pspv
                                  :rewrite-constant)
                          :current-enabled-structure))
             (terms (generalizable-terms2 cl ens wrld)))
        (cond
         ((null terms)
          (mv 'miss nil nil nil))
         (t
	  (let ((cl (append (quote-types-l cl) cl)))
          (mv-let
           (contradictionp type-alist ttree)
           (type-alist-clause cl nil t nil ens wrld
                              nil nil)
           (declare (ignore ttree))
           (cond
            (contradictionp

; We compute the type-alist of the clause to allow us to generate nice
; variable names and to restrict the coming generalization.  We know
; that a contradiction cannot arise, because this clause survived
; simplification.  However, we will return an accurate answer just to
; be rugged.  We'll report that we couldn't do anything!  That's
; really funny.  We just proved our goal and we're saying we can't do
; anything.  But if we made this fn sometimes return the empty set of
; clauses we'd want to fix the io handler for it and we'd have to
; respect the 'assumptions in the ttree and we don't.  Do we?  As
; usual, we ignore the ttree in this case, and hence we ignore it
; totally since it is known to be nil when contradictionp is nil.

             (mv 'miss nil nil nil))
            (t
	     (let ((gen-vars
                    (generate-variable-lst terms
                                           (all-vars1-lst cl
                                                          (owned-vars
                                                           'generalize-clause2
                                                           nil
                                                           hist))
                                           type-alist ens wrld)))
               (mv-let (generalized-cl restricted-vars var-to-runes-alist ttree)
                       (generalize1 cl type-alist terms gen-vars ens wrld)
                       (mv 'hit
                           (list generalized-cl)
                           (add-to-tag-tree
                            'variables gen-vars
                            (add-to-tag-tree
                             'terms terms
                             (add-to-tag-tree
                              'restricted-vars restricted-vars
                              (add-to-tag-tree
                               'var-to-runes-alist var-to-runes-alist
                               (add-to-tag-tree
                                'ts-ttree ttree
                                nil)))))
                           pspv)))))))))))))


;(defun unhidden-lit-info (hist clause pos wrld)     (mv nil nil nil))

;(defun cross-fertilizep/c (equiv cl direction lhs1 rhs1) t)

