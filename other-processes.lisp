; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
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

; Our top-level function for generating variables attempts to feed
; genvar roots that generate names suggestive of the term being
; replaced by the variable.  We now develop the code for generating
; these roots.  It involves a recursive descent through a term.  At
; the bottom, we see variable symbols, e.g., ABC123, and we wish to
; generate the root '("ABC" . 124).

(defun strip-final-digits1 (lst)
; See strip-final-digits.
  (cond ((null lst) (mv "" 0))
        ((member (car lst) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
         (mv-let (str n)
                 (strip-final-digits1 (cdr lst))
                 (mv str (+ (let ((c (car lst)))
                              (case c
                                    (#\0 0)
                                    (#\1 1)
                                    (#\2 2)
                                    (#\3 3)
                                    (#\4 4)
                                    (#\5 5)
                                    (#\6 6)
                                    (#\7 7)
                                    (#\8 8)
                                    (otherwise 9)))
                            (* 10 n)))))
        (t (mv (coerce (reverse lst) 'string) 0))))

(defun strip-final-digits (str)

; Given a string, such as "ABC123", we strip off the final digits in it,
; and compute the number they represent.  We return two things,
; the string and the number, e.g., "ABC" and 123.

  (strip-final-digits1 (reverse (coerce str 'list))))

; For non-variable, non-quote terms we try first the idea of
; generating a name based on the type of the term.  The following
; constant associates with selected type sets the names of some
; variables that we find pleasing and suggestive of the type.  When we
; generalize a term we look at its type and if it is a subtype of one
; of those listed we prefer to use the variables given.  The first
; variable in each family is additionally used as the root for a
; gensym, should it come to that.  This list can be extended
; arbitrarily without affecting soundness, as long as (a) the car of
; each pair below is a type set and (b) the cdr is a true-list of
; symbols.  Arbitrary overlaps between the types and between the
; symbols are permitted.

;; Historical Comment from Ruben Gamboa:
;; I changed rational to real and complex-rational to complex in
;; the list below, since the new types are supersets of the old types,
;; so it should be harmless.

(defconst *var-families-by-type*
  (list (cons *ts-integer* '(I J K L M N))
        (cons #+:non-standard-analysis
              *ts-real*
              #-:non-standard-analysis
              *ts-rational*
              '(R S I J K L M N))
        (cons #+:non-standard-analysis
              *ts-complex*
              #-:non-standard-analysis
              *ts-complex-rational*
              '(Z R S I J K L M N))
        (cons *ts-cons* '(L LST))
        (cons *ts-boolean* '(P Q R))
        (cons *ts-symbol* '(A B C D E))
        (cons *ts-string* '(S STR))
        (cons *ts-character* '(C CH))))

; The following function is used to find the family of vars, given the
; type set of a term:

(defun assoc-ts-subsetp (ts alist)

; Like assoc except we compare with ts-subsetp.

  (cond ((null alist) nil)
        ((ts-subsetp ts (caar alist)) (car alist))
        (t (assoc-ts-subsetp ts (cdr alist)))))

; And here is how we look for an acceptable variable.

(defun first-non-member-eq (lst1 lst2)

; Return the first member of lst1 that is not a member-eq of lst2.

  (cond ((null lst1) nil)
        ((member-eq (car lst1) lst2)
         (first-non-member-eq (cdr lst1) lst2))
        (t (car lst1))))

; If the above techniques don't lead to a choice we generate a string
; from the term by abbreviating the first symbol in the term.  Here is
; how we abbreviate:

(defun abbreviate-hyphenated-string1 (str i maximum prev-c)

; We return a list of characters that, when coerced to a string,
; abbreviates string str from position i to (but not including) maximum.
; Currently, it returns the first character after each block of "hyphens"
; and the last character.  Thus, "PITON-TEMP-STK" is abbreviated
; "PTSK".

; If prev-char is T it means we output the character we last saw.
; If prev-char is NIL it means the character we last saw was a "hyphen".
; Otherwise, prev-char is the previous character.  "Hyphen" here means
; any one of several commonly used "word separators" in symbols.
; This function can be changed arbitrarily as long as it returns a
; list of characters.

  (cond
   ((< i maximum)
    (let ((c (char str i)))
      (cond
       ((member c '(#\- #\_ #\. #\/ #\+))
        (abbreviate-hyphenated-string1 str (1+ i) maximum nil))
       ((null prev-c)
        (cons c (abbreviate-hyphenated-string1 str (1+ i) maximum t)))
       (t (abbreviate-hyphenated-string1 str (1+ i) maximum c)))))
   ((characterp prev-c) (list prev-c))
   (t nil)))

(defun abbreviate-hyphenated-string (str)

; The function scans a string and collects the first and last character
; and every character immediately after a block of "hyphens" as defined
; above.

  (let ((lst (abbreviate-hyphenated-string1 str 0 (length str) nil)))
    (coerce
     (cond ((or (null lst)
                (member (car lst) *suspiciously-first-numeric-chars*))
            (cons #\V lst))
           (t lst))
     'string)))

; Just as strip-final-digits produces the genvar root for a variable,
; the following function produces the genvar root for a nonvariable term.

(defun generate-variable-root1 (term avoid-lst type-alist ens wrld)

; Term is a nonvariable, non-quote term.  This function returns two
; results, str and n, such that (str . n) is a "root" for genvar.

; In fact, it tries to return a root that when fed to genvar will
; create a variable symbol that is suggestive of term and which does
; not occur in avoid-lst.  But the function is correct as long as it
; returns any root, which could be any string.

  (mv-let
   (ts ttree)
   (type-set term t nil type-alist ens wrld nil nil nil)

; Note: We don't really know that the guards have been checked and we
; don't split on the 'assumptions we have forced.  But our only use of
; type set here is heuristic.  This also explains why we just use the
; global enabled structure and ignore the ttree.

   (declare (ignore ttree))
   (let* ((family (cdr (assoc-ts-subsetp ts *var-families-by-type*)))
          (var (first-non-member-eq family avoid-lst)))

     (cond (var

; If the type set of term is one of those for which we have a var family
; and some member of that family does not occur in avoid-lst, then we will
; use the symbol-name of var as the root from which to generate a
; variable symbol for term.  This will almost certainly result in the
; generation of the symbol var by genvar.  The only condition under which
; this won't happen is if var is an illegal variable symbol, in which case
; genvar will suffix it with some sufficiently large natural.

            (mv (symbol-name var) nil))
           (family

; If we have a family for this type of term but all the members are
; to be avoided, we'll genvar from the first member of the family and
; we might as well start suffixing immediately (from 0) because we
; know the unsuffixed var is in avoid-lst.

            (mv (symbol-name (car family)) 0))

           (t

; Otherwise, we will genvar from an abbreviated version of the "first
; symbol" in term.

            (mv (abbreviate-hyphenated-string
                 (symbol-name
                  (cond ((variablep term)            'z) ; never happens
                        ((fquotep term)              'z) ; never happens
                        ((flambda-applicationp term) 'z)
                        (t (ffn-symb term)))))
                nil))))))

; And here we put them together with one last convention.  The
; root for (CAR ...) is just the root for ..., except we force
; there to be a suffix.  Thus, the root for (CAR X4) is going to be
; ("X" . 5).

(defun generate-variable-root (term avoid-lst type-alist ens wrld)
  (cond
   ((variablep term)
    (mv-let (str n)
            (strip-final-digits (symbol-name term))
            (mv str (1+ n))))
   ((fquotep term) (mv "CONST" 0))
   ((eq (ffn-symb term) 'car)
    (mv-let (str n)
            (generate-variable-root (fargn term 1) avoid-lst type-alist ens
                                    wrld)
            (mv str (or n 0))))
   ((eq (ffn-symb term) 'cdr)
    (mv-let (str n)
            (generate-variable-root (fargn term 1) avoid-lst type-alist ens
                                    wrld)
            (mv str (or n 0))))
   (t (generate-variable-root1 term avoid-lst type-alist ens wrld))))

(defun generate-variable (term avoid-lst type-alist ens wrld)

; We generate a legal variable symbol that does not occur in avoid-lst.  We use
; term, type-alist, ens, and wrld in a heuristic way to suggest a preferred
; name for the symbol.  Generally speaking, the symbol we generate will be used
; to replace term in some conjecture, so we try to generate a symbol that we
; think "suggests" term.

  (mv-let (str n)
          (generate-variable-root term avoid-lst type-alist ens wrld)
          (genvar (find-pkg-witness term) str n avoid-lst)))

(defun generate-variable-lst (term-lst avoid-lst type-alist ens wrld)

; And here we generate a list of variable names sequentially, one for
; each term in term-lst.

; See also generate-variable-lst-simple, which only requires the first two of
; the formals above.

  (cond ((null term-lst) nil)
        (t
         (let ((var (generate-variable (car term-lst) avoid-lst
                                       type-alist ens wrld)))
           (cons var (generate-variable-lst (cdr term-lst)
                                            (cons var avoid-lst)
                                            type-alist ens wrld))))))

; That completes the code for generating new variable names.

; An elim-rule, as declared below, denotes a theorem of the form
; (implies hyps (equal lhs rhs)), where rhs is a variable symbol and
; lhs involves the terms destructor-terms, each of which is of the
; form (dfn v1 ... vn), where the vi are distinct variables and {v1
; ... vn} are all the variables in the formula.  We call rhs the
; "crucial variable".  It is the one we will "puff up" to eliminate
; the destructor terms.  For example, in (CONSP X) -> (CONS (CAR X)
; (CDR X)) = X, X is the crucial variable and puffing it up to (CONS A
; B) we can eliminate (CAR X) and (CDR X).  We store an elim-rule
; under the function symbol, dfn, of each destructor term.  The rule
; we store for (dfn v1 ... vn) has that term as the car of destructor-
; terms and has crucial-position j where (nth j '(v1 ... vn)) = rhs.
; (Thus, the crucial-position is the position in the args at which the
; crucial variable occurs and for these purposes we enumerate the args
; from 0 (as by nth) rather than from 1 (as by fargn).)

; The following is now defined in rewrite.lisp.

; (defrec elim-rule
;   (((nume . crucial-position) . (destructor-term . destructor-terms))
;    (hyps . equiv)
;    (lhs . rhs)
;    . rune) nil)

(defun occurs-nowhere-else (var args c i)

; Index the elements of args starting at i.  Scan all args except the
; one with index c and return nil if var occurs in one of them and t
; otherwise.

  (cond ((null args) t)
        ((int= c i)
         (occurs-nowhere-else var (cdr args) c (1+ i)))
        ((dumb-occur var (car args)) nil)
        (t (occurs-nowhere-else var (cdr args) c (1+ i)))))

(defun first-nomination (term votes nominations)

; See nominate-destructor-candidate for an explanation.

  (cons (cons term (cons term votes))
        nominations))

(defun second-nomination (term votes nominations)

; See nominate-destructor-candidate for an explanation.

  (cond ((null nominations) nil)
        ((equal term (car (car nominations)))
         (cons (cons term
                     (union-equal votes (cdr (car nominations))))
               (cdr nominations)))
        (t (cons (car nominations)
                 (second-nomination term votes (cdr nominations))))))


(defun some-hyp-probably-nilp (hyps type-alist ens wrld)

; The name of this function is meant to limit its use to heuristics.
; In fact, if this function says some hyp is probably nil then in fact
; some hyp is known to be nil under the given type-alist, wrld and
; some forced 'assumptions.

; Since the function actually ignores 'assumptions generated, its use
; must be limited to heuristic situations.  When it says "yes, some
; hyp is probably nil" we choose not to pursue the establishment of
; those hyps.

  (cond
   ((null hyps) nil)
   (t (mv-let
       (knownp nilp ttree)
       (known-whether-nil
        (car hyps) type-alist ens (ok-to-force-ens ens)
        nil ; dwp
        wrld nil)
       (declare (ignore ttree))
       (cond ((and knownp nilp) t)
             (t (some-hyp-probably-nilp (cdr hyps) type-alist ens wrld)))))))

(mutual-recursion

(defun sublis-expr (alist term)

; Alist is of the form ((a1 . b1) ... (ak . bk)) where the ai and bi are
; all terms.  We substitute bi for each occurrence of ai in term.
; Thus, if the ai are distinct variables, this function is equivalent to
; sublis-var.  We do not look for ai's properly inside of quoted objects.
; Thus,
;    (sublis-expr '(('3 . x)) '(f '3))       = '(f x)
; but
;    (sublis-expr '(('3 . x)) '(f '(3 . 4))) = '(f '(3 . 4)).

  (let ((temp (assoc-equal term alist)))
    (cond (temp (cdr temp))
          ((variablep term) term)
          ((fquotep term) term)
          (t (cons-term (ffn-symb term)
                        (sublis-expr-lst alist (fargs term)))))))

(defun sublis-expr-lst (alist lst)
  (cond ((null lst) nil)
        (t (cons (sublis-expr alist (car lst))
                 (sublis-expr-lst alist (cdr lst))))))

)

(defun nominate-destructor-candidate
  (term eliminables type-alist clause ens wrld votes nominations)

; This function recognizes candidates for destructor elimination.  It
; is assumed that term is a non-variable, non-quotep term.  To be a
; candidate the term must not be a lambda application and the function
; symbol of the term must have an enabled destructor elimination rule.
; Furthermore, the crucial argument position of the term must be
; occupied by a variable symbol that is a member of the eliminables,
; that occurs only in equiv-hittable positions within the clause,
; and that occurs nowhere else in the arguments of the term, or else
; the crucial argument position must be occupied by a term that itself
; is recursively a candidate.  (Note that if the crucial argument is
; an eliminable term then when we eliminate it we will introduce a
; suitable distinct var into the crucial argument of this term and
; hence it will be eliminable.)  Finally, the instantiated hypotheses
; of the destructor elimination rule must not be known nil under the
; type-alist.

; Votes and nominations are accumulators.  Votes is a list of terms
; that contain term and will be candidates if term is eliminated.
; Nominations are explained below.

; If term is a candidate we either "nominate" it, by adding a
; "nomination" for term to the running accumulator nominations, or
; else we "second" a prior nomination for it.  A nomination of a term
; is a list of the form (dterm . votes) where dterm is the innermost
; eliminable candidate in term and votes is a list of all the terms
; that will be eliminable if dterm is eliminated.  To "second" a
; nomination is simply to add yourself as a vote.

; For example, if X is eliminable then (CAR (CAR (CAR X))) is a
; candidate.  If nominations is initially nil then at the conclusion
; of this function it will be

; (((CAR X) (CAR X) (CAR (CAR X)) (CAR (CAR (CAR X))))).

; We always return a nominations list.

  (cond
   ((flambda-applicationp term) nominations)
   (t (let ((rule (getpropc (ffn-symb term) 'eliminate-destructors-rule nil
                            wrld)))
        (cond
         ((or (null rule)
              (not (enabled-numep (access elim-rule rule :nume) ens)))
          nominations)
         (t (let ((crucial-arg (nth (access elim-rule rule :crucial-position)
                                    (fargs term))))
              (cond
               ((variablep crucial-arg)

; Next we wish to determine that every occurrence of the crucial
; argument -- outside of the destructor nests themselves -- is equiv
; hittable.  For example, for car-cdr-elim, where we have A as the
; crucial arg (meaning term, above, is (CAR A) or (CDR A)), we wish to
; determine that every A in the clause is equal-hittable, except those
; A's occurring inside the (CAR A) and (CDR A) destructors.  Suppose
; the clause is p(A,(CAR A),(CDR A)).  The logical explanation of what
; elim does is to replace the A's not in the destructor nests by (CONS
; (CAR A) (CDR A)) and then generalize (CAR A) to HD and (CDR A) to
; TL.  This will produce p((CONS HD TL), HD, TL).  Observe that we do
; not actually hit the A's inside the CAR and CDR.  So we do not
; require that they be equiv-hittable.  (This situation actually
; arises in the elim rule for sets, where equiv tests equality on the
; canonicalizations.  In this setting, equiv is not a congruence for
; the destructors.)  So the question then is how do we detect that all
; the ``naked'' A's are equiv-hittable?  We ``ought'' to generalize
; away the instantiated destructor terms and then ask whether all the
; A's are equiv-hittable.  But we do not want to pay the price of
; generating n distinct new variable symbols.  So we just replace
; every destructor term by NIL.  This creates a ``pseudo-clause;'' the
; ``terms'' in it are not really legal -- NIL is not a variable
; symbol.  We only use this pseudo-clause to answer the question of
; whether the crucial variable, which certainly isn't NIL, is
; equiv-hittable in every occurrence.

                (let* ((alist (pairlis$
                               (fargs
                                (access elim-rule rule :destructor-term))
                               (fargs term)))
                       (inst-destructors
                        (sublis-var-lst
                         alist
                         (cons (access elim-rule rule :destructor-term)
                               (access elim-rule rule :destructor-terms))))
                       (pseudo-clause (sublis-expr-lst
                                       (pairlis$ inst-destructors nil)
                                       clause)))
                  (cond
                   ((not (every-occurrence-equiv-hittablep-in-clausep
                          (access elim-rule rule :equiv)
                          crucial-arg
                          pseudo-clause ens wrld))
                    nominations)
                   ((assoc-equal term nominations)
                    (second-nomination term votes nominations))
                   ((member crucial-arg eliminables)
                    (cond
                     ((occurs-nowhere-else crucial-arg
                                           (fargs term)
                                           (access elim-rule rule
                                                   :crucial-position)
                                           0)
                      (let* ((inst-hyps
                              (sublis-var-lst alist
                                              (access elim-rule rule :hyps))))
                        (cond
                         ((some-hyp-probably-nilp inst-hyps
                                                  type-alist ens wrld)
                          nominations)
                         (t (first-nomination term votes nominations)))))
                     (t nominations)))
                   (t nominations))))
               (t (nominate-destructor-candidate crucial-arg
                                                 eliminables
                                                 type-alist
                                                 clause
                                                 ens
                                                 wrld
                                                 (cons term votes)
                                                 nominations))))))))))

(mutual-recursion

(defun nominate-destructor-candidates
  (term eliminables type-alist clause ens wrld nominations)

; We explore term and accumulate onto nominations all the nominations.

  (cond ((variablep term) nominations)
        ((fquotep term) nominations)
        (t (nominate-destructor-candidates-lst
            (fargs term)
            eliminables
            type-alist
            clause
            ens
            wrld
            (nominate-destructor-candidate term
                                           eliminables
                                           type-alist
                                           clause
                                           ens
                                           wrld
                                           nil
                                           nominations)))))

(defun nominate-destructor-candidates-lst
  (terms eliminables type-alist clause ens wrld nominations)
  (cond ((null terms) nominations)
        (t (nominate-destructor-candidates-lst
            (cdr terms)
            eliminables
            type-alist
            clause
            ens
            wrld
            (nominate-destructor-candidates (car terms)
                                             eliminables
                                             type-alist
                                             clause
                                             ens
                                             wrld
                                             nominations)))))

)

; We next turn to the problem of choosing which candidate we will eliminate.
; We want to eliminate the most complicated one.  We measure them with
; max-level-no, which is also used by the defuns principle to store the
; level-no of each fn.  Max-level-no was originally defined here, but it is
; mutually recursive with get-level-no, a function we call earlier in the ACL2
; sources, in sort-approved1-rating1.

(defun sum-level-nos (lst wrld)

; Lst is a list of non-variable, non-quotep terms.  We sum the
; level-no of the function symbols of the terms.  For the level no of
; a lambda expression we use the max level no of its body, just as
; would be done if a non-recursive function with the same body were
; being applied.

  (cond ((null lst) 0)
        (t (+ (if (flambda-applicationp (car lst))
                  (max-level-no (lambda-body (ffn-symb (car lst))) wrld)
                  (or (getpropc (ffn-symb (car lst)) 'level-no
                                nil wrld)
                      0))
              (sum-level-nos (cdr lst) wrld)))))

(defun pick-highest-sum-level-nos (nominations wrld dterm max-score)

; Nominations is a list of pairs of the form (dterm . votes), where
; votes is a list of terms.  The "score" of a dterm is the
; sum-level-nos of its votes.  We scan nominations and return a dterm
; with maximal score, assuming that dterm and max-score are the
; winning dterm and its score seen so far.

  (cond
   ((null nominations) dterm)
   (t (let ((score (sum-level-nos (cdr (car nominations)) wrld)))
        (cond
         ((> score max-score)
          (pick-highest-sum-level-nos (cdr nominations) wrld
                                      (caar nominations) score))
         (t
          (pick-highest-sum-level-nos (cdr nominations) wrld
                                      dterm max-score)))))))

(defun select-instantiated-elim-rule (clause type-alist eliminables ens wrld)

; Clause is a clause to which we wish to apply destructor elimination.
; Type-alist is the type-alist obtained by assuming all literals of cl nil.
; Eliminables is the list of legal "crucial variables" which can be
; "puffed up" to do an elim.  For example, to eliminate (CAR X), X
; must be puffed up to (CONS A B).  X is the crucial variable in (CAR
; X).  Upon entry to the destructor elimination process we consider
; all the variables eliminable (except the ones historically
; introduced by elim).  But once we get going within the elim process,
; the only eliminable variables are the ones we introduce ourselves
; (because they won't be eliminable by subsequent processes since they
; were introduced by elim).

; If there is at least one nomination for an elim, we choose the one
; with maximal score and return an instantiated version of the
; elim-rule corresponding to it.  Otherwise we return nil.

  (let ((nominations
         (nominate-destructor-candidates-lst clause
                                             eliminables
                                             type-alist
                                             clause
                                             ens
                                             wrld
                                             nil)))
    (cond
     ((null nominations) nil)
     (t
      (let* ((dterm (pick-highest-sum-level-nos nominations wrld nil -1))
             (rule (getpropc (ffn-symb dterm) 'eliminate-destructors-rule
                             nil wrld))
             (alist (pairlis$ (fargs (access elim-rule rule :destructor-term))
                              (fargs dterm))))
        (change elim-rule rule
                :hyps (sublis-var-lst alist (access elim-rule rule :hyps))
                :lhs  (sublis-var alist (access elim-rule rule :lhs))
                :rhs  (sublis-var alist (access elim-rule rule :rhs))
                :destructor-term
                (sublis-var alist (access elim-rule rule :destructor-term))
                :destructor-terms
                (sublis-var-lst
                 alist
                 (access elim-rule rule :destructor-terms))))))))

; We now take a break from elim and develop the code for the generalization
; that elim uses.  We want to be able to replace terms by variables
; (sublis-expr, above), we want to be able to restrict the new variables by
; noting type-sets of the terms replaced, and we want to be able to use
; generalization rules provided in the database.

(defun type-restriction-segment (cl terms vars type-alist ens wrld)

; Warning: This function calls clausify using the sr-limit from the world, not
; from the rewrite-constant.  Do not call this function from the simplifier
; without thinking about passing in the sr-limit.

; Cl is a clause.  Terms is a list of terms and is in 1:1
; correspondence with vars, which is a list of vars.  Type-alist is
; the result of assuming false every literal of cl.  This function
; returns three results.  The first is a list of literals that can be
; disjoined to cl without altering the validity of cl.  The second is
; a subset of vars.  The third is an extension of ttree.  Technically
; speaking, this function may return any list of terms with the
; property that every term in it is false (under the assumptions in
; type-alist) and any subset of vars, provided the ttree returned is
; an extension of ttree and justifies the falsity of the terms
; returned.  The final ttree must be 'assumption-free and is if the
; initial ttree is also.

; As for motivation, we are about to generalize cl by replacing each
; term in terms by the corresponding var in vars.  It is sound, of
; course, to restrict the new variable to have whatever properties the
; corresponding term has.  This function is responsible for selecting
; the restrictions we want to place on each variable, based on
; type-set reasoning alone.  Thus, if t is known to have properties h1
; & ... & hk, then we can include (not h1), ..., (not hk) in our first
; answer to restrict the variable introduced for t.  We will include
; the corresponding var in our second answer to indicate that we have
; a type restriction on that variable.

; We do not want our type restrictions to cause the new clause to
; explode into cases.  Therefore, we adopt the following heuristic.
; We convert the type set of each term t into a term (hyp t) known to
; be true of t.  We negate (hyp t) and clausify the result.  If that
; produces a single clause (segment) then that segment is added to our
; answer.  Otherwise, we add no restriction.  There are probably
; better ways to do this than to call the full-blown
; convert-type-set-to-term and clausify.  But this is simple, elegant,
; and lets us take advantage of improvements to those two utilities.

  (cond
   ((null terms) (mv nil nil nil))
   (t
    (mv-let
     (ts ttree1)
     (type-set (car terms) nil nil type-alist ens wrld nil nil nil)
     (mv-let
      (term ttree1)
      (convert-type-set-to-term (car terms) ts ens wrld ttree1)
      (let ((clauses (clausify (dumb-negate-lit term) nil t

; Notice that we obtain the sr-limit from the world; see Warning above.

                               (sr-limit wrld))))
        (mv-let
         (lits restricted-vars ttree)
         (type-restriction-segment cl
                                   (cdr terms)
                                   (cdr vars)
                                   type-alist ens wrld)
         (cond ((null clauses)

; If the negation of the type restriction term clausifies to the empty set
; of clauses, then the term is nil.  Since we get to assume it, we're done.
; But this can only happen if the type-set of the term is empty.  We don't think
; this will happen, but we test for it nonetheless, and toss a nil hypothesis
; into our answer literals if it happens.

                (mv (add-to-set-equal *nil* lits)
                    (cons (car vars) restricted-vars)
                    (cons-tag-trees ttree1 ttree)))
               ((and (null (cdr clauses))
                     (not (null (car clauses))))

; If there is only one clause and it is not the empty clause, we'll
; assume everything in it.  (If the clausify above produced '(NIL)
; then the type restriction was just *t* and we ignore it.)  It is
; possible that the literals we are about to assume are already in cl.
; If so, we are not fooled into thinking we've restricted the new var.

                (cond
                 ((subsetp-equal (car clauses) cl)
                  (mv lits restricted-vars ttree))
                 (t (mv (disjoin-clauses (car clauses) lits)
                        (cons (car vars) restricted-vars)
                        (cons-tag-trees ttree1 ttree)))))
               (t

; There may be useful type information we could extract, but we don't.
; It is always sound to exit here, giving ourselves no additional
; assumptions.

                (mv lits restricted-vars ttree))))))))))

(mutual-recursion

(defun subterm-one-way-unify (pat term)

; This function searches pat for a non-variable non-quote subterm s such that
; (one-way-unify s term) returns t and a unify-subst.  If it finds one, it
; returns t and the unify-subst.  Otherwise, it returns two nils.

  (cond ((variablep pat) (mv nil nil))
        ((fquotep pat) (mv nil nil))
        (t (mv-let (ans alist)
                   (one-way-unify pat term)
                   (cond (ans (mv ans alist))
                         (t (subterm-one-way-unify-lst (fargs pat) term)))))))

(defun subterm-one-way-unify-lst (pat-lst term)
  (cond
   ((null pat-lst) (mv nil nil))
   (t (mv-let (ans alist)
              (subterm-one-way-unify (car pat-lst) term)
              (cond (ans (mv ans alist))
                    (t (subterm-one-way-unify-lst (cdr pat-lst) term)))))))

)

; The following is now defined in rewrite.lisp.

; (defrec generalize-rule (nume formula . rune) nil)

(defun apply-generalize-rule (gen-rule term ens)

; Gen-rule is a generalization rule, and hence has a name and a
; formula component.  Term is a term which we are intending to
; generalize by replacing it with a new variable.  We return two
; results.  The first is either t or nil indicating whether gen-rule
; provides a useful restriction on the generalization of term.  If the
; first result is nil, so is the second.  Otherwise, the second result
; is an instantiation of the formula of gen-rule in which term appears.

; Our heuristic for deciding whether to use gen-rule is: (a) the rule
; must be enabled, (b) term must unify with a non-variable subterm of
; the formula of the rule, (c) the unifying substitution must leave no
; free vars in that formula, and (d) the function symbol of term must
; not occur in the instantiation of the formula except in the
; occurrences of term itself.

  (cond
   ((not (enabled-numep (access generalize-rule gen-rule :nume) ens))
    (mv nil nil))
   (t (mv-let
       (ans unify-subst)
       (subterm-one-way-unify (access generalize-rule gen-rule :formula)
                              term)
       (cond
        ((null ans)
         (mv nil nil))
        ((free-varsp (access generalize-rule gen-rule :formula)
                     unify-subst)
         (mv nil nil))
        (t (let ((inst-formula (sublis-var unify-subst
                                           (access generalize-rule
                                                   gen-rule
                                                   :formula))))
             (cond ((ffnnamep (ffn-symb term)
                              (subst-expr 'x term inst-formula))
                    (mv nil nil))
                   (t (mv t inst-formula))))))))))

(defun generalize-rule-segment1 (generalize-rules term ens)

; Given a list of :GENERALIZE rules and a term we return two results:
; the list of instantiated negated formulas of those applicable rules
; and the runes of all applicable rules.  The former list is suitable
; for splicing into a clause to add the formulas as hypotheses.

  (cond
   ((null generalize-rules) (mv nil nil))
   (t (mv-let (ans formula)
              (apply-generalize-rule (car generalize-rules) term ens)
              (mv-let (formulas runes)
                      (generalize-rule-segment1 (cdr generalize-rules)
                                                term ens)
                      (cond (ans (mv (add-literal (dumb-negate-lit formula)
                                                  formulas nil)
                                     (cons (access generalize-rule
                                                   (car generalize-rules)
                                                   :rune)
                                           runes)))
                            (t (mv formulas runes))))))))

(defun generalize-rule-segment (terms vars ens wrld)

; Given a list of terms and a list of vars in 1:1 correspondence, we
; return two results.  The first is a clause segment containing the
; instantiated negated formulas derived from every applicable
; :GENERALIZE rule for each term in terms.  This segment can be spliced
; into a clause to restrict the range of a generalization of terms.
; The second answer is an alist pairing some of the vars in vars to
; the runes of all :GENERALIZE rules in wrld that are applicable to the
; corresponding term in terms.  The second answer is of interest only
; to output routines.

  (cond
   ((null terms) (mv nil nil))
   (t (mv-let (segment1 runes1)
              (generalize-rule-segment1 (global-val 'generalize-rules wrld)
                                        (car terms) ens)
              (mv-let (segment2 alist)
                      (generalize-rule-segment (cdr terms) (cdr vars) ens wrld)
                      (cond
                       ((null runes1) (mv segment2 alist))
                       (t (mv (disjoin-clauses segment1 segment2)
                              (cons (cons (car vars) runes1) alist)))))))))

(defun generalize1 (cl type-alist terms vars ens wrld)

; Cl is a clause.  Type-alist is a type-alist obtained by assuming all
; literals of cl false.  Terms and vars are lists of terms and
; variables, respectively, in 1:1 correspondence.  We assume no var in
; vars occurs in cl.  We generalize cl by substituting vars for the
; corresponding terms.  We restrict the variables by using type-set
; information about the terms and by using :GENERALIZE rules in wrld.

; We return four results.  The first is the new clause.  The second
; is a list of the variables for which we added type restrictions.
; The third is an alist pairing some variables with the runes of
; generalization rules used to restrict them.  The fourth is a ttree
; justifying our work; it is 'assumption-free.

  (mv-let (tr-seg restricted-vars ttree)
          (type-restriction-segment cl terms vars type-alist ens wrld)
          (mv-let (gr-seg alist)
                  (generalize-rule-segment terms vars ens wrld)
                  (mv (sublis-expr-lst (pairlis$ terms vars)
                                       (disjoin-clauses tr-seg
                                                        (disjoin-clauses gr-seg
                                                                         cl)))
                      restricted-vars
                      alist
                      ttree))))


; This completes our brief flirtation with generalization.  We now
; have enough machinery to finish coding destructor elimination.
; However, it might be noted that generalize1 is the main subroutine
; of the generalize-clause waterfall processor.

(defun apply-instantiated-elim-rule (rule cl type-alist avoid-vars ens wrld)

; This function takes an instantiated elim-rule, rule, and applies it to a
; clause cl.  Avoid-vars is a list of variable names to avoid when we generate
; new ones.  See eliminate-destructors-clause for an explanation of that.

; An instantiated :ELIM rule has hyps, lhs, rhs, and destructor-terms, all
; instantiated so that the car of the destructor terms occurs somewhere in the
; clause.  To apply such an instantiated :ELIM rule to a clause we assume the
; hyps (adding their negations to cl), we generalize away the destructor terms
; occurring in the clause and in the lhs of the rule, and then we substitute
; that generalized lhs for the rhs into the generalized cl to obtain the final
; clause.  The generalization step above may involve adding additional
; hypotheses to the clause and using generalization rules in wrld.

; We return three things.  The first is the clause described above, which
; implies cl when the hyps of the rule are known to be true, the second is the
; set of elim variables we have just introduced into it, and the third is a
; list describing this application of the rune of the rule, as explained below.

; The list returned as the third value will become an element in the
; 'elim-sequence list in the ttree of the history entry for this elimination
; process.  The "elim-sequence element" we return has the form:

; (rune rhs lhs alist restricted-vars var-to-runes-alist ttree)

; and means "use rune to replace rhs by lhs, generalizing as specified by alist
; (which maps destructors to variables), restricting the restricted-vars
; variables by type (as justified by ttree) and restricting the
; var-to-runes-alist variables by the named generalize rules."  The ttree is
; 'assumption-free.

  (let* ((rune (access elim-rule rule :rune))
         (hyps (access elim-rule rule :hyps))
         (lhs (access elim-rule rule :lhs))
         (rhs (access elim-rule rule :rhs))
         (dests (access elim-rule rule :destructor-terms))
         (negated-hyps (dumb-negate-lit-lst hyps)))
    (mv-let
     (contradictionp type-alist0 ttree0)
     (type-alist-clause negated-hyps nil nil type-alist ens wrld
                        nil nil)

; Before Version_2.9.3, we just punted when contradictionp is true here, and
; this led to infinite loops reported by Sol Swords and then (shortly
; thereafter) Doug Harper, who both sent examples.  Our initial fix was to punt
; without going into the infinite loop, but then we implemented the current
; scheme in which we simply perform the elimination without generating clauses
; for the impossible "pathological" cases corresponding to falsity of each of
; the instantiated :elim rule's hypotheses.  Both fixes avoid the infinite loop
; in both examples.  We kept the present fix because at the time it actually
; proved the latter example (shown here) without induction:

; (include-book "ihs/@logops" :dir :system)
; (thm (implies (integerp (* 1/2 n)) (equal (mod n 2) 0)))

; However, the fix was buggy.  When we fixed those bugs after Version_3.6.1,
; the thm above no longer proved; but we still avoided the infinite loop.  That
; loop is easily seen in the following example sent by Eric Smith, which proved
; from Versions 2.9.3 through 3.6.1 by exploiting that bug and looped in
; Versions before 2.9.3:

; (defthmd true-listp-of-cdr
;   (implies (true-listp (cdr x))
;            (true-listp x))
;   :hints (("Goal" :in-theory (disable true-listp))))

     (let* ((type-alist (if contradictionp type-alist type-alist0))
            (cl-with-hyps (disjoin-clauses negated-hyps cl))
            (elim-vars (generate-variable-lst dests
                                              (all-vars1-lst cl-with-hyps
                                                             avoid-vars)
                                              type-alist ens wrld))
            (alist (pairlis$ dests elim-vars))
            (generalized-lhs (sublis-expr alist lhs)))
       (cond
        (contradictionp

; The negation of the clause implies that the type-alist holds, and thus one of
; the negated-hyps holds.  Then since contradictionp is true, the conjunction
; of the hyps implies the clause.  That is, *true-clause* implies cl when the
; hyps of the rule are known to be true.

         (mv *true-clause*
             nil ; actual-elim-vars
             (list rune rhs
                   generalized-lhs
                   alist
                   nil ; restricted-vars
                   nil ; var-to-runes-alist
                   ttree0)))
        (t
         (let* ((cl-with-hyps (disjoin-clauses negated-hyps cl))
                (elim-vars (generate-variable-lst dests
                                                  (all-vars1-lst cl-with-hyps
                                                                 avoid-vars)
                                                  type-alist ens wrld)))
           (mv-let (generalized-cl-with-hyps
                    restricted-vars
                    var-to-runes-alist
                    ttree)
                   (generalize1 cl-with-hyps type-alist dests elim-vars ens wrld)
                   (let* ((final-cl
                           (subst-var-lst generalized-lhs
                                          rhs
                                          generalized-cl-with-hyps))
                          (actual-elim-vars
                           (intersection-eq elim-vars
                                            (all-vars1-lst final-cl nil))))
                     (mv final-cl
                         actual-elim-vars
                         (list rune rhs generalized-lhs alist
                               restricted-vars
                               var-to-runes-alist
                               (cons-tag-trees ttree0 ttree))))))))))))

(defun eliminate-destructors-clause1 (cl eliminables avoid-vars ens wrld
                                         top-flg)

; Cl is a clause we are trying to prove.  Eliminables is the set of variables
; on which we will permit a destructor elimination.  Avoid-vars is a list of
; variable names we are to avoid when generating new names.  In addition, we
; avoid the variables in cl.  We look for an eliminable destructor, select the
; highest scoring one and get its instantiated rule, split on the hyps of that
; rule to produce a "pathological" case of cl for each hyp and apply the rule
; to cl to produce the "normal" elim case.  Then we iterate until there is
; nothing more to eliminate.

; The handling of the eliminables needs explanation however.  At the top-level
; (when top-flg is t) eliminables is the set of all variables occurring in cl
; except those historically introduced by destructor elimination.  It is with
; respect to that set that we select our first elimination rule.  Thereafter
; (when top-flg is nil) the set of eliminables is always just the set of
; variables we have introduced into the clauses.  We permit these variables to
; be eliminated by this elim and this elim only.  For example, the top-level
; entry might permit elimination of (CAR X) and of (CAR Y).  Suppose we choose
; X, introducing A and B.  Then on the second iteration, we'll allow
; eliminations of A and B, but not of Y.

; We return three things.  The first is a set of clauses to prove instead of
; cl.  The second is the set of variable names introduced by this destructor
; elimination step.  The third is an "elim-sequence list" that documents this
; step.  If the list is nil, it means we did nothing.  Otherwise it is a list,
; in order, of the "elim-sequence elements" described in
; apply-instantiated-elim-rule above.  This list should become the
; 'elim-sequence entry in the ttree for this elim process.

; Historical Remark on Nqthm.

; This code is spiritually very similar to that of Nqthm.  However, it is much
; more elegant and easy to understand.  Nqthm managed the "iteration" with a
; "todo" list which grew and then shrank.  In addition, while we select the
; best rule on each round from scratch, Nqthm kept an ordered list of
; candidates (which it culled appropriately when eliminations removed some of
; them from the clause or when the crucial variables were no longer among
; eliminables).  Finally, and most obscurely, Nqthm used an inscrutable test on
; the "process history" (related to our elim-sequence) and a subtle invariant
; about the candidates to switch from our top-flg t mode to top-flg nil mode.
; We have spent about a week coding destructor elimination in ACL2 and we have
; thrown away more code that we have kept as we at first transcribed and then
; repeatedly refined the Nqthm code.  We are much happier with the current code
; than Nqthm's and believe it will be much easier to modify in the future.  Oh,
; one last remark: Nqthm's destructor elimination code had almost no comments
; and everything was done in a single big function with lots of ITERATEs.  It
; is no wonder it was so hard to decode.

; Our first step is to get the type-alist of cl.  It is used in two different
; ways: to identify contradictory hypotheses of candidate :ELIM lemmas and to
; generate names for new variables.

  (mv-let
    (contradictionp type-alist ttree)
    (type-alist-clause cl nil

; The force-flg must be nil, or else apply-instantiated-elim-rule may call
; generalize1 with a type-alist whose ttrees are not all assumption-free,
; resulting in the return of such a ttree by generalize1 (contrary to its
; specification).  The following example was admitted in Version_2.4 and
; Version_4.1, and presumably versions inbetween and perhaps older.

; (progn
;   (defun app (x y)
;     (if (consp x)
;         (cons (car x) (app (cdr x) y))
;       y))
;   (defun rev (x)
;     (if (consp x)
;         (app (rev (cdr x)) (cons (car x) nil))
;       x))
;   (defthm rev-type
;     (implies (force (true-listp x))
;              (true-listp (rev x)))
;     :rule-classes :type-prescription)
;   (defthm false
;     (equal (rev (rev x)) x)
;     :rule-classes nil)
;   (defthm true
;     (equal (rev (rev '(a b . c)))
;            '(a b))
;     :rule-classes nil)
;   (defthm bug
;     nil
;     :hints (("Goal" :use (true (:instance false (x '(a b . c))))))
;     :rule-classes nil))

                       nil ; force-flg; see comment above
                       nil ens wrld
                       nil nil)
    (declare (ignore ttree))
    (cond
     (contradictionp

; This is unusual.  We don't really expect to find a contradiction here.  We'll
; return an answer indicating that we didn't do anything.  We ignore the
; possibly non-nil ttree here, which is valid given that we are returning the
; same goal clause rather than actually relying on the contradiction.  We thus
; ignore ttree everywhere because it is nil when contradictionp is nil.

      (mv (list cl) nil nil))
     (t
      (let ((rule (select-instantiated-elim-rule cl type-alist eliminables
                                                 ens wrld)))
        (cond ((null rule) (mv (list cl) nil nil))
              (t (mv-let (new-clause elim-vars1 ele)
                   (apply-instantiated-elim-rule rule cl type-alist
                                                 avoid-vars ens wrld)
                   (let ((clauses1 (split-on-assumptions
                                    (access elim-rule rule :hyps)
                                    cl nil)))

; Clauses1 is a set of clauses obtained by splitting on the instantiated hyps
; of the rule.  It contains n clauses, each obtained by adding one member of
; inst-hyps to cl.  (If any of these new clauses is a tautology, it will be
; deleted, thus there may not be as many clauses as there are inst-hyps.)
; Because these n clauses are all "pathological" wrt the destructor term, e.g.,
; we're assuming (not (consp x)) in a clause involving (car x), we do no
; further elimination down those paths.  Note the special case where
; contradictionp is true, meaning that we have ascertained that the
; pathological cases are all impossible.

                     (cond
                      ((equal new-clause *true-clause*)
                       (mv clauses1 elim-vars1 (list ele)))
                      (t
                       (mv-let (clauses2 elim-vars2 elim-seq)
                         (eliminate-destructors-clause1
                          new-clause
                          (if top-flg
                              elim-vars1
                            (union-eq elim-vars1
                                      (remove1-eq
                                       (access elim-rule rule :rhs)
                                       eliminables)))
                          avoid-vars
                          ens
                          wrld
                          nil)
                         (mv (conjoin-clause-sets clauses1 clauses2)
                             (union-eq elim-vars1 elim-vars2)
                             (cons ele elim-seq))))))))))))))

(defun owned-vars (process mine-flg history)

; This function takes a process name, e.g., 'eliminate-destructors-
; clause, a flag which must be either nil or t, and a clause history.
; If the flag is t, it returns all of the variables introduced into
; the history by the given process.  If the flag is nil, it returns
; all of the variables introduced into the history by any other
; process.  Note: the variables returned may not even occur in the
; clause whose history we scan.

; For example, if the only two processes that introduce variables are
; destructor elimination and generalization, then when given
; 'eliminate-destructors-clause and mine-flg nil this function will
; return all the variables introduced by 'generalize-clause.

; In order to work properly, a process that introduces variables must
; so record it by adding a tagged object to the ttree of the process.
; The tag should be 'variables and the object should be a list of the
; variables introduced at that step.  There should be at most one
; occurrence of that tag in the ttree.

; Why are we interested in this concept?  Destructor elimination is
; controlled by a heuristic meant to prevent indefinite elim loops
; involving simplification.  For example, suppose you eliminate (CDR
; X0) by introducing (CONS A X1) for X0, and then open a recursive
; function so as to produce (CDR X1).  It is easy to cause a loop if
; you then eliminate (CDR X1) by replacing X1 it with (CONS B X2),
; etc.  To prevent this, we do not allow destructor elimination to
; work on a variable that was introduced by destructor elimination
; (except within the activation of the elim process that introduces
; that variable).

; That raises the question of telling how a variable was introduced
; into a clause.  In ACL2 we adopt the convention described above and
; follow the rule that no process shall introduce a variable into a
; clause that has been introduced by a different process in the
; history of that clause.  Thus, if X1 is introduced by elim into the
; history, then X1 cannot also be introduced by generalization, even
; if X1 is new for the clause when generalization occurs.  By
; following this rule we know that if a variable is in a clause and
; that variable was introduced into the history of the clause by elim
; then that variable was introduced into the clause by elim.  If
; generalize could "re-use" a variable that was already "owned" by
; elim in the history, then we could not accurately determine by
; syntactic means the elim variables in the clause.

; Historical Remark on Nqthm:

; Nqthm solved this problem by allocating a fixed set of variable names
; to elim and a disjoint set to generalize.  At the top of the waterfall it
; removed from those two fixed sets the variables that occurred in the
; input clause.  Thereafter, if a variable was found to be in the (locally)
; fixed sets, it was known to be introduced by the given process.  The
; limitation to a fixed set caused the famous set-diff-n error message
; when the set was exhausted:

;    FATAL ERROR:  SET-DIFF-N called with inappropriate arguments.

; In the never-released xnqthm -- the "book version" of Nqthm that was
; in preparation when we began work on ACL2 -- we generated a more
; informative error message and increased the size of the fixed sets
; from 18 to over 600.  But that meant copying a list of length 600 at
; the top of the waterfall.  But the real impetus to the current
; scheme was the irritation over there being a fixed set and the
; attraction of being able to generate mnemonic names from terms.  (It
; remains to be seen whether we like the current algorithms.  E.g., is
; AENI really a good name for (EXPLODE-NONNEGATIVE-INTEGER N 10 A)?
; In any case, now we are free to experiment with name generation.)

  (cond ((null history) nil)
        ((eq mine-flg
             (eq (access history-entry (car history) :processor)
                 process))
         (union-eq (tagged-object 'variables
                                  (access history-entry (car history)
                                          :ttree))
                   (owned-vars process mine-flg (cdr history))))
        (t (owned-vars process mine-flg (cdr history)))))

(defun ens-from-pspv (pspv)
  (access rewrite-constant
          (access prove-spec-var pspv
                  :rewrite-constant)
          :current-enabled-structure))

(defun eliminate-destructors-clause (clause hist pspv wrld state)

; This is the waterfall processor that eliminates destructors.
; Like all waterfall processors it returns four values:  'hit or 'miss,
; and, if 'hit, a set of clauses, a ttree, and a possibly modified pspv.

  (declare (ignore state))
  (mv-let
   (clauses elim-vars elim-seq)
   (eliminate-destructors-clause1 clause
                                  (set-difference-eq
                                   (all-vars1-lst clause nil)
                                   (owned-vars 'eliminate-destructors-clause t
                                               hist))
                                  (owned-vars 'eliminate-destructors-clause nil
                                              hist)
                                  (ens-from-pspv pspv)
                                  wrld
                                  t)
   (cond (elim-seq (mv 'hit clauses
                       (add-to-tag-tree! 'variables elim-vars
                                         (add-to-tag-tree! 'elim-sequence
                                                           elim-seq
                                                           nil))
                       pspv))
         (t (mv 'miss nil nil nil)))))

; We now develop the code to describe the destructor elimination done,
; starting with printing clauses prettily.

(defun prettyify-clause1 (cl wrld)
  (cond ((null (cdr cl)) nil)
        (t (cons (untranslate (dumb-negate-lit (car cl)) t wrld)
                 (prettyify-clause1 (cdr cl) wrld)))))

(defun prettyify-clause2 (cl wrld)
  (cond ((null cl) nil)
        ((null (cdr cl)) (untranslate (car cl) t wrld))
        ((null (cddr cl)) (list 'implies
                                (untranslate (dumb-negate-lit (car cl)) t wrld)
                                (untranslate (cadr cl) t wrld)))
        (t (list 'implies
                 (cons 'and (prettyify-clause1 cl wrld))
                 (untranslate (car (last cl)) t wrld)))))

; Rockwell Addition:  Prettyify-clause now has a new arg to control
; whether we abstract away common subexprs.  This will show up many
; times in a compare-windows.

(defun prettyify-clause (cl let*-abstractionp wrld)

; We return an untranslated term that is equivalent to cl.  For a simpler
; function that returns a translated term, see prettyify-clause-simple.

  (if let*-abstractionp
      (mv-let (vars terms)
              (maximal-multiples (cons 'list cl) let*-abstractionp)
              (cond
               ((null vars)
                (prettyify-clause2 cl wrld))
               (t `(let* ,(listlis vars
                                   (untranslate-lst (all-but-last terms)
                                                    nil wrld))
                     ,(prettyify-clause2 (cdr (car (last terms))) wrld)))))
    (prettyify-clause2 cl wrld)))

(defun prettyify-clause-lst (clauses let*-abstractionp wrld)
  (cond ((null clauses) nil)
        (t (cons (prettyify-clause (car clauses) let*-abstractionp wrld)
                 (prettyify-clause-lst (cdr clauses) let*-abstractionp
                                       wrld)))))

(defun prettyify-clause-set (clauses let*-abstractionp wrld)
  (cond ((null clauses) t)
        ((null (cdr clauses))
         (prettyify-clause (car clauses) let*-abstractionp wrld))
        (t (cons 'and (prettyify-clause-lst clauses let*-abstractionp wrld)))))

(defun tilde-*-elim-phrase/alist1 (alist wrld)
  (cond ((null alist) nil)
        (t (cons (msg "~p0 by ~x1"
                      (untranslate (caar alist) nil wrld)
                      (cdar alist))
                 (tilde-*-elim-phrase/alist1 (cdr alist) wrld)))))

(defun tilde-*-elim-phrase/alist (alist wrld)

; Alist is never nil, except in the unusual case that
; apply-instantiated-elim-rule detected a tautology where we claim
; none could occur.  If that happens we print the phrase "generalizing
; nothing".  This is documented simply because it is strange to put
; anything in the 0 case below.

  (list* "" " and ~@*" ", ~@*" ", ~@*"
         (tilde-*-elim-phrase/alist1 alist wrld)
         nil))

(defun tilde-*-elim-phrase3 (var-to-runes-alist)
  (cond ((null var-to-runes-alist) nil)
        (t (cons (msg "noting the condition imposed on ~x0 by the ~
                       generalization rule~#1~[~/s~] ~&1"
                      (caar var-to-runes-alist)
                      (strip-base-symbols (cdar var-to-runes-alist)))
                 (tilde-*-elim-phrase3 (cdr var-to-runes-alist))))))

(defun tilde-*-elim-phrase2 (alist restricted-vars var-to-runes-alist ttree wrld)
   (list* "" "~@*" "~@* and " "~@*, "
          (append
           (list (msg "~*0"
                      (tilde-*-elim-phrase/alist alist wrld)))
           (cond
            (restricted-vars
             (let ((simp-phrase (tilde-*-simp-phrase ttree)))
               (cond ((null (cdr restricted-vars))
                      (list (msg "restrict the type of the new ~
                                  variable ~&0 to be that of the term ~
                                  it replaces~#1~[~/, as established ~
                                  by ~*2~]"
                                 restricted-vars
                                 (if (nth 4 simp-phrase) 1 0)
                                 simp-phrase)))
                     (t (list (msg "restrict the types of the new ~
                                    variables ~&0 to be those of the ~
                                    terms they replace~#1~[~/, as ~
                                    established by ~*2~]"
                                   restricted-vars
                                   (if (nth 4 simp-phrase) 1 0)
                                   simp-phrase))))))
            (t nil))
           (tilde-*-elim-phrase3 var-to-runes-alist))
          nil))

(defun tilde-*-elim-phrase1 (lst i already-used wrld)
  (cond
   ((null lst) nil)
   (t (cons
       (cons "(~xi) ~#f~[Use~/Finally, use~] ~#a~[~x0~/~x0, again,~] to ~
              replace ~x1 by ~p2~*3.  "
             (list (cons #\i i)
                   (cons #\f (if (and (null (cdr lst))
                                      (> i 2))
                                 1
                                 0))
                   (cons #\a (if (member-equal (nth 0 (car lst)) already-used)
                                 (if (member-equal (nth 0 (car lst))
                                                   (cdr (member-equal
                                                         (nth 0 (car lst))
                                                         already-used)))
                                     0
                                     1)
                                 0))
                   (cons #\0 (base-symbol (nth 0 (car lst))))
                   (cons #\1 (nth 1 (car lst)))
                   (cons #\2 (untranslate (nth 2 (car lst)) nil wrld))
                   (cons #\3 (tilde-*-elim-phrase2 (nth 3 (car lst))
                                                   (nth 4 (car lst))
                                                   (nth 5 (car lst))
                                                   (nth 6 (car lst))
                                                   wrld))))
       (tilde-*-elim-phrase1 (cdr lst)
                             (1+ i)
                             (cons (nth 0 (car lst))
                                   already-used)
                             wrld)))))

(defun tilde-*-elim-phrase (lst wrld)

; Lst is the 'elim-sequence list of the ttree of the elim process,
; i.e., it is the third result of eliminate-destructors-clause1 above,
; the third result of apply-instantiated-elim-rule, i.e., a list of
; elements of the form

; (rune rhs lhs alist restricted-vars var-to-runes-alist ttree).

; We generate an object suitable for giving to the tilde-* fmt directive
; that will cause each element of the list to print out a phrase
; describing that step.

  (list* ""
         "~@*"
         "~@*"
         "~@*"
         (tilde-*-elim-phrase1 lst 1 nil wrld)
         nil))

(defun tilde-*-untranslate-lst-phrase (lst flg wrld)
  (list* "" "~p*" "~p* and " "~p*, "
         (untranslate-lst lst flg wrld)
         nil))

(defun eliminate-destructors-clause-msg1 (signal clauses ttree pspv state)

; The arguments to this function are the standard ones for an output
; function in the waterfall.  See the discussion of the waterfall.

  (declare (ignore signal pspv))
  (let ((lst (tagged-object 'elim-sequence ttree))
        (n (length clauses))
        (wrld (w state)))
    (cond
      ((null (cdr lst))
       (fms "The destructor term~#p~[~/s~] ~*0 can be eliminated by using ~x1 ~
             to replace ~p2 by ~p3~*4.  ~#5~[All the clauses produced are ~
             tautological.~/This produces the following goal.~/This produces ~
             the following ~n6 goals.~]~|"
            (list (cons #\p (nth 3 (car lst)))
                  (cons #\0 (tilde-*-untranslate-lst-phrase
                             (strip-cars (nth 3 (car lst))) nil wrld))
                  (cons #\1 (base-symbol (nth 0 (car lst))))
                  (cons #\2 (nth 1 (car lst)))
                  (cons #\3 (untranslate (nth 2 (car lst)) nil wrld))
                  (cons #\4 (tilde-*-elim-phrase2 (nth 3 (car lst))
                                                  (nth 4 (car lst))
                                                  (nth 5 (car lst))
                                                  (nth 6 (car lst))
                                                  wrld))
                  (cons #\5 (zero-one-or-more n))
                  (cons #\6 n))
            (proofs-co state)
            state
            (term-evisc-tuple nil state)))
      (t
       (fms "The destructor term~#p~[~/s~] ~*0 can be eliminated.  ~
             Furthermore, ~#p~[that term is~/those terms are~] at the root of ~
             a chain of ~n1 rounds of destructor elimination.  ~*2These steps ~
             produce ~#3~[no nontautological goals~/the following goal~/the ~
             following ~n4 goals~].~|"
            (list (cons #\p (nth 3 (car lst)))
                  (cons #\0 (tilde-*-untranslate-lst-phrase
                             (strip-cars (nth 3 (car lst)))
                             nil wrld))
                  (cons #\1 (length lst))
                  (cons #\2 (tilde-*-elim-phrase lst wrld))
                  (cons #\3 (zero-one-or-more n))
                  (cons #\4 n))
            (proofs-co state)
            state
            (term-evisc-tuple nil state))))))

; We now develop the cross-fertilization process.

(mutual-recursion

(defun almost-quotep1 (term)
  (cond ((variablep term) t)
        ((fquotep term) t)
        ((flambda-applicationp term)
         (and (almost-quotep1 (lambda-body term))
              (almost-quotep1-listp (fargs term))))
        ((eq (ffn-symb term) 'cons)
         (and (almost-quotep1 (fargn term 1))
              (almost-quotep1 (fargn term 2))))
        (t nil)))

(defun almost-quotep1-listp (terms)
  (cond ((null terms) t)
        (t (and (almost-quotep1 (car terms))
                (almost-quotep1-listp (cdr terms))))))

)

(defun almost-quotep (term)

; A term is "almost a quotep" if it is a non-variablep term that
; consists only of variables, explicit values, and applications of
; cons.  Lambda-applications are permitted provided they have
; almost-quotep bodies and args.

; Further work:  See equal-x-cons-x-yp.

  (and (nvariablep term)
       (almost-quotep1 term)))

(defun destructor-applied-to-varsp (term ens wrld)

; We determine whether term is of the form (destr v1 ... vn)
; where destr has an enabled 'eliminate-destructors-rule
; and all the vi are variables.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term) nil)
        (t (and (all-variablep (fargs term))
                (let ((rule (getpropc (ffn-symb term)
                                      'eliminate-destructors-rule
                                      nil
                                      wrld)))
                  (and rule
                       (enabled-numep (access elim-rule rule :nume)
                                      ens)))))))

(defun dumb-occur-lst-except (term lst lit)

; Like dumb-occur-lst except that it does not look into the first
; element of lst that is equal to lit.  If you think of lst as a
; clause and lit as a literal, we ask whether term occurs in some
; literal of clause other than lit.  In Nqthm we looked for an eq
; occurrence of lit, which we can't do here.  But if there are two
; occurrences of lit in lst, then normally in Nqthm they would not
; be eq and hence we'd look in one of them.  Thus, here we look in
; all the literals of lst after we've seen lit.  This is probably
; unnecessarily complicated.

  (cond ((null lst) nil)
        ((equal lit (car lst))
         (dumb-occur-lst term (cdr lst)))
        (t (or (dumb-occur term (car lst))
               (dumb-occur-lst-except term (cdr lst) lit)))))

(defun fertilize-feasible (lit cl hist term ens wrld)

; Lit is a literal of the form (not (equiv term val)) (or the commuted
; form).  We determine if it is feasible to substitute val for term in
; clause cl.  By that we mean that term is neither a near constant nor
; a destructor, term does occur elsewhere in the clause, every
; occurrence of term is equiv-hittable, and we haven't already
; fertilized with this literal.

  (and (not (almost-quotep term))
       (not (destructor-applied-to-varsp term ens wrld))
       (dumb-occur-lst-except term cl lit)
       (every-occurrence-equiv-hittablep-in-clausep (ffn-symb (fargn lit 1))
                                                    term cl ens wrld)
       (not (already-used-by-fertilize-clausep lit hist t))))

(mutual-recursion

(defun fertilize-complexity (term wrld)

; The fertilize-complexity of (fn a1 ... an) is the level number of fn
; plus the maximum fertilize complexity of ai.

  (cond ((variablep term) 0)
        ((fquotep term) 0)
        (t (+ (get-level-no (ffn-symb term) wrld)
              (maximize-fertilize-complexity (fargs term) wrld)))))

(defun maximize-fertilize-complexity (terms wrld)
  (cond ((null terms) 0)
        (t (max (fertilize-complexity (car terms) wrld)
                (maximize-fertilize-complexity (cdr terms) wrld)))))

)

(defun first-fertilize-lit (lst cl hist ens wrld)

; We find the first literal lst of the form (not (equiv lhs1 rhs1))
; such that a fertilization of one side for the other into cl is
; feasible.  We return six values.  The first is either nil, meaning
; no such lit was found, or a direction of 'left-for-right or
; 'right-for-left.  The second is the literal found.  The last three are
; the equiv, lhs, and rhs of the literal, and the length of the tail of
; cl after lit.

  (cond
   ((null lst) (mv nil nil nil nil nil nil))
   (t (let ((lit (car lst)))
        (case-match
         lit
         (('not (equiv lhs rhs))
          (cond
           ((equivalence-relationp equiv wrld)
            (cond
             ((fertilize-feasible lit cl hist lhs ens wrld)
              (cond
               ((fertilize-feasible lit cl hist rhs ens wrld)
                (cond ((< (fertilize-complexity lhs wrld)
                          (fertilize-complexity rhs wrld))
                       (mv 'left-for-right lit equiv lhs rhs (len (cdr lst))))
                      (t (mv 'right-for-left lit equiv lhs rhs
                             (len (cdr lst))))))
               (t (mv 'right-for-left lit equiv lhs rhs (len (cdr lst))))))
             ((fertilize-feasible lit cl hist rhs ens wrld)
              (mv 'left-for-right lit equiv lhs rhs (len (cdr lst))))
             (t (first-fertilize-lit (cdr lst) cl hist ens wrld))))
           (t (first-fertilize-lit (cdr lst) cl hist ens wrld))))
         (& (first-fertilize-lit (cdr lst) cl hist ens wrld)))))))

(defun cross-fertilizep/c (equiv cl direction lhs1 rhs1)

; See condition (c) of cross-fertilizep.

  (cond ((null cl) nil)
        ((and (nvariablep (car cl))
              (not (fquotep (car cl)))
              (equal (ffn-symb (car cl)) equiv)
              (if (eq direction 'left-for-right)
                  (dumb-occur rhs1 (fargn (car cl) 2))
                  (dumb-occur lhs1 (fargn (car cl) 1))))
         t)
        (t (cross-fertilizep/c equiv (cdr cl) direction lhs1 rhs1))))

(defun cross-fertilizep/d (equiv cl direction lhs1 rhs1)

; See condition (d) of cross-fertilizep.

  (cond ((null cl) nil)
        ((and (nvariablep (car cl))
              (not (fquotep (car cl)))
              (equal (ffn-symb (car cl)) equiv)
              (if (eq direction 'left-for-right)
                  (dumb-occur rhs1 (fargn (car cl) 1))
                  (dumb-occur lhs1 (fargn (car cl) 2))))
         t)
        (t (cross-fertilizep/d equiv (cdr cl) direction lhs1 rhs1))))

(defun cross-fertilizep (equiv cl pspv direction lhs1 rhs1)

; We have found a literal, (not (equiv lhs1 rhs1)), of cl such that a
; fertilization is feasible in the indicated direction.  We want to
; know whether this will be a cross-fertilization or not.  Suppose,
; without loss of generality, that the direction is 'left-for-right,
; i.e., we are going to substitute lhs1 for rhs1.  A cross-
; fertilization is performed only if (a) neither lhs1 nor rhs1 is an
; explicit value, (b) we are under an induction (thus our interest in
; pspv), (c) there is some equiv literal, (equiv lhs2 rhs2), in the
; clause such that rhs1 occurs in rhs2 (thus we'll hit rhs2) and (d)
; there is some equiv literal such that rhs1 occurs in lhs2 (thus,
; cross fertilization will actually prevent us from hitting something
; massive substitution would hit).  Note that since we know the
; fertilization is feasible, every occurrence of the target is in an
; equiv-hittable slot.  Thus, we can use equivalence-insensitive occur
; checks rather than being prissy.

  (and (not (quotep lhs1))
       (not (quotep rhs1))
       (assoc-eq 'being-proved-by-induction
                 (access prove-spec-var pspv :pool))

; David Hardin sent an example in March 2015, for which Codewalker generates a
; goal that fails to prove under induction but is proved at the top level.  The
; reason turned out to be that cross-fertilization is used under induction but
; not at the top level.  Since the point of cross-fertilization is to prepare
; for generalization, and since generalization often fails, we arrange just
; below to avoid cross-fertilization if generalization is turned off (instead,
; fully fertilizing with the equivalence).  This makes it easy for applications
; (such as Codewalker) to avoid the limited substitution formed by
; cross-fertilization.

       (not (member-eq 'generalize-clause
                       (cdr (assoc-eq :do-not
                                      (access prove-spec-var pspv
                                              :hint-settings)))))
       (cross-fertilizep/c equiv cl direction lhs1 rhs1)
       (cross-fertilizep/d equiv cl direction lhs1 rhs1)))

(defun delete-from-ttree (tag val ttree)
  (let ((objects (tagged-objects tag ttree)))
    (cond (objects (cond
                    ((member-equal val objects)
                     (let ((new-objects (remove1-equal val objects))
                           (new-ttree (remove-tag-from-tag-tree! tag ttree)))
                       (cond (new-objects
                              (extend-tag-tree tag new-objects new-ttree))
                             (t new-ttree))))
                    (t ttree)))
          (t ttree))))

(defun fertilize-clause1 (cl lit1 equiv lhs1 rhs1
                             direction
                             cross-fert-flg
                             delete-lit-flg
                             ens
                             wrld
                             state
                             ttree)

; Cl is a clause we are fertilizing with lit1, which is one of its
; literals and which is of the form (not (equiv lhs1 rhs1)).  Direction is
; 'left-for-right or 'right-for-left, indicating which way we're to
; substitute.  Cross-fert-flg is t if we are to hit only (equiv lhs2
; rhs2) and do it in a cross-fertilize sort of way (left for right
; into right or right for left into left); otherwise we substitute for
; all occurrences.  Delete-lit-flg is t if we are to delete the first
; occurrence of lit when we see it.  We return two things:  the new
; clause and a ttree indicating the congruences used.

  (cond
   ((null cl) (mv nil ttree))
   (t
    (let* ((lit2 (car cl))
           (lit2-is-lit1p (equal lit2 lit1)))

; First, we substitute into lit2 as appropriate.  We obtain new-lit2
; and a ttree.  We ignore the hitp result always returned by
; subst-equiv-expr.

; What do we mean by "as appropriate"?  We consider three cases on
; lit2, the literal into which we are substituting: lit2 is (equiv lhs
; rhs), lit2 is (not (equiv lhs rhs)), or otherwise.  We also consider
; whether we are cross fertilizing or just substituting for all
; occurrences.  Here is a table that explains our actions below.

; lit2  (equiv lhs rhs)   (not (equiv lhs rhs))   other

; xfert       xfert               subst           no action
; subst       subst               subst           subst

; The only surprising part of this table is that in the case of
; cross-fertilizing into (not (equiv lhs rhs)), i.e., into another
; equiv hypothesis, we do a full-fledged substitution rather than a
; cross-fertilization.  I do not give an example of why we do this.
; However, it is exactly what Nqthm does (in the only comparable case,
; namely, when equiv is EQUAL).

      (mv-let
       (hitp new-lit2 ttree)
       (cond
        (lit2-is-lit1p (mv nil lit2 ttree))
        ((or (not cross-fert-flg)
             (case-match lit2
               (('not (equiv-sym & &)) (equal equiv-sym equiv))
               (& nil)))
         (cond ((eq direction 'left-for-right)
                (subst-equiv-expr equiv lhs1 rhs1
                                  *geneqv-iff*
                                  lit2 ens wrld state ttree))
               (t (subst-equiv-expr equiv rhs1 lhs1
                                    *geneqv-iff*
                                    lit2 ens wrld state ttree))))
        (t

; Caution: There was once a bug below.  We are cross fertilizing.
; Suppose we see (equiv lhs2 rhs2) and want to substitute lhs1 for
; rhs1 in rhs2.  What geneqv do we maintain?  The bug, which was
; completely nonsensical, was that we maintained *geneqv-iff*, just as
; above.  But in fact we must maintain whatever geneqv maintains
; *geneqv-iff* in the second arg of equiv.  Geneqv-lst returns a list
; of geneqvs, one for each argument position of equiv.  We select the
; one in the argument position corresponding to the side we are
; changing.  Actually, the two geneqvs for an equivalence relation
; ought to be the identical, but it would be confusing to exploit
; that.

; In the days when this bug was present there was another problem!  We
; only substituted into (equal lhs2 rhs2)!  (That is, the case-match
; below was on ('equal lhs2 rhs2) rather than (equiv-sym lhs2 rhs2).)
; So here is an example of a screwy substitution we might have done:
; Suppose (equiv a b) is a hypothesis and (equal (f a) (f b)) is a
; conclusion and that we are to do a cross-fertilization of a for b.
; We ought not to substitute into equal except maintaining equality.
; But we actually would substitute into (f b) maintaining iff!  Now
; suppose we knew that (equiv x y) -> (iff (f x) (f y)).  Then we
; could derive (equal (f a) (f a)), which would be t and unsound.  The
; preconditions for this screwy situation are exhibited by:

;  (defun squash (x)
;    (cond ((null x) nil)
;          ((integerp x) 1)
;          (t t)))
;
;  (defun equiv (x y)
;    (equal (squash x) (squash y)))
;
;  (defequiv equiv)
;
;  (defun f (x) x)
;
;  (defcong equiv iff (f x) 1)
;

; In particular, (implies (equiv a b) (equal (f a) (f b))) is not a
; theorem (a=1 and b=2 are counterexamples), but this function, if
; called with that input clause, ((not (equiv a b)) (equal (f a) (f
; b))), and the obvious lit1, etc., would return (equal (f a) (f a)),
; which is T.  (Here we are substituting left for right, a for b.)  So
; there was a soundness bug in the old version of this function.

; But it turns out that this bug could never be exploited.  The bug
; can be provoked only if we are doing cross-fertilization.  And
; cross-fertilization is only done if the fertilization is "feasible".
; That means that every occurrence of b in the clause is equiv
; hittable, as per every-occurrence-equiv-hittablep-in-clausep.  In
; our example, the b in (f b) is not equiv hittable.  Indeed, if every
; occurrence of b is equiv hittable then no matter what braindamaged
; geneqv we use below, the result will be sound!  A braindamaged
; geneqv might prevent us from hitting some, but any hit it allowed is
; ok.

; This bug was first noticed by Bill McCune (September, 1998), who
; reported an example in which the system io indicated that a was
; substituted for b but in fact no substitution occurred.  No
; substitution occurred because we didn't have the congruence theorem
; shown above -- not a surprising lack considering the random nature
; of the problem.  At first I was worried about soundness but then saw
; the argument above.

         (case-match
          lit2
          ((equiv-sym lhs2 rhs2)
           (cond ((not (equal equiv-sym equiv)) (mv nil lit2 ttree))
                 ((eq direction 'left-for-right)
                  (mv-let (hitp new-rhs2 ttree)
                          (subst-equiv-expr equiv lhs1 rhs1
                                            (cadr (geneqv-lst equiv
                                                              *geneqv-iff*
                                                              ens wrld))
                                            rhs2 ens wrld state ttree)
                          (declare (ignore hitp))
                          (mv nil
                              (mcons-term* equiv lhs2 new-rhs2)
                              ttree)))
                 (t
                  (mv-let (hitp new-lhs2 ttree)
                          (subst-equiv-expr equiv rhs1 lhs1
                                            (car (geneqv-lst equiv
                                                             *geneqv-iff*
                                                             ens wrld))
                                            lhs2 ens wrld state ttree)
                          (declare (ignore hitp))
                          (mv nil
                              (mcons-term* equiv new-lhs2 rhs2)
                              ttree)))))
          (& (mv nil lit2 ttree)))))
       (declare (ignore hitp))

; Second, we recursively fertilize appropriately into the rest of the clause.

       (mv-let (new-tail ttree)
               (fertilize-clause1 (cdr cl) lit1 equiv lhs1 rhs1
                                  direction
                                  cross-fert-flg
                                  (if lit2-is-lit1p
                                      nil
                                      delete-lit-flg)
                                  ens wrld state ttree)

; Finally, we combine the two, deleting the lit if required.

               (cond
                (lit2-is-lit1p
                 (cond (delete-lit-flg
                        (mv new-tail
                            (cond ((eq direction 'left-for-right)
                                   (add-binding-to-tag-tree
                                    rhs1 lhs1 ttree))
                                  (t
                                   (add-binding-to-tag-tree
                                    lhs1 rhs1 ttree)))))
                       (t (mv-let (not-flg atm)
                                  (strip-not lit2)
                                  (prog2$
                                   (or not-flg
                                       (er hard 'fertilize-clause1
                                           "We had thought that we only ~
                                            fertilize with negated literals, ~
                                            unlike ~x0!"
                                           new-lit2))
                                   (prog2$
                                    (or (equal lit2 new-lit2) ; should be eq
                                        (er hard 'fertilize-clause1
                                            "Internal error in ~
                                             fertilize-clause1!~|Old lit2: ~
                                             ~x0.~|New lit2: ~x1"
                                            lit2 new-lit2))
                                    (mv (cons (mcons-term* 'not
                                                           (mcons-term* 'hide
                                                                        atm))
                                              new-tail)
                                        ttree)))))))
                (t (mv (cons new-lit2 new-tail) ttree)))))))))

(defun fertilize-clause (cl-id cl hist pspv wrld state)

; A standard clause processor of the waterfall.

; We return 4 values.  The first is a signal that is either 'hit, or
; 'miss.  When the signal is 'miss, the other 3 values are irrelevant.
; When the signal is 'hit, the second result is the list of new
; clauses, the third is a ttree that will become that component of the
; history-entry for this fertilization, and the fourth is an
; unmodified pspv.  (We return the fourth thing to adhere to the
; convention used by all clause processors in the waterfall (q.v.).)

; The ttree we return has seven tagged objects in it plus a bunch
; of 'lemmas indicating the :CONGRUENCE rules used.

; 'literal        - the literal from cl we used, guaranteed to be of
;                   the form (not (equiv lhs rhs)).
; 'clause-id      - the current clause-id
; 'hyp-phrase     - a tilde-@ phrase that describes literal in cl.
; 'equiv          - the equivalence relation
; 'bullet         - the term we substituted
; 'target         - the term we substituted for
; 'cross-fert-flg - whether we did a cross fertilization
; 'delete-lit-flg - whether we deleted literal from the
;                   clause.

  (mv-let (direction lit equiv lhs rhs len-tail)
          (first-fertilize-lit cl cl hist
                               (ens-from-pspv pspv)
                               wrld)
          (cond
           ((null direction) (mv 'miss nil nil nil))
           (t (let ((cross-fert-flg
                     (cross-fertilizep equiv cl pspv direction lhs rhs))
                    (delete-lit-flg
                     (and
                      (not (quotep lhs))
                      (not (quotep rhs))
                      (assoc-eq 'being-proved-by-induction
                                (access prove-spec-var
                                        pspv
                                        :pool)))))
                (mv-let (new-cl ttree)
                        (fertilize-clause1 cl lit equiv lhs rhs
                                           direction
                                           cross-fert-flg
                                           delete-lit-flg
                                           (ens-from-pspv pspv)
                                           wrld
                                           state
                                           nil)
                        (mv 'hit
                            (list new-cl)
                            (add-to-tag-tree!
                             'literal lit
                             (add-to-tag-tree!
                              'hyp-phrase (tilde-@-hyp-phrase len-tail cl)
                              (add-to-tag-tree!
                               'cross-fert-flg cross-fert-flg
                               (add-to-tag-tree!
                                'equiv equiv
                                (add-to-tag-tree!
                                 'bullet (if (eq direction 'left-for-right)
                                             lhs
                                           rhs)
                                 (add-to-tag-tree!
                                  'target (if (eq direction 'left-for-right)
                                              rhs
                                            lhs)
                                  (add-to-tag-tree!
                                   'clause-id cl-id
                                   (add-to-tag-tree!
                                    'delete-lit-flg delete-lit-flg
                                    (if delete-lit-flg
                                        ttree
                                      (push-lemma (fn-rune-nume 'hide nil nil
                                                                wrld)
                                                  ttree))))))))))
                            pspv)))))))

(defun fertilize-clause-msg1 (signal clauses ttree pspv state)

; The arguments to this function are the standard ones for an output
; function in the waterfall.  See the discussion of the waterfall.

  (declare (ignore signal pspv clauses))
  (let* ((hyp-phrase (tagged-object 'hyp-phrase ttree))
         (wrld (w state))
         (ttree

; We can get away with eliminating the :definition of hide from the ttree
; because fertilize-clause1 only pushes lemmas by way of subst-equiv-expr,
; which are either about geneqvs (from geneqv-refinementp) or are executable
; counterparts (from scons-term).  If we do not delete the definition of hide
; from ttree here, we get a bogus "validity of this substitution relies upon
; the :definition HIDE" message.

          (delete-from-ttree 'lemma (fn-rune-nume 'hide nil nil wrld) ttree)))
    (fms "We now use ~@0 by ~#1~[substituting~/cross-fertilizing~] ~p2 for ~p3 ~
          and ~#4~[hiding~/throwing away~] the ~@5.~#6~[~/  The validity of ~
          this substitution relies upon ~*7.~]  This produces~|"
          (list
           (cons #\0 hyp-phrase)
           (cons #\1 (if (tagged-object 'cross-fert-flg ttree)
                         1
                         0))
           (cons #\2 (untranslate (tagged-object 'bullet ttree) nil wrld))
           (cons #\3 (untranslate (tagged-object 'target ttree) nil wrld))
           (cons #\4 (if (tagged-object 'delete-lit-flg ttree)
                         1
                         0))
           (cons #\5 (if (and (consp hyp-phrase)
                              (null (cdr hyp-phrase)))
                         "conclusion"
                         "hypothesis"))
           (cons #\6 (if (tagged-objectsp 'lemma ttree)
                         1
                       0))
           (cons #\7 (tilde-*-simp-phrase ttree)))
          (proofs-co state)
          state
          (term-evisc-tuple nil state))))

; And now we do generalization...

(defun collectable-fnp (fn ens wrld)

; A common collectable term is a non-quoted term that is an
; application of a collectable-fnp.  Most functions are common
; collectable.  The ones that are not are cons, open lambdas, and the
; (enabled) destructors of wrld.

  (cond ((flambdap fn) nil)
        ((eq fn 'cons) nil)
        (t (let ((rule (getpropc fn 'eliminate-destructors-rule nil wrld)))
             (cond ((and rule
                         (enabled-numep (access elim-rule rule :nume) ens))
                    nil)
                   (t t))))))

(mutual-recursion

(defun smallest-common-subterms1 (term1 term2 ens wrld ans)

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
             (fquotep term1))

; Since term1 is not collectable, we don't add it to ans.  But we return
; t as our second value if term1 occurs in term2, i.e., term1 has
; potential.

         (mv ans (occur term1 term2)))

        (t (mv-let
            (ans all-potentials)
            (smallest-common-subterms1-lst (fargs term1) term2 ens wrld ans)
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
                  ((collectable-fnp (ffn-symb term1) ens wrld)

; So term1 occurs, none of its subterms were collected, and term1
; is collectable.  So we collect it, but it no longer has potential
; (because it got collected).

                   (mv (add-to-set-equal term1 ans)
                       nil))

                  (t

; Term1 occurs, none of its subterms were collected, and term1
; was not collected.  So it has potential to participate vicariously.

                   (mv ans t)))))))

(defun smallest-common-subterms1-lst (terms term2 ens wrld ans)

; We accumulate onto ans every subterm of every element of terms
; that (a) occurs in term2, (b) is collectable, and (c) has no
; collectable subterms in common with term2.  We return the modified
; ans and the flag indicating whether all of the terms have potential.

  (cond
   ((null terms) (mv ans t))
   (t (mv-let
       (ans car-potential)
       (smallest-common-subterms1 (car terms) term2 ens wrld ans)
       (mv-let
        (ans cdr-potential)
        (smallest-common-subterms1-lst (cdr terms) term2 ens wrld ans)
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

(defun smallest-common-subterms (term1 term2 ens wrld ans)

; We accumulate onto ans and return the list of every subterm x of
; term1 that is also a subterm of term2, provided x is ``collectable''
; and no subterm of x is collectable.  A term is a collectable if it
; is an application of a collectable-fnp and is not an explicit value.
; Our aim is to collect the ``innermost'' or ``smallest'' collectable
; subterms.

  (mv-let (ans potential)
          (cond ((> (dumb-fn-count term1) (dumb-fn-count term2))
                 (smallest-common-subterms1 term2 term1 ens wrld ans))
                (t (smallest-common-subterms1 term1 term2 ens wrld ans)))
          (declare (ignore potential))
          ans))

(defun generalizing-relationp (term wrld)

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

(defun generalizable-terms-across-relations (cl ens wrld ans)

; We scan clause cl for each literal that is a generalizing-relationp,
; e.g., (equal lhs rhs), and collect into ans all the smallest common
; subterms that occur in each lhs and rhs.  We return the final ans.

  (cond ((null cl) ans)
        (t (mv-let (genp lhs rhs)
                   (generalizing-relationp (car cl) wrld)
                   (generalizable-terms-across-relations
                    (cdr cl) ens wrld
                    (if genp
                        (smallest-common-subterms lhs rhs ens wrld ans)
                        ans))))))

(defun generalizable-terms-across-literals1 (lit1 cl ens wrld ans)
  (cond ((null cl) ans)
        (t (generalizable-terms-across-literals1
            lit1 (cdr cl) ens wrld
            (smallest-common-subterms lit1 (car cl) ens wrld ans)))))

(defun generalizable-terms-across-literals (cl ens wrld ans)

; We consider each pair of literals, lit1 and lit2, in cl and
; collect into ans the smallest common subterms that occur in
; both lit1 and lit2.  We return the final ans.

  (cond ((null cl) ans)
        (t (generalizable-terms-across-literals
            (cdr cl) ens wrld
            (generalizable-terms-across-literals1 (car cl) (cdr cl)
                                                       ens wrld ans)))))

(defun generalizable-terms (cl ens wrld)

; We return the list of all the subterms of cl that we will generalize.
; We look for common subterms across equalities and inequalities, and
; for common subterms between the literals of cl.

  (generalizable-terms-across-literals
   cl ens wrld
   (generalizable-terms-across-relations
    cl ens wrld nil)))

(defun generalize-clause (cl hist pspv wrld state)

; A standard clause processor of the waterfall.

; We return 4 values.  The first is a signal that is either 'hit, or 'miss.
; When the signal is 'miss, the other 3 values are irrelevant.  When the signal
; is 'hit, the second result is the list of new clauses, the third is a ttree
; that will become that component of the history-entry for this generalization,
; and the fourth is an unmodified pspv.  (We return the fourth thing to adhere
; to the convention used by all clause processors in the waterfall (q.v.).)
; The ttree we return is 'assumption-free.

  (declare (ignore state))
  (cond
   ((not (assoc-eq 'being-proved-by-induction
                   (access prove-spec-var pspv :pool)))
    (mv 'miss nil nil nil))
   (t (let* ((ens (ens-from-pspv pspv))
             (terms (generalizable-terms cl ens wrld)))
        (cond
         ((null terms)
          (mv 'miss nil nil nil))
         (t
          (mv-let
           (contradictionp type-alist ttree)
           (type-alist-clause cl nil

; The force-flg probably needs to be nil, to avoid an inappropriate call of
; generalize1.  See the comment about a similar call of type-alist-clause in
; eliminate-destructors-clause1.

                              nil ; force-flg
                              nil ens wrld
                              nil nil)
           (declare (ignore ttree))
           (cond
            (contradictionp

; We compute the type-alist of the clause to allow us to generate nice variable
; names and to restrict the coming generalization.  A contradiction will not
; arise if this clause survived simplification (which it has, unless :do-not
; hints specified that simplification was not to be used).  However, we will
; return an accurate answer just to be rugged.  We'll report that we couldn't
; do anything!  That's really funny.  We just proved our goal and we're saying
; we can't do anything.  But if we made this fn sometimes return the empty set
; of clauses we'd want to fix the io handler for it and we'd have to respect
; the 'assumptions in the ttree and we don't.  Do we?  As usual, we ignore the
; ttree in this case, and hence we ignore it totally since it is known to be
; nil when contradictionp is nil.

             (mv 'miss nil nil nil))
            (t
             (let ((gen-vars
                    (generate-variable-lst terms
                                           (all-vars1-lst cl
                                                          (owned-vars
                                                           'generalize-clause
                                                           nil
                                                           hist))
                                           type-alist ens wrld)))
               (mv-let (generalized-cl restricted-vars var-to-runes-alist ttree)
                       (generalize1 cl type-alist terms gen-vars ens wrld)
                       (mv 'hit
                           (list generalized-cl)
                           (add-to-tag-tree!
                            'variables gen-vars
                            (add-to-tag-tree!
                             'terms terms
                             (add-to-tag-tree!
                              'restricted-vars restricted-vars
                              (add-to-tag-tree!
                               'var-to-runes-alist var-to-runes-alist
                               (add-to-tag-tree!
                                'ts-ttree ttree
                                nil)))))
                           pspv))))))))))))

(defun tilde-*-gen-phrase/alist1 (alist wrld)
  (cond ((null alist) nil)
        (t (cons (msg "~p0 by ~x1"
                      (untranslate (caar alist) nil wrld)
                      (cdar alist))
                 (tilde-*-gen-phrase/alist1 (cdr alist) wrld)))))

(defun tilde-*-gen-phrase/alist (alist wrld)

; Alist is never nil

  (list* "" "~@*" "~@* and " "~@*, "
         (tilde-*-gen-phrase/alist1 alist wrld)
         nil))

(defun tilde-*-gen-phrase (alist restricted-vars var-to-runes-alist ttree wrld)
  (list* "" "~@*" "~@* and " "~@*, "
         (append
          (list (msg "~*0"
                     (tilde-*-gen-phrase/alist alist wrld)))
          (cond
           (restricted-vars
            (let* ((runes (tagged-objects 'lemma ttree))
                   (primitive-type-reasoningp
                    (member-equal *fake-rune-for-type-set* runes))
                   (symbols
                    (strip-base-symbols
                     (remove1-equal *fake-rune-for-type-set* runes))))
              (cond ((member-eq nil symbols)
                     (er hard 'tilde-*-gen-phrase
                         "A fake rune other than ~
                          *fake-rune-for-type-set* was found in the ~
                          ts-ttree generated by generalize-clause.  ~
                          The list of runes in the ttree is ~x0."
                         runes))
                    ((null (cdr restricted-vars))
                     (list (msg "restricting the type of the new ~
                                 variable ~&0 to be that of the term ~
                                 it replaces~#1~[~/, as established ~
                                 by primitive type reasoning~/, as ~
                                 established by ~&2~/, as established ~
                                 by primitive type reasoning and ~&2~]"
                                restricted-vars
                                (cond ((and symbols
                                            primitive-type-reasoningp)
                                       3)
                                      (symbols 2)
                                      (primitive-type-reasoningp 1)
                                      (t 0))
                                symbols)))
                    (t (list (msg "restricting the types of the new ~
                                   variables ~&0 to be those of the ~
                                   terms they replace~#1~[~/, as ~
                                   established by primitive type ~
                                   reasoning~/, as established by ~
                                   ~&2~/, as established by primitive ~
                                   type reasoning and ~&2~]"
                                  restricted-vars
                                  (cond ((and symbols
                                              primitive-type-reasoningp)
                                         3)
                                        (symbols 2)
                                        (primitive-type-reasoningp 1)
                                        (t 0))
                                  symbols))))))
           (t nil))
          (tilde-*-elim-phrase3 var-to-runes-alist))
         nil))

(defun generalize-clause-msg1 (signal clauses ttree pspv state)

; The arguments to this function are the standard ones for an output
; function in the waterfall.  See the discussion of the waterfall.

  (declare (ignore signal pspv clauses))
  (fms "We generalize this conjecture, replacing ~*0.  This produces~|"
       (list
        (cons #\0
              (tilde-*-gen-phrase
               (pairlis$ (tagged-object 'terms ttree)
                         (tagged-object 'variables ttree))
               (tagged-object 'restricted-vars ttree)
               (tagged-object 'var-to-runes-alist ttree)
               (tagged-object 'ts-ttree ttree)
               (w state))))
       (proofs-co state)
       state
       (term-evisc-tuple nil state)))

; The elimination of irrelevance is defined in the same file as induct
; because elim uses m&m.
