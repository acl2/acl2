(in-package "PACO")

; Section:  More on Generating Variable Names

; Our top-level function for generating variables attempts to feed
; genvar with inputs that generate names suggestive of the term being
; replaced by the variable.  We now develop the code for generating
; these roots.  It involves a recursive descent through a term.  At
; the bottom, we see variable symbols, e.g., ABC123, and we wish to
; generate the root '("ABC" . 124).

(defun strip-final-digits1 (lst)
; See strip-final-digits.
  (cond ((endp lst) (mv "" 0))
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
; arbitarily without affecting soundness, as long as (a) the car of
; each pair below is a type set and (b) the cdr is a true-list of
; symbols.  Arbitrary overlaps between the types and between the
; symbols are permitted.

;; RAG - I changed rational to real and complex-rational to complex in
;; the list below, since the new types are supersets of the old types,
;; so it should be harmless.

(defconst *var-families-by-type*
  (list (cons *ts-integer* '(I J K L M N))
        (cons *ts-rational*
              '(R S I J K L M N))
        (cons *ts-complex-rational*
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

  (cond ((endp alist) nil)
        ((ts-subsetp ts (caar alist)) (car alist))
        (t (assoc-ts-subsetp ts (cdr alist)))))

; And here is how we look for an acceptable variable.

(defun first-non-member-eq (lst1 lst2)

; Return the first member of lst1 that is not a member-eq of lst2.

  (cond ((endp lst1) nil)
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

  (declare (xargs :measure (nfix (- (acl2::ifix maximum) (acl2::ifix i)))))
  (cond
   ((or (not (integerp i))
        (not (integerp maximum)))
    nil)
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

(defconst *suspiciously-first-numeric-chars*
  '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9 #\+ #\- #\. #\^ #\_))

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

  (let* ((ts (type-set term type-alist nil ens wrld *type-set-nnn*))
         (family (cdr (assoc-ts-subsetp ts *var-families-by-type*)))
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
               nil)))))

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
   ((eq (ffn-symb term) 'CAR)
    (mv-let (str n)
            (generate-variable-root (fargn term 1) avoid-lst type-alist
                                    ens wrld)
            (mv str (or n 0))))
   ((eq (ffn-symb term) 'CDR)
    (mv-let (str n)
            (generate-variable-root (fargn term 1) avoid-lst type-alist
                                    ens wrld)
            (mv str (or n 0))))
   (t (generate-variable-root1 term avoid-lst type-alist ens wrld))))

; We must be able to find a package witness for the variable we generate.
; We search the term for a likely symbol.

(mutual-recursion

(defun find-first-var (term)
  (cond ((variablep term) term)
        ((fquotep term) nil)
        ((find-first-var-lst (fargs term)))
        ((flambdap (ffn-symb term))
         (car (lambda-formals (ffn-symb term))))
        (t nil)))

(defun find-first-var-lst (lst)
  (cond ((endp lst) nil)
        (t (or (find-first-var (car lst))
               (find-first-var-lst (cdr lst))))))
)

(mutual-recursion

(defun find-first-fnsymb (term)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambdap (ffn-symb term))
         (or (find-first-fnsymb-lst (fargs term))
             (find-first-fnsymb (lambda-body (ffn-symb term)))))
        (t (ffn-symb term))))

(defun find-first-fnsymb-lst (lst)
  (cond ((endp lst) nil)
        (t (or (find-first-fnsymb (car lst))
               (find-first-fnsymb-lst (cdr lst))))))
)

(defun find-pkg-witness (term)

; This function must return a symbol.  Imagine that term is to be replaced by
; some variable symbol.  In which package do we intern that symbol?  This
; function finds a symbol which is used with intern-in-package-of-symbol.
; Thus, the package of the returned symbol is important to human readability.
; We return the first variable we see in term, if there is one.  Otherwise, we
; return the first function symbol we see, if there is one.  Otherwise, we
; return the symbol 'find-pkg-witness.

  (or (find-first-var term)
      (find-first-fnsymb term)
      'find-pkg-witness))



(defun generate-variable (term avoid-lst type-alist ens wrld)

; We generate a legal variable symbol that does not occur in
; avoid-lst.  We use term, type-alist and wrld in a heuristic way to
; suggest a preferred name for the symbol.  Generally speaking, the
; symbol we generate will be used to replace term in some conjecture,
; so we try to generate a symbol that we think "suggests" term.

  (mv-let (str n)
          (generate-variable-root term avoid-lst type-alist ens wrld)
          (genvar (find-pkg-witness term) str n avoid-lst)))

(defun generate-variable-lst (term-lst avoid-lst type-alist ens wrld)

; And here we generate a list of variable names sequentially, one for
; each term in term-lst.

  (cond ((endp term-lst) nil)
        (t
         (let ((var (generate-variable (car term-lst) avoid-lst
                                       type-alist ens wrld)))
           (cons var (generate-variable-lst (cdr term-lst)
                                            (cons var avoid-lst)
                                            type-alist ens wrld))))))


; ---------------------------------------------------------------------------
; Section:  Destructor Elim Rules

; An elim-rule, as declared below, denotes a theorem of the form
; (implies hyps (equal lhs rhs)), where rhs is a variable symbol and
; lhs involves the terms destructor-terms, each of which is of the
; form (dfn v1 ... vn), where the vi are distinct variables and {v1
; ... vn} are all the variables in the formula.  We call rhs the
; "crucial variable".  It is the one we will "puff up" to eliminate
; the destructor terms.  For example, in (CONSP X) -> (CONS (CAR X)
; (CDR X)) = X, X is the crucial variable and by puffing it up to (CONS A
; B) we can eliminate (CAR X) and (CDR X).  We store an elim-rule
; under the function symbol, dfn, of each destructor term.  The rule
; we store for (dfn v1 ... vn) has that term as the car of destructor-
; terms and has crucial-position j where (nth j '(v1 ... vn)) = rhs.
; (Thus, the crucial-position is the position in the args at which the
; crucial variable occurs and for these purposes we enumerate the args
; from 0 (as by nth) rather than from 1 (as by fargn).)

(defrec elim-rule
  (((nume . crucial-position) . (destructor-term . destructor-terms))
   (hyps . equiv)
   .
   (lhs . rhs)))

; In Paco, equiv is always EQUAL.

(defun occurs-nowhere-else (var args c i)

; Index the elements of args starting at i.  Scan all args except the
; one with index c and return nil if var occurs in one of them and t
; otherwise.

  (cond ((endp args) t)
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

  (cond ((endp nominations) nil)
        ((equal term (car (car nominations)))
         (cons (cons term
                     (union-equal votes (cdr (car nominations))))
               (cdr nominations)))
        (t (cons (car nominations)
                 (second-nomination term votes (cdr nominations))))))


(defun some-hyp-probably-nilp (hyps type-alist ens wrld)

; The name of this function is meant to limit its use to heuristics.
; In fact, if this function says some hyp is probably nil then in fact
; some hyp is known to be nil under the given type-alist and wrld.

  (cond
   ((endp hyps) nil)
   (t (mv-let
       (knownp nilp)
       (known-whether-nil
        (car hyps) type-alist ens wrld)
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
  (cond ((endp lst) nil)
        (t (cons (sublis-expr alist (car lst))
                 (sublis-expr-lst alist (cdr lst))))))

)

(defthm acl2-count-nth
  (<= (acl2-count (nth i x)) (acl2-count x))
  :rule-classes :linear)

(defun nominate-destructor-candidate
  (term eliminables type-alist ens wrld votes nominations)

  (declare (xargs :measure (acl2-count term)))

; This function recognizes candidates for destructor elimination.  It
; is assumed that term is a non-variable, non-quotep term.  To be a
; candidate the term must not be a lambda application and the function
; symbol of the term must have an enabled destructor elimination rule.
; Furthermore, the crucial argument position of the term must be
; occupied by a variable symbol that is a member of the eliminables
; and that occurs nowhere else in the arguments of the term, or else
; the crucial argument position must be occupied by a term that itself
; is recursively a candidate.  (The :equiv slot of the rule will be
; EQUAL; should we expand Paco's elim technique to deal with other
; equivalence relations, we have to check that the crucial var occurs
; only in equiv-hittable positions within the target clause.)  (Note
; that if the crucial argument is an eliminable term then when we
; eliminate it we will introduce a suitable distinct var into the
; crucial argument of this term and hence it will be eliminable.)
; Finally, the instantiated hypotheses of the destructor elimination
; rule must not be known nil under the type-alist.

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
   (t (let ((rule (getprop (ffn-symb term) 'eliminate-destructors-rule
                           nil wrld)))
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

                (let* ((alist (pairlis
                               (fargs
                                (access elim-rule rule :destructor-term))
                               (fargs term))))
                  (cond
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
                                                 ens
                                                 wrld
                                                 (cons term votes)
                                                 nominations))))))))))

(mutual-recursion

(defun nominate-destructor-candidates
  (term eliminables type-alist ens wrld nominations)

; We explore term and accumulate onto nominations all the nominations.

  (cond ((variablep term) nominations)
        ((fquotep term) nominations)
        (t (nominate-destructor-candidates-lst
            (fargs term)
            eliminables
            type-alist
            ens
            wrld
            (nominate-destructor-candidate term
                                           eliminables
                                           type-alist
                                           ens
                                           wrld
                                           nil
                                           nominations)))))

(defun nominate-destructor-candidates-lst
  (terms eliminables type-alist ens wrld nominations)
  (cond ((endp terms) nominations)
        (t (nominate-destructor-candidates-lst
            (cdr terms)
            eliminables
            type-alist
            ens
            wrld
            (nominate-destructor-candidates (car terms)
                                             eliminables
                                             type-alist
                                             ens
                                             wrld
                                             nominations)))))

)

; We next turn to the problem of choosing which candidate we will
; eliminate.  We want to eliminate the most complicated one.  We
; measure them with max-level-no.  The level-no of each function
; symbol is computed at definition time and stored as a property of
; that name.  Functions with no stored level-no (primitives) have
; level-no 0.  Lambda expressions are assigned the max level-no
; of their bodies.

(mutual-recursion

(defun max-level-no (term wrld)
  (cond ((variablep term) 0)
        ((fquotep term) 0)
        (t (max (get-level-no (ffn-symb term) wrld)
                (max-level-no-lst (fargs term)
                                  wrld)))))

(defun max-level-no-lst (args wrld)
  (cond ((endp args) 0)
        (t (max (max-level-no (car args) wrld)
                (max-level-no-lst (cdr args) wrld)))))

(defun get-level-no (fn wrld)
  (cond ((flambdap fn) (max-level-no (lambda-body fn) wrld))
        ((getprop fn 'level-no nil wrld))
        (t 0)))

)

(defun sum-level-nos (lst wrld)

; Lst is a list of non-variable, non-quotep terms.  We sum the
; level-no of the function symbols of the terms.

  (cond ((endp lst) 0)
        (t (+ (if (flambda-applicationp (car lst))
                  (max-level-no (lambda-body (ffn-symb (car lst))) wrld)
                  (or (getprop (ffn-symb (car lst)) 'level-no nil wrld)
                      0))
              (sum-level-nos (cdr lst) wrld)))))

(defun pick-highest-sum-level-nos (nominations wrld dterm max-score)

; Nominations is a list of pairs of the form (dterm . votes), where
; votes is a list of terms.  The "score" of a dterm is the
; sum-level-nos of its votes.  We scan nominations and return a dterm
; with maximal score, assuming that dterm and max-score are the
; winning dterm and its score seen so far.

  (cond
   ((endp nominations) dterm)
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
; will have been introduced by elim).

; If there is at least one nomination for an elim, we choose the one
; with maximal score and return an instantiated version of the
; elim-rule corresponding to it.  Otherwise we return nil.

  (let ((nominations
         (nominate-destructor-candidates-lst clause
                                             eliminables
                                             type-alist
                                             ens
                                             wrld
                                             nil)))
    (cond
     ((endp nominations) nil)
     (t
      (let* ((dterm (pick-highest-sum-level-nos nominations wrld nil -1))
             (rule (getprop (ffn-symb dterm) 'eliminate-destructors-rule
                            nil wrld))
             (alist (pairlis (fargs (access elim-rule rule :destructor-term))
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

; We now take a break from elim and develop the code for the
; generalization that elim uses.  After replacing a term by a variable
; (sublis-expr, above), must to restrict the new variable by noting
; the type-set of the term replaced.  We must also use generalization
; rules provided in the data base.

; We now develop the function that converts a type-set into a term.

(defrec type-set-inverter-rule ((nume . ts) . terms))

; A type-set-inverter-rule states that x has type-set ts iff the conjunction of
; terms{X/x} is true.  Thus, for example, if :ts is *ts-integer* then :terms is
; '((INTEGERP X)).

; A type-set, s, is a disjunction of the individual bits in it.  Thus, to
; create a term whose truth is equivalent to the claim that X has type-set s it
; is sufficient to find any type-set-inverter-rule whose :ts is a subset of s
; and then disjoin the :term of that rule to the result of recursively creating
; the term recognizing s minus :ts.  This assumes one has a rule for each
; single type bit.

; The database contains a global-val, type-set-inverter-rules, of all
; known type-set-inverter-rules.  The list is ordered in a
; heuristically important way: the larger type-sets are at the front.
; This ordering is exploited by convert-type-set-to-term-lst which
; operates by finding the largest recognized type set group and knocks
; it out of the type set.

(defun convert-type-set-to-term-lst (ts rules ens lst)

; We map over the list of type-set-inverter rules and each time we
; find an enabled rule whose :ts is a subset of ts, we accumulate its
; conjoined :terms and its :rune, and knock off those bits of ts.  We
; return lst, where lst is a list of terms in the variable X whose
; disjunction is equivalent to ts.

  (cond
   ((endp rules) (reverse lst))
   ((and (enabled-numep (access type-set-inverter-rule (car rules) :nume) ens)
         (ts= (access type-set-inverter-rule (car rules) :ts)
              (ts-intersection
               (access type-set-inverter-rule (car rules) :ts)
               ts)))
    (<convert-type-set-to-term-lst-id>
     (convert-type-set-to-term-lst
      (ts-intersection
       ts
       (ts-complement (access type-set-inverter-rule (car rules) :ts)))
      (cdr rules)
      ens
      (add-to-set-equal
       (conjoin (access type-set-inverter-rule (car rules) :terms))
       lst))))
   (t (convert-type-set-to-term-lst ts (cdr rules) ens lst))))

(defun convert-type-set-to-term (x ts ens w)

; Given a term x and a type set ts we generate a term that expresses
; the assertion that "x has type set ts".  E.g., if x is the term (FN
; X Y) and ts is *ts-rational* then our output will be (RATIONALP (FN
; X Y)).  We return term.  We do not use disabled type-set-inverters.

  (cond ((ts= ts *ts-unknown*) *t*)
        ((and (ts= ts *ts-t*)
              (ts-booleanp x nil ens w))
         x)
        ((ts-complementp ts)
         (subst-var x 'x
                    (conjoin
                     (dumb-negate-lit-lst
                      (convert-type-set-to-term-lst
                       (ts-complement ts)
                       (global-val 'type-set-inverter-rules w)
                       ens nil)))))
        (t (subst-var x 'x
                      (disjoin
                       (convert-type-set-to-term-lst
                        ts
                        (global-val 'type-set-inverter-rules w)
                        ens nil))))))

(defun type-restriction-segment (terms vars type-alist ens wrld)

; Terms is a list of terms.  Vars is a list in 1:1 correspondence with
; terms.  We are in the process of generalizing some clause by
; replacing each term with the corresponding var.  We wish to restrict
; the new vars to have the types of their terms.  Type-alist is the
; result of assuming false every literal of the clause.

; This function returns a list of literals that can be disjoined to
; the GENERALIZED clause.  That is, the new literals contain the new
; vars, not the old terms.

; It is sound, of course, to restrict the new variable to have
; whatever properties the corresponding term has.  This function is
; responsible for selecting the restrictions we want to place on each
; variable, based on type-set reasoning alone.  Thus, if t is known to
; have properties h1 & ... & hk, then we can include (not h1), ...,
; (not hk) in our first answer to restrict the variable introduced for
; t.

; We do not want our type restrictions to cause the new clause to
; explode into cases.  Therefore, we adopt the following heuristic.
; We convert the type set of each term t into a term (hyp t) known to
; be true of t.  Then we generalize t to the var v.  We negate (hyp v)
; and clausify the result.  If that produces a single clause (segment)
; then that segment is added to our answer.  Otherwise, we add no
; restriction.  There are probably better ways to do this than to call
; the full-blown convert-type-set-to-term and clausify.  But this is
; simple, elegant, and lets us take advantage of improvements to those
; two utilities.

; Subtle Design Issue: Once upon a time, Paco clausified (not (hyp t))
; rather than (not (hyp v)) and then generalized the assembled clause.
; But because Paco's clausify uses type-set, this strategy (which is
; used by ACL2) doesn't work!  The clausify below erased much of the
; the type information.  E.g., if we're restricting (* i j) to with
; (acl2-numberp (* i j)), the clausification will just eliminate the
; restriction.  We must create (acl2-numberp (* i j)), generalize it
; to (acl2-numberp v), and then clausify.

  (cond
   ((endp terms) nil)
   (t
    (let* ((ts
            (type-set (car terms) type-alist nil ens wrld *type-set-nnn*))
           (generalized-term
            (convert-type-set-to-term (car vars) ts ens wrld))
           (clauses
            (clausify (dumb-negate-lit generalized-term) ens wrld))
           (lits
            (type-restriction-segment (cdr terms)
                                      (cdr vars)
                                      type-alist ens wrld)))
      (cond ((null clauses)

; If the negation of the type restriction term clausifies to the empty
; set of clauses, then the term is nil.  Since we get to assume it,
; we're done.  But this can only happen if the type-set of the term is
; empty.  We don't think this will happen, but we test for it
; nonetheless, and toss a nil hypothesis into our answer literals if
; it happens.

             (add-to-set-equal *nil* lits))
            ((and (endp (cdr clauses))
                  (not (endp (car clauses))))

; If there is only one clause and it is not the empty clause, we'll
; assume everything in it.  (If the clausify above produced '(NIL)
; then the type restriction was just *t* and we ignore it.)

             (disjoin-clauses (car clauses) lits))
            (t

; There may be useful type information we could extract, but we don't.
; It is always sound to exit here, giving ourselves no additional
; assumptions.

             lits))))))

(mutual-recursion

(defun subterm-one-way-unify (pat term)

; This function searches pat for a non-variable non-quote subterm s
; such that (one-way-unify s term) returns t and a unify-subst.  If it
; finds one, it returns t and the unify-subst.  Otherwise, it returns
; two nils.

  (cond ((variablep pat) (mv nil nil))
        ((fquotep pat) (mv nil nil))
        (t (mv-let (ans alist)
                   (one-way-unify pat term)
                   (cond (ans (mv ans alist))
                         (t (subterm-one-way-unify-lst (fargs pat) term)))))))

(defun subterm-one-way-unify-lst (pat-lst term)
  (cond
   ((endp pat-lst) (mv nil nil))
   (t (mv-let (ans alist)
              (subterm-one-way-unify (car pat-lst) term)
              (cond (ans (mv ans alist))
                    (t (subterm-one-way-unify-lst (cdr pat-lst) term)))))))

)

(defrec generalize-rule (nume . formula))

(defun apply-generalize-rule (gen-rule term ens)

; Gen-rule is a generalization rule.  Term is a term which we are
; intending to generalize by replacing it with a new variable.  We
; return two results.  The first is either t or nil indicating whether
; gen-rule provides a useful restriction on the generalization of
; term.  If the first result is nil, so is the second.  Otherwise, the
; second result is an instantiation of the formula of gen-rule in
; which term appears.

; Our heuristic for deciding whether to use gen-rule is: (a) the rule
; must be enabled, (b) term must unify with a non-variable non-quote
; subterm of the formula of the rule, (c) the unifying substitution
; must leave no free vars in that formula, and (d) the function symbol
; of term must not occur in the instantiation of the formula except in
; the occurrences of term itself.

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
                   (t
                    (<apply-generalize-rule-id>
                     (mv t inst-formula)))))))))))

(defun generalize-rule-segment1 (generalize-rules term ens)

; Given a list of :GENERALIZE rules and a term we return the list of
; instantiated negated formulas of those applicable rules.  The list
; is suitable for splicing into a clause to add the formulas as
; hypotheses.

  (cond
   ((endp generalize-rules) nil)
   (t (mv-let (ans formula)
              (apply-generalize-rule (car generalize-rules) term ens)
              (let ((formulas
                     (generalize-rule-segment1 (cdr generalize-rules)
                                               term ens)))
                (cond (ans (add-literal (dumb-negate-lit formula)
                                        formulas nil))
                      (t formulas)))))))

(defun generalize-rule-segment (terms ens wrld)

; Given a list of terms, we return a clause segment containing the
; instantiated negated formulas derived from every applicable
; :GENERALIZE rule for each term in terms.  This segment can be
; spliced into a clause to restrict the range of a generalization of
; terms.

  (cond
   ((endp terms) nil)
   (t (disjoin-clauses
       (generalize-rule-segment1 (global-val 'generalize-rules wrld)
                                 (car terms) ens)
       (generalize-rule-segment (cdr terms) ens wrld)))))

(defun generalize1 (cl type-alist terms vars ens wrld)

; Cl is a clause.  Type-alist is a type-alist obtained by assuming all
; literals of cl false.  Terms and vars are lists of terms and
; distinct variables, respectively, in 1:1 correspondence.  We assume
; no var in vars occurs in cl.  We generalize cl by substituting vars
; for the corresponding terms.  We restrict the variables by using
; type-set information about the terms and by using :GENERALIZE rules
; in wrld.

; We return the new clause.

  (disjoin-clauses
   (type-restriction-segment terms vars type-alist ens wrld)
   (sublis-expr-lst
    (pairlis terms vars)
    (disjoin-clauses (generalize-rule-segment terms ens wrld) cl))))

; This completes our brief flirtation with generalization.  We now
; have enough machinery to finish coding destructor elimination.
; However, it might be noted that generalize1 is the main subroutine
; of the generalize-clause waterfall processor.

(defun apply-instantiated-elim-rule (rule cl type-alist avoid-vars ens wrld)

; This function takes an instantiated elim-rule, rule, and applies it
; to a clause cl.  Avoid-vars is a list of variable names to avoid
; when we generate new ones.  See eliminate-destructors-clause for
; an explanation of that.

; An instantiated :ELIM rule has hyps, lhs, rhs, and destructor-terms,
; all instantiated so that the car of the destructor terms occurs
; somewhere in the clause.  To apply such an instantiated :ELIM rule to
; a clause we assume the hyps (adding their negations to cl), we
; generalize away the destructor terms occurring in the clause and in
; the lhs of the rule, and then we substitute that generalized lhs for
; the rhs into the generalized cl to obtain the final clause.  The
; generalization step above may involve adding additional hypotheses
; to the clause and using generalization rules in wrld.

; We return two things: the clause described above, which implies cl
; if the hyps of the rule are known to be true and the set of elim
; variables we have just introduced into it.

  (<apply-instantiated-elim-rule-id>
   (let* ((hyps (access elim-rule rule :hyps))
          (lhs (access elim-rule rule :lhs))
          (rhs (access elim-rule rule :rhs))
          (dests (access elim-rule rule :destructor-terms))
          (negated-hyps (dumb-negate-lit-lst hyps))
          (cl-with-hyps (disjoin-clauses negated-hyps cl)))
     (mv-let
      (contradictionp type-alist)
      (type-alist-clause negated-hyps type-alist ens wrld)
      (cond
       (contradictionp

; We compute the type-alist of the clause to allow us to generate nice
; variable names and to restrict the coming generalization.  We know
; that a contradiction cannot arise, because we would not have chosen
; an :ELIM rule with nil hypotheses.  However, we will return an
; accurate answer, namely cl.  We'll report that we introduced the
; variable rhs (which was actually already there) thus preventing any
; future attempt to elim it.

        (mv cl (list rhs)))
       (t
        (let* ((elim-vars (generate-variable-lst dests
                                                 (all-vars1-lst cl-with-hyps
                                                                avoid-vars)
                                                 type-alist ens wrld))
               (generalized-cl-with-hyps
                (generalize1 cl-with-hyps type-alist dests elim-vars
                             ens wrld))
               (alist (pairlis dests elim-vars))
               (generalized-lhs (sublis-expr alist lhs))
               (final-cl
                (subst-var-lst generalized-lhs
                               rhs
                               generalized-cl-with-hyps))
               (actual-elim-vars
                (intersection-eq elim-vars
                                 (all-vars1-lst final-cl nil))))
          (mv final-cl
              actual-elim-vars))))))))

(defun eliminate-destructors-clause1
  (cl eliminables avoid-vars ens wrld top-flg nnn)

; Cl is a clause we are trying to prove.  Eliminables is the set of
; variables on which we will permit a destructor elimination.
; Avoid-vars is a list of variable names we are to avoid when
; generating new names.  In addition, we avoid the variables in cl.
; (See below and then the discussion in owned-vars, further below, for
; more on variable name avoidance.)  We look for an eliminable
; destructor, select the highest scoring one and get its instantiated
; rule, split on the hyps of that rule to produce a "pathological"
; case of cl for each hyp and apply the rule to cl to produce the
; "normal" elim case.  Then we iterate until there is nothing more to
; eliminate.

; The handling of the eliminables needs explanation however.  At the
; top-level (when top-flg is t) eliminables is the set of all
; variables occurring in cl except those historically introduced by
; destructor elimination.  It is with respect to that set that we
; select our first elimination rule.  Thereafter (when top-flg is nil)
; the set of eliminables is always just the set of variables we have
; introduced into the clauses.  We permit these variables to be
; eliminated by this elim and this elim only.  For example, the
; top-level entry might permit elimination of (CAR X) and of (CAR Y).
; Suppose we choose X, introducing A and B.  Then on the second
; iteration, we'll allow eliminations of A and B, but not of Y.

; We return two things.  The first is a set of clauses to prove
; instead of cl.  The second is the set of variable names introduced
; by this destructor elimination step.

  (declare (xargs :measure (acl2-count nnn)))
  (cond
   ((zp nnn)

; We have an artificial termination condition to make admission
; simple.  This function probably terminates without this, because the
; number of eligible destructor terms in it decreases every round.
; But rather than try to formalize that measure, we just count down.
; The answer below is always correct: to prove cl it is sufficient to
; prove the set of clauses containing cl, and no new variables were
; introduced.

    (mv (list cl) nil))
   (t

; Our first step is to get the type-alist of cl.  It is used in two
; different ways: to identify contradictory hypotheses of candidate
; :ELIM lemmas and to generate names for new variables.

    (mv-let
     (contradictionp type-alist)
     (type-alist-clause cl nil ens wrld)
     (cond
      (contradictionp

; This is unusual.  We don't really expect to find a contradiction.

       (mv (list cl) nil))
      (t
       (let ((rule (select-instantiated-elim-rule cl type-alist eliminables
                                                  ens wrld)))
         (cond
          ((null rule)
           (mv (list cl) nil))
          (t
           (let ((clauses1 (split-on-assumptions
                            (access elim-rule rule :hyps)
                            cl nil)))

; Clauses1 is a set of clauses obtained by splitting on the
; instantiated hyps of the rule.  It contains n clauses, each obtained
; by adding one member of inst-hyps to cl.  (If any of these new
; clauses is a tautology, it will be deleted, thus there may not be as
; many clauses as there are inst-hyps.)  Because these n clauses are
; all "pathological" wrt the destructor term, e.g., we're assuming
; (not (consp x)) in a clause involving (car x), we do no further
; elimination down those paths.

             (mv-let
              (new-clause elim-vars1)
              (apply-instantiated-elim-rule rule cl type-alist
                                            avoid-vars ens wrld)
              (cond
               ((equal new-clause *true-clause*)
                (mv clauses1 elim-vars1))
               (t
                (mv-let
                 (clauses2 elim-vars2)
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
                  nil
                  (- nnn 1))
                 (mv (conjoin-clause-sets clauses1 clauses2)
                     (union-eq elim-vars1 elim-vars2))))))))))))))))

(defconst *eliminate-destructors-nnn* 10)

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

; Every history entry has an :alist field and if the process for the
; entry introduced new variables, those variables are listed in the
; :VARIABLES pair of that alist.

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

  (cond ((endp history) nil)
        ((eq mine-flg
             (eq (access history-entry (car history) :processor)
                 process))
         (union-eq (cdr (assoc-eq :VARIABLES
                                  (access history-entry (car history) :alist)))
                   (owned-vars process mine-flg (cdr history))))
        (t (owned-vars process mine-flg (cdr history)))))

(defun eliminate-destructors-clause (id cl hist pspv wrld)

; This is the waterfall processor that eliminates destructors.  Like
; all waterfall processors it returns four values: 'hit or 'miss, and,
; if 'hit, a set of clauses, a history alist, and a possibly modified
; pspv.

  (declare (ignore id))
  (mv-let
   (clauses elim-vars)
   (eliminate-destructors-clause1 cl
                                  (set-difference-eq
                                   (all-vars1-lst cl nil)
                                   (owned-vars 'eliminate-destructors-clause t
                                               hist))
                                  (owned-vars 'eliminate-destructors-clause nil
                                              hist)
                                  (access rewrite-constant
                                          (access prove-spec-var
                                                  pspv
                                                  :rewrite-constant)
                                          :ens)
                                  wrld
                                  t
                                  *eliminate-destructors-nnn*)
   (cond (elim-vars (mv 'hit clauses
                        (list (cons :VARIABLES elim-vars))
                       pspv))
         (t (mv 'miss nil nil nil)))))

