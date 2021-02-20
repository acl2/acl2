(in-package "PACO")

; ----------------------------------------------------------------
; Section: Numes and Enabled Structures

; In Paco, all rules in the database are numbered by integers,
; called ``numes''.  (In ACL2, all rules have names, called
; ``runes'' or ``rule names'' such as (:REWRITE ASSOC-OF-APP).
; To each rune there corresponds a unique integer called the
; ``number of the rune'' or ``nume.''  Paco's numes are ACL2's
; numes; Paco does not have runes.)

; Each rule has a ``status'' which is either ``enabled'' or
; ``disabled.''  Disabled rules are not used automatically.  The
; status of a rule is determined by an ``enabled structure'' or
; ``ens'' (pronounced ``eee-in-ess'').  Abstractly an ens is a set
; containing the enabled rules.  Concretely, in Paco, an ens is a
; balanced binary tree, btree, containing the numes of the
; DISabled rules.

(defun enabled-numep (nume ens)

; Some rules have nil for their "nume".  These are built-in and
; are always considered enabled.  For example, consider the
; initial elements of (global-val 'built-in-clauses (w)).

  (or (null nume)
      (not (in-btreep nume ens))))

; It must be possible to map from a function symbol, fn, to the
; numes corresponding to (:DEFINITION fn) and
; (:EXECUTABLE-COUNTERPART fn).

(defun fn-nume (keyword fn w)
  (let ((lst (getprop fn 'FN-NUMES '(0 0 0) w)))
    (case keyword
      (:DEFINITION (car lst))
      (:EXECUTABLE-COUNTERPART (cadr lst))
      (:INDUCTION (caddr lst))
      (otherwise 0))))

;-----------------------------------------------------------------
; Section: Term Construction and Manipulation

(defmacro variablep (x) (list 'atom x))

(defmacro nvariablep (x) (list 'consp x))

(defmacro fquotep (x) (list 'eq ''quote (list 'car x)))

(defun quotep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (eq (car x) 'quote)))

(defmacro unquote (x) (list 'cadr x))

(defmacro ffn-symb (x) (list 'car x))

(defun fn-symb (x)
  (declare (xargs :guard t))
  (if (and (nvariablep x)
           (not (fquotep x)))
      (car x)
    nil))

(defmacro fargs (x) (list 'cdr x))

(defmacro fcons-term* (&rest x)
  (cons 'list x))

(defmacro fcons-term (fn args) (list 'cons fn args))

(defun fargn1 (x n)
  (cond ((zp n) 'fargn1-zero-case-error)
        ((equal n 1) (list 'cdr x))
        (t (list 'cdr (fargn1 x (- n 1))))))

(defmacro fargn (x n)
  (list 'car (fargn1 x n)))

(defmacro flambda-applicationp (term)

; Term is assumed to be nvariablep.

  `(consp (car ,term)))

(defmacro lambda-applicationp (term)
  `(let ((temp ,term))
     (and (consp temp)
          (flambda-applicationp temp))))

(defmacro flambdap (fn)

; Fn is assumed to be the fn-symb of some term.

  `(consp ,fn))

(defmacro lambda-formals (x) `(cadr ,x))

(defmacro lambda-body (x) `(caddr ,x))

(defmacro make-lambda (args body)
  `(list 'lambda ,args ,body))

(defun formals (fn w)
  (cond ((flambdap fn)
         (lambda-formals fn))
        (t (getprop fn 'formals nil w))))

(defun arity (fn w)
  (cond ((flambdap fn) (length (lambda-formals fn)))
        (t (let ((temp (getprop fn 'formals t w)))
             (cond ((eq temp t) nil)
                   (t (length temp)))))))

(defun body (fn normalp w)
  (cond ((flambdap fn)
         (lambda-body fn))
        (normalp (getprop fn 'body nil w))
        (t (getprop fn 'unnormalized-body nil w))))

(mutual-recursion

(defun pseudo-termp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (symbolp x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cdr (cdr x)))))
        ((not (true-listp x)) nil)
        ((not (pseudo-term-listp (cdr x))) nil)
        (t (or (symbolp (car x))

; For most function applications we do not check that the number
; of arguments matches the number of formals.  However, for
; lambda applications we do make that check.  The reason is that
; the constraint on an evaluator dealing with lambda applications
; must use pairlis$ to pair the formals with the actuals and
; pairlis$ insists on the checks below.

               (and (true-listp (car x))
                    (equal (length (car x)) 3)
                    (eq (car (car x)) 'lambda)
                    (symbol-listp (cadr (car x)))
                    (pseudo-termp (caddr (car x)))
                    (equal (length (cadr (car x)))
                           (length (cdr x))))))))

(defun pseudo-term-listp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (equal lst nil))
        (t (and (pseudo-termp (car lst))
                (pseudo-term-listp (cdr lst))))))

)

(defun all-variablep (lst)
  (cond ((endp lst) t)
        (t (and (variablep (car lst))
                (all-variablep (cdr lst))))))

(defun all-quoteps (lst)
  (cond ((endp lst) t)
        (t (and (quotep (car lst))
                (all-quoteps (cdr lst))))))

(mutual-recursion

(defun all-vars1 (term ans)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp ans))))
  (cond ((variablep term)
         (add-to-set-eq term ans))
        ((fquotep term) ans)
        (t (all-vars1-lst (fargs term) ans))))

(defun all-vars1-lst (lst ans)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (symbol-listp ans))))
  (cond ((endp lst) ans)
        (t (all-vars1-lst (cdr lst)
                          (all-vars1 (car lst) ans)))))

)

(defun all-vars (term)

; This function collects the variables in term in reverse print
; order of first occurrence.  E.g., all-vars of '(f (g a b) c) is
; '(c b a).  This ordering is exploited by, at least,
; loop-stopper and bad-synp-hyp.

  (declare (xargs :guard (pseudo-termp term)
                  :verify-guards nil))
  (all-vars1 term nil))

; Matching

(defun equal-x-constant (x const)

; x is an arbitrary term, const is a quoted constant, e.g., a
; list of the form (QUOTE guts).  We return a term equivalent to
; (equal x const).

  (let ((guts (cadr const)))
    (cond ((symbolp guts)
           (list 'eq x const))
          ((or (acl2-numberp guts)
               (characterp guts))
           (list 'eql x guts))
          ((stringp guts)
           (list 'equal x guts))
          (t (list 'equal x const)))))

(defun match-tests-and-bindings (x pat tests bindings)

; We return two results.  The first is a list of tests, in
; reverse order, that determine whether x matches the structure
; pat.  We describe the language of pat below.  The tests are
; accumulated onto tests, which should be nil initially.  The
; second result is an alist containing entries of the form (sym
; expr), suitable for use as the bindings in the let we generate
; if the tests are satisfied.  The bindings required by pat are
; accumulated onto bindings and thus are reverse order, although
; their order is actually irrelevant.

; For example, the pattern
;   ('equal ('car ('cons u v)) u)
; matches only first order instances of
; (EQUAL (CAR (CONS u v)) u).

; The pattern
;   ('equal (ev (simp x) a) (ev x a))
; matches only second order instances of
; (EQUAL (ev (simp x) a) (ev x a)),
; i.e., ev, simp, x, and a are all bound in the match.

; In general, the match requires that the cons structure of x be
; isomorphic to that of pat, down to the atoms in pat.  Symbols
; in the pat denote variables that match anything and get bound
; to the structure matched.  Occurrences of a symbol after the
; first match only structures equal to the binding.  Non-symbolp
; atoms match themselves.

; There are some exceptions to the general scheme described
; above.  A cons structure starting with QUOTE matches only
; itself.  The symbols nil and t, and all symbols whose
; symbol-name starts with #\* match only structures equal to
; their values.  (These symbols cannot be legally bound in ACL2
; anyway, so this exceptional treatment does not restrict us
; further.)  Any symbol starting with #\! matches only the value
; of the symbol whose name is obtained by dropping the #\!.  This
; is a way of referring to already bound variables in the
; pattern.  Finally, the symbol & matches anything and causes no
; binding.

  (cond
   ((symbolp pat)
    (cond
     ((or (eq pat t)
          (eq pat nil))
      (mv (cons (list 'eq x pat) tests) bindings))
     ((and (> (length (symbol-name pat)) 0)
           (eql #\* (char (symbol-name pat) 0)))
      (mv (cons (list 'equal x pat) tests) bindings))
     ((and (> (length (symbol-name pat)) 0)
           (eql #\! (char (symbol-name pat) 0)))
      (mv (cons (list 'equal x
                      (intern
                       (coerce (cdr (coerce (symbol-name pat)
                                            'list))
                               'string)
                       "ACL2"))
                tests)
          bindings))
     ((eq pat '&) (mv tests bindings))
     (t (let ((binding (assoc pat bindings)))
          (cond ((null binding)
                 (mv tests (cons (list pat x) bindings)))
                (t (mv (cons (list 'equal x (cadr binding)) tests)
                       bindings)))))))
   ((atom pat)
    (mv (cons (equal-x-constant x (list 'quote pat)) tests)
        bindings))
   ((eq (car pat) 'quote)
    (mv (cons (equal-x-constant x pat) tests)
        bindings))
   (t (mv-let (tests1 bindings1)
        (match-tests-and-bindings (list 'car x) (car pat)
                                  (cons (list 'consp x) tests)
                                  bindings)
        (match-tests-and-bindings (list 'cdr x) (cdr pat)
                                  tests1 bindings1)))))

(defun match-clause (x pat forms)
  (mv-let (tests bindings)
    (match-tests-and-bindings x pat nil nil)
    (list (if (null tests)
              t
            (cons 'and (reverse tests)))
          (cons 'let (cons (reverse bindings) forms)))))

(defun match-clause-list (x clauses)
  (cond ((consp clauses)
         (if (eq (caar clauses) '&)
             (list (match-clause x (caar clauses) (cdar clauses)))
           (cons (match-clause x (caar clauses) (cdar clauses))
                 (match-clause-list x (cdr clauses)))))
        (t '((t nil)))))

(defmacro case-match (&rest args)
  (declare (xargs :guard (and (consp args)
                              (symbolp (car args))
                              (alistp (cdr args))
                              (null (cdr (member-equal (assoc '& (cdr args))
                                                       (cdr args)))))))
  (cons 'cond (match-clause-list (car args) (cdr args))))

(defmacro match (x pat)
  (list 'case-match x (list pat t)))

(defconst *t* (quote (quote t)))

(defconst *true-clause* (list *t*))

(defconst *nil* (quote (quote nil)))

(defconst *0* (quote (quote 0)))

(defconst *1* (quote (quote 1)))

(defconst *-1* (quote (quote -1)))

(defmacro strip-not (term)

; We return (mv not-flg atm), where not-flg is non-nil precisely
; when term is a negated atom, atm.  Else, not-flg is nil and atm
; is term.  We recognize two forms of negation, (NOT atm) and (IF
; atm 'NIL 'T) and indicate which was seen by using the values
; 'NOT and 'IF for the flag.

  `(let ((term ,term))
     (cond ((variablep term) (mv nil term))
           ((fquotep term) (mv nil term))
           ((eq (ffn-symb term) 'NOT) (mv 'NOT (fargn term 1)))
           ((and (eq (ffn-symb term) 'IF)
                 (equal (fargn term 2) *nil*)
                 (equal (fargn term 3) *t*))
            (mv 'IF (fargn term 1)))
           (t (mv nil term)))))

(defmacro equalityp (term)

; Note that the fquotep below is commented out.  This function
; violates our standard rules on the use of ffn-symb but is ok
; since we are looking for 'equal and not for 'quote or any
; constructor that might be hidden inside a quoted term.

  `(let ((term ,term))
     (and (nvariablep term)
;         (not (fquotep term))
          (eq (ffn-symb term) 'equal))))

(defmacro consityp (term)

; Consityp is to cons what equalityp is equal: it recognizes
; terms that are non-evg cons expressions.

  `(let ((term ,term))
     (and (nvariablep term)
          (not (fquotep term))
          (eq (ffn-symb term) 'cons))))

(defun subrp (fn)
  (and (symbolp fn)
       (member-eq fn
                  '(ACL2-NUMBERP
                    BAD-ATOM<= BINARY-* BINARY-+ UNARY--
                    UNARY-/ < CAR CDR CHAR-CODE CHARACTERP
                    CODE-CHAR COMPLEX COMPLEX-RATIONALP COERCE
                    CONS CONSP DENOMINATOR EQUAL IMAGPART INTEGERP
                    INTERN-IN-PACKAGE-OF-SYMBOL NUMERATOR RATIONALP
                    REALPART STRINGP SYMBOL-NAME SYMBOL-PACKAGE-NAME
                    SYMBOLP))))

(defun apply-subr (fn args)
  (let ((x (car args))
        (y (cadr args)))
    (case fn
      (ACL2-NUMBERP
       (mv nil (acl2-numberp x)))
      (BAD-ATOM<=
       (mv t nil))
      (BINARY-*
       (mv nil
           (* (fix x) (fix y))))
      (BINARY-+
       (mv nil
           (+ (fix x) (fix y))))
      (UNARY--
       (mv nil (- (fix x))))
      (UNARY-/
       (mv nil
           (cond ((and (acl2-numberp x) (not (equal x 0)))
                  (/ x))
                 (t 0))))
      (<
       (mv nil
           (cond ((and (rationalp x) (rationalp y))
                  (< x y))
                 (t (let ((x (fix x))
                          (y (fix y)))
                      (or (< (realpart x)
                             (realpart y))
                          (and (= (realpart x)
                                  (realpart y))
                               (< (imagpart x)
                                  (imagpart y)))))))))
      (CAR
       (mv nil
           (cond ((consp x)
                  (car x))
                 (t nil))))
      (CDR
       (mv nil
           (cond ((consp x)
                  (cdr x))
                 (t nil))))
      (CHAR-CODE
       (mv nil
           (cond ((characterp x)
                  (char-code x))
                 (t 0))))
      (CHARACTERP
       (mv nil (characterp x)))
      (CODE-CHAR
       (mv nil
           (cond ((and (integerp x) (<= 0 x) (< x 256))
                  (code-char x))
                 (t (code-char 0)))))
      (COMPLEX
       (mv nil
           (complex (if (rationalp x) x 0)
                    (if (rationalp y) y 0))))
      (COMPLEX-RATIONALP
       (mv nil (complex-rationalp x)))
      (COERCE
       (mv nil
           (cond ((equal y 'list)
                  (if (stringp x)
                      (coerce x 'list)
                    nil))
                 ((character-listp x)
                  (coerce x 'string))
                 (t (coerce (make-character-list x) 'string)))))
      (CONS
       (mv nil (cons x y)))
      (CONSP
       (mv nil (consp x)))
      (DENOMINATOR
       (mv nil
           (cond ((rationalp x)
                  (denominator x))
                 (t 1))))
      (EQUAL
       (mv nil (equal x y)))
      (IMAGPART
       (mv nil
           (cond ((complex-rationalp x)
                  (imagpart x))
                 (t 0))))
      (INTEGERP
       (mv nil (integerp x)))
      (INTERN-IN-PACKAGE-OF-SYMBOL
       (mv nil
           (cond ((and (stringp x)
                       (symbolp y))
                  (intern-in-package-of-symbol x y))
                 (t nil))))
      (NUMERATOR
       (mv nil
           (cond ((rationalp x)
                  (numerator x))
                 (t 0))))
      (RATIONALP
       (mv nil (rationalp x)))
      (REALPART
       (mv nil
           (cond ((acl2-numberp x)
                  (realpart x))
                 (t 0))))
      (STRINGP
       (mv nil (stringp x)))
      (SYMBOL-NAME
       (mv nil
           (cond ((symbolp x)
                  (symbol-name x))
                 (t ""))))
      (SYMBOL-PACKAGE-NAME
       (mv nil
           (cond ((symbolp x)
                  (symbol-package-name x))
                 (t ""))))
      (SYMBOLP
       (mv nil (symbolp x)))
      (otherwise
       (mv t nil)))))

(defun cons-term1 (fn args)

; Fn is a function and args are quoted constants.  We return a
; term equivalent to (fn . args), but we generally evaluate fn on
; args.  We handle every subrp, plus IF and NOT.

  (let ((x (cadr (car args)))
        (y (cadr (cadr args))))
    (cond ((subrp fn)
           (mv-let (erp val)
                   (apply-subr fn (list x y))
                   (cond (erp (cons fn args))
                         (t (kwote val)))))
          ((eq fn 'IF)
           (kwote (if x y (cadr (caddr args)))))
          ((eq fn 'NOT)
           (kwote (not x)))
          (t (cons fn args)))))

(defun cons-term-primitivep (fn)

; This function recognizes the function symbols that cons-term
; can compute.

  (and (symbolp fn)
       (member-eq fn '(acl2-numberp
                       binary-* binary-+ unary-- unary-/ < car cdr
                       char-code characterp code-char complex
                       complex-rationalp coerce cons consp
                       denominator equal if imagpart integerp
                       intern-in-package-of-symbol numerator
                       rationalp realpart stringp symbol-name
                       symbol-package-name symbolp not))))

(defun quote-listp (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((null l) t)
        (t (and (quotep (car l))
                (quote-listp (cdr l))))))

(defun cons-term (fn args)
  (cond ((quote-listp args)
         (cons-term1 fn args))
        (t (cons fn args))))

(defun dumb-negate-lit (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term)
         (fcons-term* 'not term))
        ((fquotep term)
         (cond ((equal term *nil*) *t*)
               (t *nil*)))
        ((eq (ffn-symb term) 'not)
         (fargn term 1))
        ((and (eq (ffn-symb term) 'equal)
              (or (equal (fargn term 2) *nil*)
                  (equal (fargn term 1) *nil*)))
         (if (equal (fargn term 2) *nil*)
             (fargn term 1)
             (fargn term 2)))
        (t (fcons-term* 'not term))))

; Substitution

; Substitution is so common that we have many different functions
; for performing it.  For example, substituting a term for
; variable (instantiation), substituting a term for term
; (replacement of equals for equals), substituting a list of
; terms for a list of variables (as in function expansion),
; applying a substitution alist to a term, etc.

; First we do substitution for variables (i.e., instantiation)
; and then the more general substitution for expressions.

; (Study this elementary function just to see how we recur
; through terms.  The function instantiates a variable, i.e.,
; (subst-var new old form w) substitutes the term new for the
; variable old in the term form.  W is the property list world
; and is used merely to keep certain terms (constants) in a
; canonical form.  For example, (subst-var '(car a) 'x '(foo x
; y)) = '(foo (car a) y).)

(mutual-recursion

(defun subst-var (new old form)
  (declare (xargs :guard (pseudo-termp form)))
  (cond ((variablep form)
         (cond ((eq form old) new)
               (t form)))
        ((fquotep form) form)
        (t (cons-term (ffn-symb form)
                      (subst-var-lst new old (fargs form))))))

(defun subst-var-lst (new old lst)
  (declare (xargs :guard (pseudo-term-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (subst-var new old (car lst))
                 (subst-var-lst new old (cdr lst))))))

)

; Now we show how to substitute one term, new, for another term,
; old, in a term.  The presumption is that new and old are known
; to be equal.  This might be used, for example, to substitute A
; for (CAR (CONS A B)) in (FOO (CAR (CONS A B))) to produce (FOO
; A).

(mutual-recursion

(defun subst-expr1 (new old term)
  (cond ((equal term old) new)
        ((variablep term) term)
        ((fquotep term) term)
        (t (cons-term (ffn-symb term)
                      (subst-expr1-lst new old (fargs term))))))

(defun subst-expr1-lst (new old lst)
  (cond ((endp lst) nil)
        (t (cons (subst-expr1 new old (car lst))
                 (subst-expr1-lst new old (cdr lst))))))


)

(defun subst-expr (new old term)

; We do not substitute for quoted constants because we do not
; want to look for such constants inside larger constants.  For
; example '#\L occurs inside of '(0 1 2) because '(0 1 2) is '(0
; 1 2 . NIL) and the symbol-name of NIL includes #\L.  So this
; function is a no-op on substitution for constants.  In
; addition, we use subst-var, which is a little faster, when
; substituting for variables.

  (cond ((variablep old) (subst-var new old term))
        ((fquotep old) old)
        (t (subst-expr1 new old term))))

; There is another substitution function below, subst-equiv-expr,
; which is like subst-expr but also reduces the new term by
; evaluating functions on newly introduced constant args.  But we
; cannot define it yet.

(mutual-recursion

(defun sublis-var (alist form)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-termp form))))

; The two following comments come from the nqthm version of this
; function and do not necessarily pertain to ACL2.

;     In REWRITE-WITH-LEMMAS we use this function with the nil
;     alist to put form into quote normal form.  Do not optimize
;     this function for the nil alist.

;     This is the only function in the theorem prover that we
;     sometimes call with a "term" that is not in quote normal
;     form.  However, even this function requires that form be at
;     least a pseudo-termp.

  (cond ((variablep form)
         (let ((a (assoc-eq form alist)))
           (cond (a (cdr a))
                 (t form))))
        ((fquotep form)
         form)
        (t (cons-term (ffn-symb form)
                      (sublis-var-lst alist (fargs form))))))

(defun sublis-var-lst (alist l)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-term-listp l))))
  (if (endp l)
      nil
    (cons (sublis-var alist (car l))
          (sublis-var-lst alist (cdr l)))))

)

(defun subcor-var1 (vars terms var)
  (declare (xargs :guard (and (true-listp vars)
                              (true-listp terms)
                              (equal (length vars) (length terms))
                              (variablep var))))
  (cond ((endp vars) var)
        ((eq var (car vars)) (car terms))
        (t (subcor-var1 (cdr vars) (cdr terms) var))))

(mutual-recursion

(defun subcor-var (vars terms form)

; "Subcor" stands for "substitute corresponding elements".  Vars
; and terms are in 1:1 correspondence and we substitute terms for
; corresponding vars into form.

  (cond ((variablep form)
         (subcor-var1 vars terms form))
        ((fquotep form) form)
        (t (cons-term (ffn-symb form)
                      (subcor-var-lst vars terms (fargs form))))))

(defun subcor-var-lst (vars terms forms)
  (cond ((endp forms) nil)
        (t (cons (subcor-var vars terms (car forms))
                 (subcor-var-lst vars terms (cdr forms))))))

)

(defun xxxjoin (fn args)
  (if (endp (cdr (cdr args)))
      (cons fn args)
    (cons fn
          (cons (car args)
                (cons (xxxjoin fn (cdr args))
                      nil)))))

(defun disjoin2 (t1 t2)

; We return a term IFF-equiv (but not EQUAL) to (OR t1 t2).  For
; example, if t1 is 'A and t2 is 'T, then we return 'T but (OR t1
; t2) is 'A.

  (cond ((equal t1 *t*) *t*)
        ((equal t2 *t*) *t*)
        ((equal t1 *nil*) t2)
        ((equal t2 *nil*) t1)
        (t (fcons-term* 'if t1 *t* t2))))

(defun disjoin (lst)
  (cond ((null lst) *nil*)
        ((null (cdr lst)) (car lst))
        (t (disjoin2 (car lst) (disjoin (cdr lst))))))

(defun conjoin2 (t1 t2)

; This function returns a term representing the logical
; conjunction of t1 and t2.  The term is IFF-equiv to (AND t1
; t2).  But, the term is not EQUAL to (AND t1 t2) because if t2
; is *t* we return t1's value, while (AND t1 t2) would return *t*
; if t1's value were non-NIL.

  (cond ((equal t1 *nil*) *nil*)
        ((equal t2 *nil*) *nil*)
        ((equal t1 *t*) t2)
        ((equal t2 *t*) t1)
        (t (fcons-term* 'if t1 t2 *nil*))))

(defun conjoin (l)
  (cond ((endp l) *t*)
        ((endp (cdr l)) (car l))
        (t (conjoin2 (car l) (conjoin (cdr l))))))

(mutual-recursion

(defun all-fnnames (term)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (union-eq (all-fnnames (lambda-body (ffn-symb term)))
                   (all-fnnames-lst (fargs term))))
        (t
         (add-to-set-eq (ffn-symb term)
                        (all-fnnames-lst (fargs term))))))

(defun all-fnnames-lst (lst)
  (cond ((endp lst) nil)
        (t (union-eq (all-fnnames (car lst))
                     (all-fnnames-lst (cdr lst))))))
)

; Here is a simple formalization of eval, the Lisp interpreter.
; Since Paco does not support state or other single-threaded
; objects and it guards are outside of the logic, the Paco's eval
; is much clearer than ACL2's ev.  The termination of Paco's eval
; is clocked, to insure termination and a relatively small clock
; max is used.

(defconst *eval-nnn* 100)

(defun pairlis (x y)
  (cond ((endp x) nil)
        (t (cons (cons (car x) (car y))
                 (pairlis (cdr x) (cdr y))))))

(mutual-recursion

(defun eval1 (term alist wrld nnn)
  (declare (xargs :measure (acl2::make-ord 1 (+ 1 (nfix nnn)) (acl2-count term))))
  (cond
   ((zp nnn) (mv t (cons :out-of-time term)))
   ((variablep term)
    (let ((temp (assoc-eq term alist)))
      (cond (temp (mv nil (cdr temp)))
            (t (mv t (cons :ubv term))))))
   ((fquotep term)
    (mv nil (cadr term)))
   ((eq (ffn-symb term) 'IF)
    (mv-let (erp test)
            (eval1 (fargn term 1) alist wrld nnn)
            (cond
             (erp (mv t test))
             (test (eval1 (fargn term 2) alist wrld nnn))
             (t    (eval1 (fargn term 3) alist wrld nnn)))))
   (t
    (mv-let (erp args)
            (eval1-lst (fargs term) alist wrld nnn)
            (cond
             (erp (mv t args))
             ((subrp (ffn-symb term))
              (apply-subr (ffn-symb term) args))
             (t (let ((bterm (body (ffn-symb term) nil wrld)))
                  (cond (bterm
                         (eval1 bterm
                                (pairlis
                                 (formals (ffn-symb term) wrld)
                                 args)
                                wrld
                                (- nnn 1)))
                        (t (mv t
                               (cons :udf
                                     (ffn-symb term))))))))))))

(defun eval1-lst (terms alist wrld nnn)
  (declare (xargs :measure (acl2::make-ord 1 (+ 1 (nfix nnn)) (acl2-count terms))))
  (cond
   ((endp terms) (mv nil nil))
   (t (mv-let
       (erp val)
       (eval1 (car terms) alist wrld nnn)
       (cond (erp (mv t val))
             (t (mv-let (erp vals)
                        (eval1-lst (cdr terms)
                                   alist wrld nnn)
                        (cond (erp (mv t vals))
                              (t (mv nil (cons val vals)))))))))))
)


(defun eval (term alist wrld)
  (eval1 term alist wrld *eval-nnn*))

#|
; Here are some tests of eval (actually eval1).
(eval1 '(binary-+ x (binary-* z y))
       '((x . 1)(z . 2) (y . 3)) (w) 10)
(eval1 '(expt '2 i) '((i . 6)) (w) 10)
(eval1 '(expt '2 i) '((i . 7)) (w) 10)
(eval1 '(binary-append x y) '((x . (1 2 3)) (y . (4 5 6))) (w) 10)
(eval1 '(binary-append x y) '((x . (1 2 3)) (y . (4 5 6))) (w) 10)
(eval1 '(length (binary-append x y))
       '((x . (1 2 3)) (y . (4 5 6))) (w) 10)

(set-w)

; Here is an example that shows we can eval1 calls of eval1

(eval1 '(eval1 '(binary-+ x x) '((x . 2)) w '10)
       (list (cons 'w (w)))
       (w)
       20)
|#

(defun apply (fn args wrld)
  (cond
   ((subrp fn) (apply-subr fn args))
   ((eq fn 'IF)
    (mv nil (if (car args) (cadr args) (caddr args))))
   (t (let ((bterm (body fn nil wrld)))
        (cond (bterm
               (eval1 bterm
                      (pairlis (formals fn wrld) args)
                      wrld
                      *eval-nnn*))
              (t (mv t (cons :udf fn))))))))

(defun legal-variable-or-constant-namep (name)

; This function checks the syntax of variable or constant name
; symbols.  In all cases, name must be a symbol that is not in
; the keyword package or in ; *common-lisp-specials-and-constants*
; (except t and nil), or in ; the main Lisp package but outside
; *common-lisp-symbols-from-main-lisp-package*, and that does not
; start with an ampersand.  The function returns 'constant,
; 'variable, or nil.

; WARNING: T and nil are legal-variable-or-constant-nameps
; because we want to allow their use as constants.

; We now allow some variables (but still no constants) from the
; main Lisp package.  See *common-lisp-specials-and-constants*.
; The following two note explains why we have been cautious here.

; Historical Note

; This package restriction prohibits using some very common names
; as variables or constants, e.g., MAX and REST.  Why do we do
; this?  The reason is that there are a few such symbols, such as
; LAMBDA-LIST-KEYWORDS, which if bound or set could cause real
; trouble.  Rather than attempt to identify all of the specials
; of CLTL that are prohibited as ACL2 variables, we just prohibit
; them all.  One might be reminded of Alexander cutting the
; Gordian Knot.  We could spend a lot of time unravelling complex
; questions about specials in CLTL or we can get on with it.
; When ACL2 prevents you from using REST as an argument, you
; should see the severed end of a once tangled rope.

; For example, akcl and lucid (and others perhaps) allow you to
; define (defun foo (boole-c2) boole-c2) but then (foo 3) causes
; an error.  Note that boole-c2 is recognized as special (by
; system::proclaimed-special-p) in lucid, but not in akcl (by
; si::specialp); in fact it's a constant in both.  Ugh.

; End of Historical Note.

  (and
   (symbolp name)
   (cond
    ((or (eq name t) (eq name nil))
     'constant)
    (t (let ((p (symbol-package-name name)))
         (and (not (equal p "KEYWORD"))
              (let ((s (symbol-name name)))
                (cond
                 ((and (not (= (length s) 0))
                       (eql (char s 0) #\*)
                       (eql (char s (1- (length s))) #\*))
                  (if (equal p *main-lisp-package-name*)
                      nil
                    'constant))
                 ((and (not (= (length s) 0))
                       (eql (char s 0) #\&))
                  nil)
                 ((equal p *main-lisp-package-name*)
                  (and
                   (not
                    (member-eq
                     name
                     *common-lisp-specials-and-constants*))
                   (member-eq
                    name
                    *common-lisp-symbols-from-main-lisp-package*)
                   'variable))
                 (t 'variable)))))))))

(defun legal-variablep (name)

; Name may be used as a variable if it has the syntax of a
; variable (see legal-variable-or-constant-namep) and does not
; have the syntax of a constant, i.e., does not start and end
; with a *.

  (eq (legal-variable-or-constant-namep name) 'variable))

(defun arglistp1 (lst)

; Every element of lst is a legal-variablep.

  (cond ((atom lst) (null lst))
        (t (and (legal-variablep (car lst))
                (arglistp1 (cdr lst))))))

(defun arglistp (lst)
  (and (arglistp1 lst)
       (no-duplicatesp-equal lst)))



(mutual-recursion

(defun termp (x wrld)
  (declare (xargs ; Matt K. change for ruler-extenders mod 2/2021
            :ruler-extenders nil))
  (cond ((atom x) (legal-variablep x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cddr x))))
        ((symbolp (car x))
         (let ((arity (arity (car x) wrld)))
           (and arity
                (true-listp (cdr x))
                (eql (length (cdr x)) arity)
                (term-listp (cdr x) wrld))))
        ((and (consp (car x))
              (true-listp (car x))
              (eq (car (car x)) 'lambda)
              (equal 3 (length (car x)))
              (arglistp (cadr (car x)))
              (termp (caddr (car x)) wrld)
              (null (set-difference-eq
                     (all-vars (caddr (car x)))
                     (cadr (car x))))
              (term-listp (cdr x) wrld)
              (equal (length (cadr (car x)))
                     (length (cdr x))))
         t)
        (t nil)))

(defun term-listp (x wrld)
  (cond ((atom x) (equal x nil))
        ((termp (car x) wrld) (term-listp (cdr x) wrld))
        (t nil)))

)

(defun fn-count-evg (evg)

; See the comment in var-fn-count for an explanation of how this
; function counts the size of evgs.

  (declare (xargs :guard t))
  (cond ((atom evg)
         (cond ((rationalp evg)
                (cond ((integerp evg)
                       (cond ((< evg 0)
                              (+ 2 (- evg)))
                             (t  (+ 1 evg))))
                      (t
                       (1+
                        (+ (fn-count-evg (numerator evg))
                           (fn-count-evg (denominator evg)))))))
               ((complex-rationalp evg)
                (1+
                 (+ (fn-count-evg (realpart evg))
                    (fn-count-evg (imagpart evg)))))
               ((symbolp evg)
                (+ 2 (* 2 (length (symbol-name evg)))))
               ((stringp evg)
                (+ 1 (* 2 (length evg))))
               (t ; (characterp evg)
                1)))
        (t (1+ (+ (fn-count-evg (cdr evg))
                  (fn-count-evg (car evg)))))))


(mutual-recursion

(defun var-fn-count (term)

; We return a triple --- the variable count, the function count,
; and the pseudo-function count --- derived from term.

; The fn count of a term is the number of function symbols in the
; unabbreviated term.  Thus, the fn count of (+ (f x) y) is 2.
; The primitives of ACL2, however, do not give very natural
; expression of the constants of the logic in pure first order
; form, i.e., as a variable-free nest of function applications.
; What, for example, is 2?  It can be written (+ 1 (+ 1 0)),
; where 1 and 0 are considered primitive constants, i.e., 1 is
; (one) and 0 is (zero).  That would make the fn count of 2 be 5.
; However, one cannot even write a pure first order term for NIL
; or any other symbol or string unless one adopts NIL and 'STRING
; as primitives too.  It is probably fair to say that the
; primitives of CLTL were not designed for the inductive
; construction of the objects in an orderly way.  But we would
; like for our accounting for a constant to somehow reflect the
; structure of the constant rather than the structure of the
; rather arbitrary CLTL term for constructing it.  'A seems to
; have relatively little to do with (intern (coerce (cons #\A
; 'NIL) 'STRING)) and it is odd that the fn count of 'A should be
; larger than that of 'STRING, and odder still that the fn count
; of "STRING" be larger than that of 'STRING since the latter is
; built from the former with intern.

; We therefore adopt a story for how the constants of ACL2 are
; actually constructed inductively and the pseudo-fn count is the
; number of symbols in that construction.  The story is as
; follows.  (z), zero, is the only primitive integer.  Positive
; integers are constructed from it by the successor function s.
; Negative integers are constructed from positive integers by
; unary minus.  Ratios are constructed by the dyadic function quo
; on an integer and a natural.  For example, -2/3 is inductively
; built as (quo (- (s(s(z)))) (s(s(s(z))))).  Complex rationals
; are similarly constructed from pairs of rationals.  All
; characters are primitive and are constructed by the function of
; the same name.  Strings are built from the empty string, (o),
; by "string-cons", cs, which adds a character to a string.  Thus
; "AB" is formally (cs (#\A) (cs (#\B) (o))).  Symbols are
; constructed by "packing" a string with p.  Conses are conses,
; as usual.  Again, this story is nowhere else relevant to ACL2;
; it just provides a consistent model for answering the question
; "how big is a constant?"

; Previously we had made no distinction between the fn-count and
; the pseudo-fn-count, but Jun Sawada ran into difficulty because
; (term-order (f) '2).  Note also that before we had (term-order
; (a (b (c (d (e (f (g (h (i x))))))))) (foo y '2/3)) but
; (term-order (foo y '1/2) (a (b (c (d (e (f (g (h (i
; x)))))))))).

  (declare (xargs :guard (pseudo-termp term)
                  :verify-guards nil))
  (cond ((variablep term)
         (mv 1 0 0))
        ((fquotep term)
         (mv 0
             0
             (fn-count-evg (cadr term))))
        (t (mv-let (v f p-f)
                   (var-fn-count-lst (fargs term))
                   (mv v (+ 1 f) p-f)))))

(defun var-fn-count-lst (lst)
  (declare (xargs :guard (pseudo-term-listp lst)))
  (cond ((endp lst)
         (mv 0 0 0))
        (t (mv-let (v1 f1 p-f1)
                   (var-fn-count (car lst))
                   (mv-let (v2 f2 p-f2)
                           (var-fn-count-lst (cdr lst))
                           (mv (+ v1 v2)
                               (+ f1 f2)
                               (+ p-f1 p-f2)))))))

)

(defun var-fn-count-hint (x)
  (if (atom x)
      nil
    (list (var-fn-count-hint (car x))
          (var-fn-count-hint (cdr x)))))

#|
; I have decided NOT to verify guards in this project.  See the
; discussion of this in the Introduction.

(defthm acl2-numberp-var-fn-count
  (and (acl2-numberp (mv-nth 0 (var-fn-count x)))
       (acl2-numberp (mv-nth 1 (var-fn-count x)))
       (acl2-numberp (mv-nth 2 (var-fn-count x)))
       (acl2-numberp (mv-nth 0 (var-fn-count-lst x)))
       (acl2-numberp (mv-nth 1 (var-fn-count-lst x)))
       (acl2-numberp (mv-nth 2 (var-fn-count-lst x))))
  :hints (("Goal" :induct (var-fn-count-hint x))))

(verify-guards var-fn-count
               :hints (("Goal" :in-theory (disable mv-nth))))
|#

; This is a special case of var-fn-count that just returns the fn
; and pseudo-fn counts.

(defun fn-count (term)
  (mv-let (var fn pfn)
          (var-fn-count term)
          (declare (ignore var))
          (mv fn pfn)))

(defun term-order (term1 term2)

; A simple -- or complete or total -- ordering is a relation
; satisfying: "antisymmetric" XrY & YrX -> X=Y, "transitive" XrY
; & Y&Z -> XrZ, and "trichotomy" XrY v YrX.  A partial order
; weakens trichotomy to "reflexive" XrX.

; Term-order is a simple ordering on terms.  (term-order term1
; term2) if and only if (a) the number of occurrences of
; variables in term1 is strictly less than the number in term2,
; or (b) the numbers of variable occurrences are equal and the
; fn-count of term1 is strictly less than that of term2, or (c)
; the numbers of variable occurrences are equal, the fn-counts
; are equal, and the pseudo-fn-count of term1 is strictly less
; than that of term2, or (d) the numbers of variable occurrences
; are equal, the fn-counts are equal, the pseudo-fn-counts are
; equal, and (lexorder term1 term2).

; Let (STRICT-TERM-ORDER X Y) be the LISP function defined as
; (AND (TERM-ORDER X Y) (NOT (EQUAL X Y))).  For a fixed, finite
; set of function symbols and variable symbols STRICT-TERM-ORDER
; is well founded, as can be proved with the following lemma.

; Lemma.  Suppose that M is a function whose range is well
; ordered by r and such that the inverse image of any member of
; the range is finite.  Suppose that L is a total order.  Define
; (LESSP x y) = (OR (r (M x) (M y)) (AND (EQUAL (M x) (M y)) (L x
; y) (NOT (EQUAL x y)))). < is a well-ordering.  Proof.  Suppose
; ... < t3 < t2 < t1 is an infinite descending sequence. ..., (M
; t3), (M t2), (M t1) is weakly descending but not infinitely
; descending and so has a least element.  WLOG assume ... = (M
; t3) = (M t2) = (M t1).  By the finiteness of the inverse image
; of (M t1), { ..., t3, t2, t1} is a finite set, which has a
; least element under L, WLOG t27.  But t28 L t27 and t28 /= t27
; by t28 < t27, contradicting the minimality of t27.  QED

; If (TERM-ORDER x y) and t2 results from replacing one
; occurrence of y with x in t1, then (TERM-ORDER t2 t1).  Cases
; on why x is less than y.  1. If the number of occurrences of
; variables in x is strictly smaller than in y, then the number
; in t2 is strictly smaller than in t1.  2. If the number of
; occurrences of variables in x is equal to the number in y but
; the fn-count of x is smaller than the fn-count of y, then the
; number of variable occurrences in t1 is equal to the number in
; t2 but the fn-count of t1 is less than the fn-count of t2.
; 3. A similar argument to the above applies if the number of
; variable occurrences and fn-counts are the same but the
; pseudo-fn-count of x is smaller than that of y.  4. If the
; number of variable occurrences and parenthesis occurrences in x
; and y are the same, then (LEXORDER x y).  (TERM-ORDER t2 t1)
; reduces to (LEXORDER t2 t1) because the number of variable and
; parenthesis occurrences in t2 and t1 are the same.  The
; lexicographic scan of t1 and t2 will be all equals until x and
; y are hit.

  (mv-let (var-count1 fn-count1 p-fn-count1)
    (var-fn-count term1)
    (mv-let (var-count2 fn-count2 p-fn-count2)
      (var-fn-count term2)
      (cond ((< var-count1 var-count2) t)
            ((> var-count1 var-count2) nil)
            ((< fn-count1 fn-count2) t)
            ((> fn-count1 fn-count2) nil)
            ((< p-fn-count1 p-fn-count2) t)
            ((> p-fn-count1 p-fn-count2) nil)
            (t (lexorder term1 term2))))))

(defun cons-term-if1 (t1 t2 t3)

; Later we define a better version of this function, named
; cons-term-if, that uses type information.

  (cond ((quotep t1)
         (if (equal t1 *nil*) t3 t2))
        ((equal t2 t3) t2)
        ((and (equal t1 t2)
              (equal t3 *nil*))
         t1)
        (t (fcons-term* 'if t1 t2 t3))))

(defun scons-term (fn args ens wrld)

; This function is (cons-term fn args) except that we evaluate
; any fn on quoted arguments and may do any other replacements
; that preserve equality (e.g., (equal x x) = t).  We return (mv
; hitp term), where hitp is t iff term is something different
; than (fn . args).

  (cond
   ((and (all-quoteps args)
         (or (flambdap fn)
             (enabled-numep
              (fn-nume :EXECUTABLE-COUNTERPART fn wrld) ens)))
    (mv-let (erp val)
            (apply fn (strip-cadrs args) wrld)
            (cond (erp (mv nil (cons-term fn args)))
                  (t
                   (<scons-term-id>
                    (mv t (kwote val)))))))
   ((and (eq fn 'equal)
         (equal (car args) (cadr args)))
    (mv t *t*))
   ((eq fn 'if)
    (let ((term1 (cons-term fn args))
          (term2 (cons-term-if1 (car args)
                                (cadr args)
                                (caddr args))))
      (mv (not (equal term1 term2)) term2)))
   (t (mv nil (cons-term fn args)))))

(mutual-recursion

(defun subst-equiv-expr1 (new old term ens wrld)

; This function substitutes new for old (which are known to be
; EQUAL) into term, producing term'.  We return (mv flg term'),
; where flg is t or nil indicating whether we changed term.

  (cond ((equal term old)
         (mv t new))
        ((or (variablep term)
             (fquotep term))
         (mv nil term))
        (t (mv-let (hitp1 args)
                   (subst-equiv-expr1-lst new old (fargs term)
                                          ens wrld)
                   (mv-let (hitp2 new-term)
                           (scons-term (ffn-symb term) args
                                       ens wrld)
                           (mv (or hitp1 hitp2)
                               new-term))))))

(defun subst-equiv-expr1-lst (new old args ens wrld)
  (cond
   ((endp args)
    (mv nil nil))
   (t (mv-let (hitp1 arg)
              (subst-equiv-expr1 new old (car args)
                                 ens wrld)
              (mv-let (hitp2 args)
                      (subst-equiv-expr1-lst new old (cdr args)
                                             ens wrld)
                      (mv (or hitp1 hitp2)
                          (cons arg args)))))))

)

(defun subst-equiv-expr (new old term ens wrld)
  (cond ((and (nvariablep old)
              (fquotep old))
         (mv nil term))
        (t (subst-equiv-expr1 new old term ens wrld))))

(mutual-recursion

(defun ffnnamep (fn term)

; We determine whether the function fn (possibly a
; lambda-expression) is used as a function in term.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (equal fn (ffn-symb term))
             (ffnnamep fn (lambda-body (ffn-symb term)))
             (ffnnamep-lst fn (fargs term))))
        ((eq (ffn-symb term) fn) t)
        (t (ffnnamep-lst fn (fargs term)))))

(defun ffnnamep-lst (fn l)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-listp l))))
  (if (endp l)
      nil
    (or (ffnnamep fn (car l))
        (ffnnamep-lst fn (cdr l)))))

)

(mutual-recursion

(defun ffnnamesp (fns term)

; We determine whether some function fn (possibly a
; lambda-expression) in fns is used as a function in term.  So
; this function is: (exists fn in fns s.t. (ffnamep fn term)).

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (member-equal (ffn-symb term) fns)
             (ffnnamesp fns (lambda-body (ffn-symb term)))
             (ffnnamesp-lst fns (fargs term))))
        ((member-eq (ffn-symb term) fns) t)
        (t (ffnnamesp-lst fns (fargs term)))))

(defun ffnnamesp-lst (fns l)
  (if (endp l)
      nil
    (or (ffnnamesp fns (car l))
        (ffnnamesp-lst fns (cdr l)))))

)

(defun flatten-ands-in-lit (term)
  (case-match
   term
   (('if t1 t2 t3)
    (cond ((equal t2 *nil*)
           (append (flatten-ands-in-lit (dumb-negate-lit t1))
                   (flatten-ands-in-lit t3)))
          ((equal t3 *nil*)
           (append (flatten-ands-in-lit t1)
                   (flatten-ands-in-lit t2)))
          (t (list term))))
   (& (cond ((equal term *t*) nil)
            (t (list term))))))

(mutual-recursion

(defun dumb-occur (x y)

; This function determines if term x occurs in term y, but does
; not look for x inside of quotes.  It is thus equivalent to
; occur if you know that x is not a quotep.

  (cond ((equal x y) t)
        ((variablep y) nil)
        ((fquotep y) nil)
        (t (dumb-occur-lst x (fargs y)))))

(defun dumb-occur-lst (x lst)
  (cond ((endp lst) nil)
        (t (or (dumb-occur x (car lst))
               (dumb-occur-lst x (cdr lst))))))

)

; ----------------------------------------------------------------
; Section:  Elementary Clause Operations

(defun complementaryp (lit1 lit2)
  (declare (xargs :guard (and (pseudo-termp lit1)
                              (pseudo-termp lit2))))

; Suppose lit1 and lit2 are terms and neither is of the form (NOT
; (NOT &)).  Then we determine whether one is the complement of
; the other, i.e., one is (NOT lit) where lit is the other.  Note
; that we do not use any commuativity knowledge.  Thus,

; WARNING: (EQUAL A B) and (NOT (EQUAL B A)) are *not*
; complementaryp, by this definition!

  (or (and (nvariablep lit1)
           (not (fquotep lit1))
           (eq (ffn-symb lit1) 'not)
           (equal (fargn lit1 1) lit2))
      (and (nvariablep lit2)
           (not (fquotep lit2))
           (eq (ffn-symb lit2) 'not)
           (equal (fargn lit2 1) lit1))))


(defun comm-equal (fn lhs rhs term)

; This function is equivalent to
; (or (equal `(,fn ,lhs ,rhs) term)
;     (equal `(,fn ,rhs ,lhs) term))

  (and (nvariablep term)
       (not (fquotep term))
       (eq fn (ffn-symb term))
       (or (and (equal lhs (fargn term 1))
                (equal rhs (fargn term 2)))
           (and (equal lhs (fargn term 2))
                (equal rhs (fargn term 1))))))

(defun member-term2 (fn lhs rhs cl)

; We determine whether either `(,fn ,lhs ,rhs) or `(,fn ,rhs
; ,lhs) is a member of cl.

; Note on Nomenclature: This is a subroutine of member-term.  It
; ought to be named member-term1, but in symmetry with
; member-complement-term, we named it member-term2.  Member-equal
; plays the role of member-term1.

  (cond ((endp cl) nil)
        ((comm-equal fn lhs rhs (car cl)) cl)
        (t (member-term2 fn lhs rhs (cdr cl)))))

(defun member-complement-term2 (fn lhs rhs cl)
  (cond ((endp cl) nil)
        ((and (nvariablep (car cl))
              (not (fquotep (car cl)))
              (eq (ffn-symb (car cl)) 'not)
              (comm-equal fn lhs rhs (fargn (car cl) 1)))
         cl)
        (t (member-complement-term2 fn lhs rhs (cdr cl)))))

(defun member-complement-term1 (lit cl)

; Lit is known not to begin with not and not to be an equality or
; iff.  This fn is equivalent to (member-equal `(not ,lit) cl).

  (cond ((endp cl) nil)
        ((and (nvariablep (car cl))
              (not (fquotep (car cl)))
              (eq (ffn-symb (car cl)) 'not)
              (equal lit (fargn (car cl) 1)))
         cl)
        (t (member-complement-term1 lit (cdr cl)))))

(mutual-recursion

(defun member-term (lit cl)

; We determine whether lit is a member-equal of cl, except that
; if the atom of lit is an equality or iff term, we also look for
; its commuted version.

  (cond ((variablep lit) (member-eq lit cl))
        ((fquotep lit) (member-equal lit cl))
        ((or (eq (ffn-symb lit) 'equal)
             (eq (ffn-symb lit) 'iff))
         (member-term2 (ffn-symb lit) (fargn lit 1) (fargn lit 2) cl))
        ((eq (ffn-symb lit) 'not)
         (member-complement-term (fargn lit 1) cl))
        (t (member-equal lit cl))))

(defun member-complement-term (lit cl)

; We determine whether the complement of lit is a member-equal of
; cl, except that if the atom of lit is an equality or iff we
; recognize its commuted version.

  (cond ((variablep lit) (member-complement-term1 lit cl))
        ((fquotep lit) (member-complement-term1 lit cl))
        ((or (eq (ffn-symb lit) 'equal)
             (eq (ffn-symb lit) 'iff))
         (member-complement-term2 (ffn-symb lit)
                                  (fargn lit 1)
                                  (fargn lit 2)
                                  cl))
        ((eq (ffn-symb lit) 'not)
         (member-term (fargn lit 1) cl))
        (t (member-complement-term1 lit cl))))

)

(defun dumb-negate-lit-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (dumb-negate-lit (car lst))
                 (dumb-negate-lit-lst (cdr lst))))))

(defun add-literal (lit cl at-end-flg)

; We add lit to clause cl, optionally at the end as per the flag.
; We assume that lit has been subjected to rewriting modulo
; iff-flg t.  Therefore, though we check lit against *t* and
; *nil* we do not do more powerful type-set reasoning.

  (cond ((quotep lit)
         (cond ((equal lit *nil*) cl)
               (t *true-clause*)))
        ((equal cl *true-clause*) *true-clause*)
        ((member-complement-term lit cl) *true-clause*)
        ((variablep lit)
         (cond ((member-term lit cl) cl)
               (at-end-flg (append cl (list lit)))
               (t (cons lit cl))))
        ((and (eq (ffn-symb lit) 'rationalp)
              (member-complement-term1
               (fcons-term 'integerp (fargs lit))
               cl))
         *true-clause*)
        ((and (eq (ffn-symb lit) 'not)
              (nvariablep (fargn lit 1))
              (not (fquotep (fargn lit 1)))
              (eq (ffn-symb (fargn lit 1)) 'integerp)
              (member-equal
               (fcons-term 'rationalp (fargs (fargn lit 1)))
               cl))
         *true-clause*)
        ((member-term lit cl) cl)
        (at-end-flg (append cl (list lit)))
        (t (cons lit cl))))

(defun add-each-literal (cl)
  (cond ((endp cl) nil)
        (t (add-literal (car cl)
                        (add-each-literal (cdr cl))
                        nil))))

(defun conjoin-clause-to-clause-set (cl cl-set)
  (cond ((member-equal *t* cl) cl-set)
        ((member-equal cl cl-set) cl-set)
        (t (cons cl cl-set))))

(defun add-each-literal-lst (cl-set)
  (cond ((endp cl-set) nil)
        (t (conjoin-clause-to-clause-set
            (add-each-literal (car cl-set))
            (add-each-literal-lst (cdr cl-set))))))

(defun conjoin-clause-sets (cl-set1 cl-set2)
  (cond ((endp cl-set1) cl-set2)
        (t (conjoin-clause-to-clause-set
            (car cl-set1)
            (conjoin-clause-sets (cdr cl-set1) cl-set2)))))


(defun some-element-member-complement-term (lst1 lst2)
  (cond ((endp lst1) nil)
        ((member-complement-term (car lst1) lst2) t)
        (t (some-element-member-complement-term (cdr lst1)
                                                lst2))))

(defun disjoin-clauses1 (cl1 cl2)

; This is equivalent to (append cl1 (set-difference-equal cl2
; cl1)) except that we add each literal with add-literal to check
; for complementary pairs, etc.

; Note: This function repeatedly adds literals from cl2 to cl1,
; at the end.  So it copies cl1's spine as many times as there
; are literals to add.  We used to use the append formulation
; above but found that complementary pairs were being missed once
; we extended the notion of complementary to include rational v
; integer.

  (cond ((endp cl2) cl1)
        (t (disjoin-clauses1 (add-literal (car cl2) cl1 t)
                             (cdr cl2)))))

(defun disjoin-clauses (cl1 cl2)
  (cond ((or (equal cl1 *true-clause*)
             (equal cl2 *true-clause*))
         *true-clause*)
        ((null cl1) cl2)
        ((null cl2) cl1)
        (t (disjoin-clauses1 cl1 cl2))))

(defun disjoin-clause-segments-to-clause (segments cl)
  (cond ((endp segments) nil)
        (t (conjoin-clause-to-clause-set
            (disjoin-clauses (car segments) cl)
            (disjoin-clause-segments-to-clause (cdr segments)
                                               cl)))))

(defun disjoin-clause-segment-to-clause-set (segment cl-set)
  (cond
   ((endp cl-set) nil)
   (t (conjoin-clause-to-clause-set
       (disjoin-clauses segment (car cl-set))
       (disjoin-clause-segment-to-clause-set segment
                                             (cdr cl-set))))))

; ----------------------------------------------------------------
; Section:  One Way Unification

(mutual-recursion

(defun one-way-unify1 (pat term alist)

; This function is a "No-Change Loser" meaning that if it fails
; and returns nil as its first result, it returns the unmodified
; alist as its second.

  (declare (xargs :measure (acl2::make-ord 1 (+ 1 (acl2-count pat)) 2)
                  :guard (and (pseudo-termp pat)
                              (pseudo-termp term)
                              (alistp alist))))
  (cond ((variablep pat)
         (let ((pair (assoc-eq pat alist)))
           (cond (pair (cond ((equal (cdr pair) term)
                              (mv t alist))
                             (t (mv nil alist))))
                 (t (mv t (cons (cons pat term) alist))))))
        ((fquotep pat)
         (cond ((equal pat term) (mv t alist))
               (t (mv nil alist))))
        ((variablep term) (mv nil alist))
        ((fquotep term)

; We can unify some patterns with constants.  For example,
; (binary-+ '1 x) can be unified with '7 by binding x to '6.

         (cond
          ((acl2-numberp (cadr term))
           (let ((ffn-symb (ffn-symb pat)))
             (case ffn-symb
               (binary-+
                (cond ((quotep (fargn pat 1))
                       (one-way-unify1
                        (fargn pat 2)
                        (kwote (- (cadr term)
                                  (fix (cadr (fargn pat 1)))))
                        alist))
                      ((quotep (fargn pat 2))
                       (one-way-unify1
                        (fargn pat 1)
                        (kwote (- (cadr term)
                                  (fix (cadr (fargn pat 2)))))
                        alist))
                      (t (mv nil alist))))
               (binary-*
                (cond ((and (quotep (fargn pat 1))
                            (integerp (cadr (fargn pat 1)))
                            (> (abs (cadr (fargn pat 1))) 1))
                       (one-way-unify1
                        (fargn pat 2)
                        (kwote (/ (cadr term)
                                  (cadr (fargn pat 1))))
                        alist))
                      ((and (quotep (fargn pat 2))
                            (integerp (cadr (fargn pat 2)))
                            (> (abs (cadr (fargn pat 2))) 1))
                       (one-way-unify1
                        (fargn pat 1)
                        (kwote (/ (cadr term)
                                  (cadr (fargn pat 2))))
                        alist))
                      (t (mv nil alist))))

; We once were willing to unify (- x) with 3 by binding x to -3.
; John Cowles' experience with developing ACL2 arithmetic led him
; to suggest that we not unify (- x) with any constant other than
; negative ones.  Similarly, we do not unify (/ x) with any
; constant other than those between -1 and 1.  The code below
; reflects these suggestions.

               (unary--
                (cond ((>= (+ (realpart (cadr term))
                              (imagpart (cadr term)))
                           0)
                       (mv nil alist))
                      (t (one-way-unify1 (fargn pat 1)
                                         (kwote (- (cadr term)))
                                         alist))))
               (unary-/
                (cond ((or (>= (* (cadr term)
                                  (conjugate (cadr term)))
                               1)
                           (eql 0 (cadr term)))
                       (mv nil alist))
                      (t (one-way-unify1 (fargn pat 1)
                                         (kwote
                                          (/ (cadr term)))
                                         alist))))
               (otherwise (mv nil alist)))))

          ((symbolp (cadr term))
           (cond
            ((eq (ffn-symb pat) 'intern-in-package-of-symbol)
             (let ((pkg (symbol-package-name (cadr term)))
                   (name (symbol-name (cadr term))))
               (mv-let
                (ans alist1)

; We are careful with alist to keep this a no change loser.

                (one-way-unify1 (fargn pat 1) (kwote name) alist)
                (cond
                 (ans

; We are unifying 'pkg::name with (intern-in-package-of-symbol x
; y) where x is now unified with "name".  So when is
; (intern-in-package-of-symbol "name" y) equal to pkg::name?  It
; would suffice to unify y with any symbol in pkg.  It might be
; that y is already such a quoted symbol.  Or perhaps we could
; unify y with pkg::name, which is one symbol we know is in pkg.
; But note that it is not necessary that y unify with a symbol in
; pkg.  It would suffice, for example, if y could be unified with
; a symbol in some other package, say gkp, with the property that
; pkg::name was imported into gkp, for then gkp::name would be
; pkg::name.  Thus, as is to be expected by all failed
; unifications, failure does not mean there is no instance that
; is equal to the term.  Suppose that y is not a quoted symbol
; and is not a variable (which could therefore be unified with
; pkg::name).  What else might unify with "any symbol in pkg?"
; At first sight one might think that if y were
; (intern-in-package-of-symbol z 'pkg::name2) then the result is
; a symbol in pkg no matter what z is.  (The idea is that one
; might think that (intern-in-package-of-symbol z 'pkg::name2) is
; "the" generic expression of "any symbol in pkg.")  But that is
; not true because for certain z it is possible that the result
; isn't in pkg.  Consider, for example, the possibility that
; gkp::zzz is imported into pkg so that if z is "ZZZ" the result
; is a symbol in gkp not pkg.

                  (cond
                   ((and (nvariablep (fargn pat 2))
                         (fquotep (fargn pat 2)))
                    (cond
                     ((not (symbolp (cadr (fargn pat 2))))

; (intern-in-package-of-symbol x y) is NIL if y is not a symbol.
; So we win if term is 'nil and lose otherwise.  If we win, note
; that x is unified (unnecessarily) with "NIL" in alist1 and so
; we report the win with alist!  If we lose, we have to report
; alist to be a no change loser.  So its alist either way.

                      (mv (if (equal term *nil*) t nil)
                          alist))
                     (t (if (equal pkg
                                   (symbol-package-name
                                    (cadr (fargn pat 2))))
                            (mv t alist1)
                          (mv nil alist)))))
                   (t
                    (mv-let (ans alist2)
                            (one-way-unify1 (fargn pat 2)
                                            term alist1)
                            (cond (ans (mv t alist2))
                                  (t (mv nil alist)))))))
                 (t (mv nil alist))))))
            (t (mv nil alist))))
          ((stringp (cadr term))
           (cond ((and (eq (ffn-symb pat) 'coerce)
                       (equal (fargn pat 2) ''string))
                  (one-way-unify1 (fargn pat 1)
                                  (kwote (coerce (cadr term)
                                                 'list))
                                  alist))
                 (t (mv nil alist))))
          ((consp (cadr term))
           (cond ((eq (ffn-symb pat) 'cons)

; We have to be careful with alist below so we are a no change
; loser.

                  (mv-let
                   (ans alist1)
                   (one-way-unify1 (fargn pat 1)
                                   (kwote
                                    (car (cadr term)))
                                   alist)

                   (cond
                    (ans
                     (mv-let
                      (ans alist2)
                      (one-way-unify1 (fargn pat 2)
                                      (kwote (cdr (cadr term)))
                                      alist1)
                      (cond (ans (mv t alist2))
                            (t (mv nil alist)))))
                    (t (mv nil alist)))))
                 (t (mv nil alist))))
          (t (mv nil alist))))
        ((cond ((flambda-applicationp pat)
                (equal (ffn-symb pat) (ffn-symb term)))
               (t
                (eq (ffn-symb pat) (ffn-symb term))))
         (cond ((eq (ffn-symb pat) 'equal)
                (one-way-unify1-equal
                 (fargn pat 1)  (fargn pat 2)
                 (fargn term 1) (fargn term 2)
                 alist))
               (t (mv-let (ans alist1)
                          (one-way-unify1-lst (fargs pat)
                                              (fargs term)
                                              alist)
                          (cond (ans (mv t alist1))
                                (t (mv nil alist)))))))
        (t (mv nil alist))))

(defun one-way-unify1-lst (pl tl alist)

; This function is NOT a No Change Loser.  That is, it may return
; nil as its first result, indicating that no substitution
; exists, but return as its second result an alist different from
; its input alist.

  (declare (xargs :measure (acl2::make-ord 1 (+ 1 (acl2-count pl)) 2)
                  :guard (and (pseudo-term-listp pl)
                              (pseudo-term-listp tl)
                              (alistp alist))))
  (cond ((endp pl) (mv t alist))
        (t (mv-let (ans alist)
             (one-way-unify1 (car pl) (car tl) alist)
             (cond
              (ans
               (one-way-unify1-lst (cdr pl) (cdr tl) alist))
              (t (mv nil alist)))))))

(defun one-way-unify1-equal1 (pat1 pat2 term1 term2 alist)

; At first glance, the following code looks more elaborate than
; necessary.  But this function is supposed to be a No Change
; Loser.  The first time we coded this we failed to ensure that
; property.  The bug is the result of fuzzy thinking in the
; vicinity of conjunctive subgoals.  Suppose success requires
; success on x and success on y.  The naive way to code it is
; (mv-let (ans nochanger) x (if ans y (mv nil nochanger))), i.e.,
; to solve the x problem and if you win, return your solution to
; the y problem.  But if x wins it will have changed nochanger.
; If y then loses, it returns the changed nochanger produced by
; x.  Clearly, if x might win and change things but ultimate
; success also depends on y, you must preserve the original
; inputs and explicitly revert to them if y loses.

  (declare (xargs :measure (acl2::make-ord 1 (+ 2 (acl2-count pat1)
                                          (acl2-count pat2))
                                 0)
                  :guard (and (pseudo-termp pat1)
                              (pseudo-termp pat2)
                              (pseudo-termp term1)
                              (pseudo-termp term2)
                              (alistp alist))))
  (mv-let (ans alist1)
    (one-way-unify1 pat1 term1 alist)
    (cond (ans
           (mv-let (ans alist2)
                   (one-way-unify1 pat2 term2 alist1)
                   (cond (ans (mv t alist2))
                         (t (mv nil alist)))))
          (t (mv nil alist)))))

(defun one-way-unify1-equal (pat1 pat2 term1 term2 alist)
  (declare (xargs :measure (acl2::make-ord 1 (+ 2 (acl2-count pat1)
                                          (acl2-count pat2))
                                     1)
                  :guard (and (pseudo-termp pat1)
                              (pseudo-termp pat2)
                              (pseudo-termp term1)
                              (pseudo-termp term2)
                              (alistp alist))))
  (mv-let (ans alist)
    (one-way-unify1-equal1 pat1 pat2 term1 term2 alist)
    (cond
     (ans (mv t alist))
     (t (one-way-unify1-equal1 pat2 pat1 term1 term2 alist)))))
)

; Note: I do not verify the guards on one-way-unify1.  It
; requires proving that the second result is an alist, which
; requires an induction the way the whole nest recurs.  I don't
; want to define the necessary hint.

(defun one-way-unify (pat term)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term))))

; This function returns two values.  The first is 'T, or 'NIL,
; according to whether unification succeeded.  The second value
; returned is a symbol alist that when substituted into pat will
; produce term, when the unification succeeded.

; The use of the phrase ``unify'' here is somewhat opaque but is
; historically justified by its usage in nqthm.  Really, all we
; are doing is matching because we do not treat the ``variable
; symbols'' in term as instantiable.

; Note that the fact that this function returns nil should not be
; taken as a sign that no substition makes pat equal to term in
; the current theory.  For example, we fail to unify (+ x x) with
; '2 even though '((x . 1)) does the job.

  (one-way-unify1 pat term nil))

; This function determines whether term uses vars not bound in
; alist.

(mutual-recursion

(defun free-varsp (term alist)
  (cond ((variablep term) (not (assoc-eq term alist)))
        ((fquotep term) nil)
        (t (free-varsp-lst (fargs term) alist))))

(defun free-varsp-lst (args alist)
  (cond ((endp args) nil)
        (t (or (free-varsp (car args) alist)
               (free-varsp-lst (cdr args) alist)))))

)


; ----------------------------------------------------------------
; Section:  Worse-Than - a Heuristic Ordering on Terms

(defun member-char-stringp (chr str i)
  (cond ((zp i) (eql chr (char str 0)))
        (t (or (eql chr (char str i))
               (member-char-stringp chr str (1- i))))))

(defun terminal-substringp1 (str1 str2 max1 max2)
  (cond ((zp max1) (eql (char str1 max1) (char str2 max2)))
        ((eql (char str1 max1) (char str2 max2))
         (terminal-substringp1 str1 str2 (1- max1) (1- max2)))
        (t nil)))

(defun terminal-substringp (str1 str2 max1 max2)
  (cond ((< max2 max1) nil)
        (t (terminal-substringp1 str1 str2 max1 max2))))

(defun evg-occur (x y)

; Consider the idealized inductive construction of the ACL2
; objects x and y as described in the comment for var-fn-count.
; Imagine that x and y are so represented.  Then this function
; answers the question: "Does x occur in y?"

  (cond
   ((atom y)
    (cond
     ((characterp y) (and (characterp x) (eql x y)))
     ((stringp y)
      (cond ((characterp x)
             (member-char-stringp x y (1- (length y))))
            ((stringp x)
             (terminal-substringp x y
                                  (1- (length x))
                                  (1- (length y))))
            (t nil)))
     ((symbolp y)
      (cond ((characterp x)
             (let ((sny (symbol-name y)))
               (member-char-stringp x sny (1- (length sny)))))
            ((stringp x)
             (let ((sny (symbol-name y)))
               (terminal-substringp x sny
                                    (1- (length x))
                                    (1- (length sny)))))
            ((symbolp x) (eq x y))
            (t nil)))
     ((integerp y)
      (and (integerp x)
           (or (int= x y)
               (and (<= 0 x)
                    (<= x (if (< y 0) (- y) y))))))
     ((rationalp y)

; We know y is a non-integer rational.  X occurs in it either
; because x is the same non-integer rational or x is an integer
; that occurs in the numerator or denominator.

      (cond ((integerp x)
             (or (evg-occur x (numerator y))
                 (evg-occur x (denominator y))))
            ((rationalp x) (= x y))
            (t nil)))
     ((complex-rationalp y)

; We know y is a complex rational.  X occurs in it either because
; x is the same complex rational or x is a rational that occurs in
; the real or imaginary part.

      (cond ((rationalp x)
             (or (evg-occur x (realpart y))
                 (evg-occur x (imagpart y))))
            ((complex-rationalp x) (= x y))
            (t nil)))
     (t (equal x y))))
   (t (or (evg-occur x (car y))
          (evg-occur x (cdr y))))))

(mutual-recursion

(defun occur (term1 term2)
  (cond ((variablep term2)
         (eq term1 term2))
        ((fquotep term2)
         (cond ((quotep term1)
                (evg-occur (cadr term1) (cadr term2)))
               (t nil)))
        ((equal term1 term2) t)
        (t (occur-lst term1 (fargs term2)))))

(defun occur-lst (term1 args2)
  (cond ((endp args2) nil)
        (t (or (occur term1 (car args2))
               (occur-lst term1 (cdr args2))))))
)

; Rockwell Addition: I found an exponential explosion in
; worse-than and it is fixed here.

; Up through Version 2.5 worse-than was defined as shown below:

; (defun worse-than (term1 term2)
;   (cond ((quick-worse-than term1 term2) t)
;         ((variablep term1) nil)
;         ((fquotep term1) nil)
;         (t (worse-than-lst (fargs term1) term2))))

; But we discovered via Rockwell examples that this performs
; terribly if term1 and term2 are variants of each other, i.e.,
; the same up to the variables used.  So we have implemented a
; short circuit.

(mutual-recursion

(defun pseudo-variantp (term1 term2)

; We determine whether term1 and term2 are identical up to the
; variables used, down to the variables in term1.

; If (pseudo-variantp term1 term2) is true then we know that
; (worse-than term1 term2) is nil.

; Note: In the theorem proving literature, the word ``variant''
; is used to mean that the two terms are identical up to a
; renaming of variables.  That is checked by our function
; variantp.  This function is different and of little logical
; use.  It does not insist that a consistent renaming of variable
; occur, just that the two terms are isomorphic down to the
; variable symbols.  It is here to avoid a very bad case in the
; worse-than check.

  (cond ((variablep term1)

; Suppose that term1 is a variable.  The only thing that it can
; be worse than is a quote.  That is, if we return t, then we
; must ensure that either term2 is term1 or (worse-than term1
; term2) is nil.  The worse-than will be nil unless term2 is a
; quote.  See the exponential sequences below.

         (not (quotep term2)))

        ((fquotep term1) (equal term1 term2))
        ((or (variablep term2)
             (fquotep term2))
         nil)
        (t (and (equal (ffn-symb term1) (ffn-symb term2))
                (pseudo-variantp-list (fargs term1)
                                      (fargs term2))))))

(defun pseudo-variantp-list (args1 args2)
  (cond ((endp args1) t)
        (t (and (pseudo-variantp (car args1) (car args2))
                (pseudo-variantp-list (cdr args1)
                                      (cdr args2)))))))

; It turns out that without the use of pseudo-variantp in the
; definition of worse-than, below, worse-than's cost grows
; exponentially on pseudo-variant terms.  Consider the sequence
; of terms (f a a), (f a (f a a)), ..., and the corresponding
; sequence with variable symbol b used in place of a.  Call these
; terms a1, a2, ..., and b1, b2, ...  Then if pseudo-variantp
; were redefined to return nil, here are the real times taken to
; do (worse-than a1 b1), (worse-than a2 b2), ...  0.000, 0.000,
; 0.000, 0.000, 0.000, 0.000, 0.000, 0.020, 0.080, 0.300, 1.110,
; 4.230, 16.390.  This was measured on a 330 MHz Pentium II.

#|
(progn
  (time
   (new-worse-than
    '(f a a)
    '(f b b)))

  (time
   (new-worse-than
    '(f a (f a a))
    '(f b (f b b))))

  (time
   (new-worse-than
    '(f a (f a (f a a)))
    '(f b (f b (f b b)))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a a))))
    '(f b (f b (f b (f b b))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a a)))))
    '(f b (f b (f b (f b (f b b)))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a a))))))
    '(f b (f b (f b (f b (f b (f b b))))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a a)))))))
    '(f b (f b (f b (f b (f b (f b (f b b)))))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a a))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b b))))))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a))))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))

  (time
   (new-worse-than
    '(f a
        (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a))))))))))))
    '(f b
        (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))

  (time
   (new-worse-than
    '(f a
        (f a
           (f a
              (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))))
    '(f b
        (f b
           (f b
              (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
    ))
  )
|#

; If pseudo-variantp is defined so that instead of (not (quotep
; term2)) it insists of (variablep term2) when (variablep term1),
; then the following sequence goes exponential even though the
; preceding one does not.

#|
(progn
  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))
    ))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
    ))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))
    ))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))
    ))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))))
    ))

  (time
   (new-worse-than
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))))
    ))
  )
|#
; with times of 0.000, 0.120, 0.250, 0.430, etc.  But with the
; current definition of pseudo-variantp, the sequence above is
; flat.

; However, the sequence with the terms commuted grows
; exponentially, still.

#|
(progn
  (time
   (new-worse-than
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

  (time
   (new-worse-than
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

  (time
   (new-worse-than
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

  (time
   (new-worse-than
    '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    ))

  (time
   (new-worse-than
    '(f b
        (f b
           (f b
              (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    ))

  (time
   (new-worse-than
    '(f b
        (f b
           (f b
              (f b
                 (f b
                    (f b
                       (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    ))

  (time
   (new-worse-than
    '(f b
        (f b
           (f b
              (f b
                 (f b
                    (f b
                       (f b
                          (f b
                             (f b
                                (f b (f b (f b (f b (f b (f b b)))))))))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    ))

  (time
   (new-worse-than
    '(f b
        (f b
           (f b
              (f b
                 (f b
                    (f b
                       (f b
                          (f b
                             (f b
                                (f b
                                   (f b
                                      (f b
                                         (f b (f b (f b (f b b))))))))))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    ))

  (time
   (new-worse-than
    '(f b
        (f b
           (f b
              (f b
                 (f b
                    (f b
                       (f b
                          (f b
                             (f b
                                (f b
                                   (f b
                                      (f b
                                         (f b
                                            (f b
                                               (f b
                                                  (f b
                                                     (f b b)))))))))))))))))
    '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
    ))
  )
|#

; Real times: 0.000, 0.000, 0.010, 0.000, 0.010, 0.020, 0.040,
; 0.100, 0.210, ...

(mutual-recursion

(defun worse-than (term1 term2)

  (declare (xargs :measure (acl2::make-ord 1
                                           (+ 1
                                              (acl2-count term1)
                                              (acl2-count term2))
                                           2)))

; Term1 is worse-than term2 if it is basic-worse-than term2 or
; some proper subterm of it is worse-than or equal to term2.
; However, we know that if two terms are pseudo-variants of
; eachother, then the worse-than relation does not hold.

  (cond ((basic-worse-than term1 term2) t)
        ((pseudo-variantp term1 term2) nil)
        ((variablep term1)

; If term1 is a variable and not basic-worse-than term2, what do
; we know about term2?  Term2 might be a variable.  Term2 cannot
; be quote.  Term2 might be a function application.  So is X
; worse-than X or Y or (F X Y)?  No.

         nil)
        ((fquotep term1)

; If term1 is a quote and not basic-worse-than term2, what do we
; know about term2?  Term2 might be a variable.  Also, term2
; might be a quote, but if it is, term2 is bigger than term1.
; Term2 might be a function application.  So is term1 worse-than
; a bigger quote?  No.  Is term1 worse-than a variable or
; function application?  No.

         nil)

        (t (worse-than-lst (fargs term1) term2))))

(defun basic-worse-than-lst1 (args1 args2)

  (declare (xargs :measure (acl2::make-ord 1
                                           (+ 1
                                              (acl2-count args1)
                                              (acl2-count args2))
                                           1)))

; Is some element of args2 ``uglier'' than the corresponding
; element of args1.  Technically, a2 is uglier than a1 if a1 is
; atomic (a variable or constant) and a2 is not or a2 is
; worse-than a1.

  (cond ((endp args1) nil)
        ((or (and (or (variablep (car args1))
                      (fquotep (car args1)))
                  (not (or (variablep (car args2))
                           (fquotep (car args2)))))
             (worse-than (car args2) (car args1)))
         t)
        (t (basic-worse-than-lst1 (cdr args1) (cdr args2)))))

(defun basic-worse-than-lst2 (args1 args2)

  (declare (xargs :measure (acl2::make-ord 1
                                           (+ 1
                                              (acl2-count args1)
                                              (acl2-count args2))
                                           1)))

; Is some element of arg1 worse-than the corresponding element of
; args2?

  (cond ((endp args1) nil)
        ((worse-than (car args1) (car args2)) t)
        (t (basic-worse-than-lst2 (cdr args1) (cdr args2)))))

(defun basic-worse-than (term1 term2)

  (declare (xargs :measure (acl2::make-ord 1
                                           (+ 1
                                              (acl2-count term1)
                                              (acl2-count term2))
                                           1)))

; We say that term1 is basic-worse-than term2 if
; * term2 is a variable and term1 properly contains it, e.g.,
;   (F A B) is basic-worse-than A;
; * term2 is a quote and term1 is either not a quote or is a
;   bigger quote, e.g., both X and '124 are basic-worse-than
;   '17 and '(A B C D E) is worse than 'X; or

; * term1 and term2 are applications of the same function and
;   no argument of term2 is uglier than the corresponding arg
;   of term1, and some argument of term1 is worse-than the
;   corresponding arg of term2.

; The last case is illustrated by the fact that (F A B) is
; basic-worse-than (F A '17), because B is worse than '17, but (F
; '17 B) is not basic-worse-than (F A '17) because A is worse
; than '17.  Think of term2 as the old goal and term1 as the new
; goal.  Do we want to cut off backchaining?  Yes, if term1 is
; basic-worse-than term2.  So would we backchain from (F A '17)
; to (F '17 B)?  Yes, because even though one argument (the
; second) got worse (it went from 17 to B) another argument (the
; first) got better (it went from A to 17).

  (cond ((variablep term2)
         (cond ((eq term1 term2) nil)
               (t (occur term2 term1))))
        ((fquotep term2)
         (cond ((variablep term1) t)
               ((fquotep term1)
                (> (fn-count-evg (cadr term1))
                   (fn-count-evg (cadr term2))))
               (t t)))
        ((variablep term1) nil)
        ((fquotep term1) nil)
        ((cond ((flambda-applicationp term1)
                (equal (ffn-symb term1) (ffn-symb term2)))
               (t (eq (ffn-symb term1) (ffn-symb term2))))
         (cond ((pseudo-variantp term1 term2) nil)
               ((basic-worse-than-lst1 (fargs term1)
                                       (fargs term2)) nil)
               (t (basic-worse-than-lst2 (fargs term1)
                                         (fargs term2)))))
        (t nil)))

(defun some-subterm-worse-than-or-equal (term1 term2)

; Returns t if some subterm of term1 is worse-than or equal to
; term2.

  (declare (xargs :measure (acl2::make-ord 1
                                           (+ 1
                                              (acl2-count term1)
                                              (acl2-count term2))
                                           2)))

  (cond
   ((variablep term1) (eq term1 term2))
   ((if (pseudo-variantp term1 term2) ; see worse-than-or-equal
        (equal term1 term2)
      (basic-worse-than term1 term2))
    t)
   ((fquotep term1) nil)
   (t (some-subterm-worse-than-or-equal-lst (fargs term1)
                                            term2))))

(defun some-subterm-worse-than-or-equal-lst (args term2)

  (declare (xargs :measure (acl2::make-ord 1
                                           (+ 1
                                              (acl2-count args)
                                              (acl2-count term2))
                                           2)))
  (cond
   ((endp args) nil)
   (t (or (some-subterm-worse-than-or-equal (car args)
                                            term2)
          (some-subterm-worse-than-or-equal-lst (cdr args)
                                                term2)))))

(defun worse-than-lst (args term2)

; We determine whether some element of args contains a subterm
; that is worse-than or equal to term2.  The subterm in question
; may be the element of args itself.  That is, we use ``subterm''
; in the ``not necessarily proper subterm'' sense.

  (declare (xargs :measure (acl2::make-ord 1
                                           (+ 1
                                              (acl2-count args)
                                              (acl2-count term2))
                                           2)))
  (cond ((endp args) nil)
        (t (or (some-subterm-worse-than-or-equal (car args) term2)
               (worse-than-lst (cdr args) term2)))))

)

(defun worse-than-or-equal (term1 term2)

; This function is not really mutually recursive and could be
; removed from this nest.  It determines whether term1 is term2
; or worse than term2.  This nest defines worse-than and does not
; use this function despite the use of similarly named functions.

; Note: This function is supposed to be equivalent to (or (equal
; term1 term2) (worse-than term1 term2)).

; Clearly, that is equivalent to

; (if (pseudo-variantp term1 term2)
;     (or (equal term1 term2) (worse-than term1 term2))
;     (or (equal term1 term2) (worse-than term1 term2)))

; But if pseudo-variantp is true, then worse-than must return
; nil.  And if pseudo-variantp is nil, then the equal returns
; nil.  So we can simplify the if above to:

  (if (pseudo-variantp term1 term2)
      (equal term1 term2)
    (worse-than term1 term2)))

; ----------------------------------------------------------------
; Section:  Generating New Variables

; This section defines the function genvar, which is used to
; generate new variable symbols.  The book contains three
; relevant definitions, those of gsym, genvar1 and genvar.  Their
; informal specs are as follows:

; (gsym pkg-witness char-lst cnt)
;   basic routine for creating a symbol (interned in a given
;   package) whose name is the concatenatin of char-lst and the
;   printed form of cnt.
;   Example:
;   (gsym 'paco::rewrite '(#\A #\B #\C) 23) = PACO::ABC23.
;   Henceforth my examples assume we're in the "PACO" package.

; (genvar1 pkg-witness char-lst avoid-lst cnt)
;   repeatedly uses gsym with increasing cnts to create symbols
;   until it finds one not in avoid-lst.
;   Example:
;   (genvar1 'rewrite '(#\A #\B #\C) '(ABC0 ABC2 ABC1) 0) = ABC3

; (genvar pkg-witness prefix-string n avoid-lst)
;   create a legal variable symbol not in avoid-lst.
;   Examples:
;   (genvar 'rewrite "ABC" nil '(ABC0 ABC1))     = ABC
;   (genvar 'rewrite "ABC" nil '(ABC ABC0 ABC1)) = ABC2
;   (genvar 'rewrite "ABC" 0   '(ABC0 ABC1))     = ABC2

; There are some fairly interesting problems associated with
; these functions.  First, the admission of genvar1 is a little
; problematic because it depends on the fact that eventually
; we'll find a cnt that makes a gsym'd symbol that doesn't occur
; in avoid-lst.  But that relies on the fact that two gsym'd
; symbols are the same iff their cnts are the same.  We have to
; prove this before we can admit genvar1 and we have to devise a
; measure that then explains genvar1.

; The second problem is that we want to guarantee that genvar
; produces legal variable symbols that don't occur in avoid-lst.
; The latter is easy once we have genvar1.  But genvar1 may
; produce illegal variable names.  For example, (genvar1 'EQUAL
; '(#\P #\R #\I #\N) '(COMMON-LISP::PRIN COMMON-LISP::PRIN0) 0)
; =
; COMMON-LISP::PRIN1
; which is not a legal-variablep.  The problem is that
; PACO::EQUAL is imported from COMMON-LISP, so the generated
; symbols are interned there and some COMMON-LISP symbols are not
; legal variables.  You cannot avoid this problem by
; discriminating against pkg-witnesses in the "COMMON-LISP"
; package.  It could be that PACO::REWRITE, which witnesses the
; package "PACO," could still cause you to intern the symbol in
; COMMON-LISP, if the name you generate is that of a COMMON-LISP
; symbol imported into "PACO".  For example,

; (genvar1 'REWRITE '(#\L #\O #\G #\O #\R #\C) '(PACO::LOGORC0) 0)
; = COMMON-LISP::LOGORC1

; (This happens to be a legal variable, despite the fact that it
; is in the COMMON-LISP package.)  While we could analyze the
; particular imports of "PACO" versus the illegal variable names,
; we cannot predict what future packages might be defined and
; they too must work with this function.

; For example:

; (defpkg "NEW" '(COMMON-LISP::PRIN1))
; (legal-variablep (genvar1 'NEW::MYSYMBOL '(#\P #\R #\I #\N )
;                 '(NEW::PRIN0) 0))
;  = NIL!

; because the symbol generated is COMMON-LISP::PRIN1 which
; happens to be in the list of Common Lisp specials.

; So genvar uses genvar1 to generate a ``good guess'' and if that
; symbol is legal, it is the answer.  Otherwise, genvar ignores
; the supplied package and prefix and uses genvar1 again to
; produce a name that is guaranteed to be legal.  To prove this
; requires a substantial amount of analysis of legal-variablep
; and the symbols imported into various packages.

(defun gsym (pkg-witness char-lst cnt)
  (intern-in-package-of-symbol
   (coerce
    (append char-lst
            (explode-nonnegative-integer cnt nil))
    'string)
   pkg-witness))

; (acl2::set-match-free-error nil)

; We're headed for the theorem that gsyms are unique if their
; cnts are unique.

(encapsulate
 nil
 (local
  (defthm lemma-1
    (IMPLIES
     (AND (STRINGP STR1)
          (STRINGP STR2)
          (SYMBOLP PKG)
          (EQUAL (symbol-name
                  (INTERN-IN-PACKAGE-OF-SYMBOL STR1 PKG))
                 (symbol-name
                  (INTERN-IN-PACKAGE-OF-SYMBOL STR2 PKG))))
     (EQUAL STR1 STR2))
    :rule-classes nil))

 (defthm interns-unique
   (implies (and (stringp str1)
                 (stringp str2)
                 (symbolp pkg))
            (iff (equal (intern-in-package-of-symbol str1 pkg)
                        (intern-in-package-of-symbol str2 pkg))
                 (equal str1 str2)))
   :hints (("Subgoal 1" :use lemma-1))))

(defthm character-listp-transfer
  (equal (character-listp x)
         (acl2::character-listp x)))

(encapsulate
 nil

 (local
  (defthm lemma-1
    (implies (and (character-listp x)
                  (character-listp y)
                  (equal (coerce (coerce x 'string) 'list)
                         (coerce (coerce y 'string) 'list)))
             (equal x y))
    :rule-classes nil))

 (defthm coerce-string-unique
   (implies (and (character-listp x)
                 (character-listp y))
            (iff (equal (coerce x 'string) (coerce y 'string))
                 (equal x y)))
   :hints (("Subgoal 1" :use lemma-1))))

(defthm character-listp-explode-nonnegative-integer
  (implies (acl2::character-listp a)
           (acl2::character-listp
            (explode-nonnegative-integer n a))))

(defthm character-listp-append
  (implies (acl2::character-listp a)
           (equal (acl2::character-listp (append a b))
                  (acl2::character-listp b))))

; So here is our first major lemma!

(defthm gsym-unique
  (implies (and (character-listp root)
                (symbolp pkg))
           (iff (equal (gsym pkg root i)
                       (gsym pkg root j))
                (equal (nfix i) (nfix j)))))

(in-theory (disable gsym))

; Next, we'll introduce genvar1.  But we have to come up with a
; measure that explains its iteration through higher and higher
; cnts.  Below is a function that collects all the symbols
; genvar1 has tried so far.  Genvar1 could keep track of this
; list but has no need for it (except to explain why it
; terminates).  Hence the name ``ghostvar''.

(defun genvar1-ghostvar (pkg-witness char-lst cnt)
  (cond ((zp cnt) nil)
        (t (cons (gsym pkg-witness char-lst (- cnt 1))
                 (genvar1-ghostvar pkg-witness
                                   char-lst
                                   (- cnt 1))))))

; Basically, the number of candidates ruled out avoid-lst will
; decrease every time we recur in genvar1.  Here is the function
; that counts the number of still-possibly-viable candidates.

(defun count-non-members (lst1 lst2)
; We count the number of elements of lst2 that are not in lst1.
  (cond ((endp lst2) 0)
        ((member (car lst2) lst1)
         (count-non-members lst1 (cdr lst2)))
        (t (+ 1 (count-non-members lst1 (cdr lst2))))))

; In key-count-non-members-property you'll see the key property
; of this function.

(defthm -1+1 (equal (+ -1 +1 x) (fix x)))

; Observe that if the ghostvar could contain duplications, we'd
; be hosed.  But it doesn't contain duplications, because of the
; key property proved about gsym.

(defthm not-member-equal-gsym
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= i j)
                (character-listp root)
                (symbolp pkg))
           (not (member-equal (gsym pkg root j)
                              (genvar1-ghostvar pkg root i)))))

(defthm no-duplicates-equal-genvar1-ghostvar
  (implies (and (character-listp root)
                (symbolp pkg))
           (no-duplicatesp-equal
            (genvar1-ghostvar pkg root cnt))))

(defthm key-count-non-members-property
  (implies (and (subsetp lit big)
                (member e avoid-lst)
                (member e big)
                (not (member e lit)))
           (< (count-non-members big avoid-lst)
              (count-non-members lit avoid-lst))))

; If you look ahead to genvar1-measure-crux you'll see where
; we're going.  That lemma is the key to why genvar1 terminates.
; It is really based on key-count-non-members-property above, but
; we have to relieve the hypotheses when big and lit are replaced
; by certain ghostvar expressions.

(defthm subsetp-cons
  (implies (subsetp a b)
           (subsetp a (cons e b))))

(defthm subsetp-x-x
  (subsetp x x))

(defthm hyp1 ; -  hyp1 of key-count-non-members-property
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= i j)
                (character-listp root)
                (symbolp pkg))
           (subsetp (genvar1-ghostvar pkg root i)
                    (genvar1-ghostvar pkg root j)))
  :hints (("Goal" :induct (genvar1-ghostvar pkg root j))))

(defthm hyp2
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (< i j)
                (character-listp root)
                (symbolp pkg))
           (member (gsym pkg root i)
                   (genvar1-ghostvar pkg root j))))

(defthm hyp3
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= i j)
                (character-listp root)
                (symbolp pkg))
           (not (member (gsym pkg root j)
                        (genvar1-ghostvar pkg root i)))))

(defthm genvar1-measure-crux
  (implies (and (integerp cnt)
                (<= 0 cnt)
                (character-listp root)
                (symbolp pkg)
                (member (gsym pkg root cnt) avoid-lst))
           (< (count-non-members
               (genvar1-ghostvar pkg root (+ 1 cnt))
               avoid-lst)
              (count-non-members
               (genvar1-ghostvar pkg root cnt)
               avoid-lst))))

(in-theory (disable genvar1-ghostvar
                    (:executable-counterpart genvar1-ghostvar)))

; So here is the measure that will explain genvar1.

(defun genvar1-measure (pkg-witness char-lst avoid-lst cnt)
  (let* ((pkg-witness
          (if (symbolp pkg-witness) pkg-witness 'rewrite))
         (char-lst
          (if (character-listp char-lst) char-lst '(#\X)))
         (cnt (nfix cnt)))
    (count-non-members (genvar1-ghostvar pkg-witness char-lst cnt)
                       avoid-lst)))

; And here is genvar1.

(defun genvar1 (pkg-witness char-lst avoid-lst cnt)

; This function generates a symbol in the same package as the
; symbol pkg-witness that is guaranteed not to be a member of
; avoid-lst.  If pkg-witness is not a symbol, we default it to a
; symbol in the PACO package.  If char-lst is not a list of
; characters, we use the character list '(#\X).  If cnt is not a
; natural, we nfix it.  We have to insist that our arguments are
; well-formed because of the first four hypotheses in the crux
; lemma above.

  (declare (xargs :measure
                  (genvar1-measure pkg-witness char-lst
                                   avoid-lst cnt)))
  (let* ((pkg-witness
          (if (symbolp pkg-witness) pkg-witness 'rewrite))
         (char-lst
          (if (character-listp char-lst) char-lst '(#\X)))
         (cnt (nfix cnt))
         (sym (gsym pkg-witness char-lst cnt)))
    (cond ((member sym avoid-lst)
           (genvar1 pkg-witness char-lst avoid-lst (1+ cnt)))
          (t sym))))

; So, for example, (genvar1 'rewrite '(#\A #\B #\C) '(abc0 abc1
; abc2) 0) is PACO::ABC3.

; We now define genvar.  But proving that it generates legal
; variables not in avoid-lst is still tedious.

(defun genvar (pkg-witness prefix-string n avoid-lst)

; This is THE function Paco uses to generate new variable names.
; Prefix is a string and n is either nil or a natural number.

; We generate from prefix a legal variable symbol in the same
; package as pkg-witness that does not occur in avoid-lst.  If n
; is nil, we first try the symbol with symbol-name prefix first
; and otherwise suffix prefix with increasingly large naturals
; (starting from 0) to find a suitable symbol.  If n is non-nil
; it had better be a natural and we immediately begin trying
; suffixes from there.  Since no legal variable begins with #\*
; or #\&, we tack a #\V on the front of our prefix if prefix
; starts with one of those chars.  If prefix is empty, we use
; "V".

; However, the symbol thus created may not be a legal variable
; name, as illustrated in the opening comments to this file.  So
; we test it and if it fails, we forget about the user-supplied
; package and prefix and generate a name of the form PACO::Xi,
; for some natural i.  We'll prove that this is guaranteed to be
; a legal variable.

  (let* ((pkg-witness
          (cond ((let ((p (symbol-package-name pkg-witness)))
                   (or (equal p "KEYWORD")
                       (equal p *main-lisp-package-name*)))
; If pkg-witness is in an inappropriate package, we default it to
; a symbol in the "PACO" package.
                 'REWRITE)
                (t pkg-witness)))
         (sym
          (if (null n)
              (intern-in-package-of-symbol prefix-string
                                           pkg-witness)
            nil))
         (cnt (nfix n)))
    (cond
     ((and (null n)
           (legal-variablep sym)
           (not (member sym avoid-lst)))
      sym)
     (t (let* ((char-lst (coerce prefix-string 'list))
               (sym
                (cond
                 ((null char-lst)
                  (genvar1 pkg-witness '(#\V) avoid-lst cnt))
                 ((and (consp char-lst)
                       (or (eql (car char-lst) #\*)
                           (eql (car char-lst) #\&)))
                  (genvar1 pkg-witness
                           (cons #\V char-lst)
                           avoid-lst cnt))
                 (t (genvar1 pkg-witness
                             char-lst
                             avoid-lst cnt)))))
          (cond ((legal-variablep sym) sym)
                (t (genvar1 'REWRITE '(#\X) avoid-lst cnt))))))))

; We will next prove that genvar always produces a legal variable
; not in avoid-lst.

; We first review the restrictions imposed by legal-variablep.
; Here is a simplified presentation of it.

(local
 (defthm member-eq-transfer
   (equal (member-eq e lst) (acl2::member-eq e lst))))

; WARNING: This theorem produces stack overflows unless member-eq
; is compiled!

(defthm legal-variablep-made-explicit
 (iff
  (legal-variablep x)
  (and
   (symbolp x)
   (not (equal (symbol-package-name x) "KEYWORD"))
   (not (and (eql (char (symbol-name x) 0) #\*)
             (eql (char (symbol-name x)
                        (1- (length (symbol-name x)))) #\*)))
   (not (eql (char (symbol-name x) 0) #\&))
   (or
    (not (equal (symbol-package-name x)
                *main-lisp-package-name*))
    (and
     (member-eq x *common-lisp-symbols-from-main-lisp-package*)
     (not (member-eq x *common-lisp-specials-and-constants*))))))

  :rule-classes nil
  :hints (("Goal" :in-theory (disable member-eq
                                      acl2::member-eq
                                      acl2::member-symbol-name))))

; Next, I want to deal with an issue that might come to the
; reader's mind.  Why not modify genvar1 to include the
; legal-variablep check in it (as ACL2 does) and just iterate on
; successive cnts until finding one that works?

; Does that terminate for any pkg-witness?  I do not think we can
; prove that in ACL2.

; Suppose, for example, a new package imported the KEYWORD :FOO.
; Then NEW::FOO would be a KEYWORD.  Intuitively, only a finite
; number of keywords can be imported into a package, because the
; way we import is to specify the imports in a list as part of
; the defpkg event.  But I do not believe this is axiomatized.
; So imagine that we someday come across a package that imports
; all the keywords, or even just the infinite number of keywords
; :FOO0, :FOO1, :FOO2, ....  Then the modified genvar1 would
; iterate forever trying to get out of these imports.  Unless
; ACL2 made explicit, with an axiom, that a package can only
; import a finite number of symbols from another package, the
; modified genvar1 would be inadmissible.

; Here is another kind of counterexample.  The only legal vars
; with symbol-package-name "COMMON-LISP" are those in
; *common-lisp-symbols-from-main-lisp-package*.  So imagine that
; genvar1 were modified to loop until legal-variablep were
; satisfied.  Then (genvar1 'COMMON-LISP::FOO '(#\V) nil 0) would
; loop forever because no symbol of the form COMMON-LISP::Vi is
; in *common-lisp-symbols-from-main-lisp-package*.

; It was for such reasons that I punted on the idea of genvar1
; iterating until it found a legal variable.  Instead, genvar
; just checks and uses a particularly tame call of genvar1 to
; generate a legal variable if the initial ``guess'' fails.

; But this requires us to prove that

; (genvar1 'REWRITE '(#\X) avoid-lst cnt)

; always returns a legal-variablep, which is a little messy
; because of the complexity of legal-variablep.

(defthm gsym-prop1-lemma
  (IMPLIES (AND (INTEGERP N) (<= 0 N) (not (member #\A ans)))
           (NOT (EQUAL (EXPLODE-NONNEGATIVE-INTEGER N ans)
                       '(#\A #\R #\G #\S)))))

; The change to rewrite-equal after ACL2 Version 3.3 necessitates the following
; lemma.
(local (acl2::defthmd cons-equal-hack
         (equal (equal (cons a x) (cons a y))
                (equal x y))))

(defthm gsym-prop1
  (IMPLIES (AND (INTEGERP n)
                (<= 0 n))
           (EQUAL (SYMBOL-PACKAGE-NAME (GSYM 'REWRITE '(#\X) N))
                  "PACO"))
  :hints (("Goal" :IN-THEORY
           '((:DEFINITION BINARY-APPEND)
             (:DEFINITION ACL2::CHARACTER-LISTP)
             (:DEFINITION GSYM)
             (:DEFINITION ACL2::MEMBER-SYMBOL-NAME)
             (:DEFINITION NOT)
             (:EXECUTABLE-COUNTERPART CAR)
             (:EXECUTABLE-COUNTERPART CDR)
             (:EXECUTABLE-COUNTERPART ACL2::CHARACTER-LISTP)
             (:EXECUTABLE-COUNTERPART CHARACTER-LISTP)
             (:EXECUTABLE-COUNTERPART CHARACTERP)
             (:EXECUTABLE-COUNTERPART CONSP)
             (:EXECUTABLE-COUNTERPART EQUAL)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
             (:EXECUTABLE-COUNTERPART ACL2::MEMBER-EQUAL)
             (:EXECUTABLE-COUNTERPART SYMBOL-NAME)
             (:REWRITE ACL2::CAR-CONS)
             (:REWRITE ACL2::CDR-CONS)
             (:REWRITE CHARACTER-LISTP-EXPLODE-NONNEGATIVE-INTEGER)
             (:REWRITE CHARACTER-LISTP-TRANSFER)
             (:REWRITE COERCE-STRING-UNIQUE)
             (:REWRITE GSYM-PROP1-LEMMA)
             (:REWRITE CONS-EQUAL-HACK)
             (:REWRITE ACL2::PACO-PACKAGE)
             (:REWRITE ACL2::SYMBOL-PACKAGE-NAME-INTERN-IN-PACKAGE-OF-SYMBOL)))))

(defthm gsym-prop2
  (IMPLIES (AND (INTEGERP n)
                (<= 0 n))
           (not (EQUAL (GSYM 'REWRITE '(#\X) N) t)))
  :hints (("Goal" :use ((:instance gsym-prop1)))))

(defthm gsym-prop3
  (IMPLIES (AND (INTEGERP n)
                (<= 0 n))
           (GSYM 'REWRITE '(#\X) N))
  :hints (("Goal" :use ((:instance gsym-prop1)))))

(defthm gsym-prop4
  (IMPLIES (AND (INTEGERP n)
                (<= 0 n))
           (equal (car
                   (coerce
                    (symbol-name (GSYM 'REWRITE '(#\X) N)) 'list))
                  #\X))
  :hints (("Goal" :in-theory (enable gsym))))

(defthm legal-variablep-gsym
  (IMPLIES (AND (INTEGERP n)
                (<= 0 n))
           (legal-variablep (gsym 'rewrite '(#\X) n)))
           :hints (("Goal" :in-theory (enable legal-variablep))))

; For an explanation of why I have to define this inductive hint
; function, see below.

(defun genvar1-special-case-induction (avoid-lst cnt)
  (declare (xargs :measure
                  (genvar1-measure 'REWRITE '(#\X)
                                   avoid-lst cnt)))
  (let* ((cnt (nfix cnt))
         (sym (gsym 'REWRITE '(#\X) cnt)))
    (cond ((member sym avoid-lst)
           (genvar1-special-case-induction avoid-lst (1+ cnt)))
          (t sym))))

; I had to define the inductive hint above because in the real
; genvar1, the measured vars pkg-witness and char-lst appear to
; be self-reflexive changers and so the genvar1 expression below
; does not suggest an induction (since constants are sitting in
; changing controller slots).

(defthm legal-variablep-genvar1
  (legal-variablep (genvar1 'rewrite '(#\X) avoid-lst cnt))
  :hints (("Goal"
           :induct (genvar1-special-case-induction avoid-lst cnt)
           :in-theory (disable member-eq acl2::member-eq))))

(defthm not-member-genvar1-avoid-lst
  (not (member (genvar1 pkg-witness char-lst avoid-lst cnt)
               avoid-lst)))

(defthm legal-variablep-genvar
  (legal-variablep (genvar pkg-witness prefix-string n avoid-lst))
  :hints (("Goal" :in-theory (disable legal-variablep))))

(defthm non-member-genvar-avoid-lst
  (not (member (genvar pkg-witness prefix-string n avoid-lst)
               avoid-lst))
  :hints (("Goal" :in-theory (disable legal-variablep))))

