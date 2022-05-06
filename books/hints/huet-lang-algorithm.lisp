; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore, December, 2003 (revised July, 2007)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; I have marked with (i-am-here) various questions worthy of
; additional work.

; Second-Order Matching Under a Set of Rewriting Rules

; I implement the second-order matching algorithm of Huet and Lang and
; then couple it with a search strategy that generates and tests ``all
; possible rewrites'' under a particular set of rewrite rules.  The
; original intent of this work was to devise a way to automatically
; recognize functional instantiations.  But in addition, I want to be
; able to use it to recognize recursion schemes.  For example, I would
; like to ask ``does this defun body match the scheme
;   (IF (test x) (tweak (REC (step x))) (base x))?''
; and have it tell me "yes" even when the body in question is
;   (IF (ENDP X) 0 (ADD1 (REC (CDR X)))).
; Note that the actual body reverses the parity of the test and
; matches the given scheme under the equality (if x y z) = (if (not x)
; z y).

; The basic second-order matching algorithm will, unfortunately, match
; the bodies above by letting tweak be the constant 0 and base be the
; (add1 (rec (cdr x))) part.  The trouble is that we need to
; communicate to the matching algorithm that base is not allowed to
; call REC.  This means we will add a mild extension to the Huet-Lang
; algorithm in which we prohibit certain otherwise legal solutions.
; (i-am-here)
; One might ask ``why not generate them all and then throw out the
; unwanted ones?''  Indeed, that might be a good idea.  But because of
; our generate-and-test strategy with equalities the production of an
; ``unwanted'' solution makes the ``generate'' phase stop before it
; ever produces the acceptable version of the term.  But I could
; use pure HL matching and then reject the unwanted solution at the
; top (insde eriapw1) instead of in the middle of HL.  This might clean
;  up our code somewhat.

; Also in this file I use the HL matcher to explore some automatic
; functional instantiations and propose some heuristics for grading
; the many alternative matches that result.

; ---------------------------------------------------------------------------
; Huet-Lang Matching - Preliminaries for Basic Algorithm

; We start by developing the Huet-Lang algorithm.

; For a description of the basic algorithm, see "Automatically
; Computing Functional Instantiations," in Proceedings of the ACL2
; Workshop 2009(eds. D. Russinoff and S. Ray), Boston, 2009, URL
; http://www.cs.utexas.edu/users/moore/publications/moore-09a.pdf .
; That is my rendition of G. Huet and B. Lang, ``Proving and applying
; program transformations expressed with second-order patterns,'' Acta
; Informatica, 11, pp 31--55, 1997.

; In this implementation, higher order terms will be like terms but
; some ``function symbols'' will be integers.  Such ``function
; symbols'' denote second-order variables, e.g., h_i, and will be
; called ``function variables.''  Substitutions will sometimes pair
; these function variables with lambda expressions.  When we
; substitute lambda expressions for function variables we will also use
; integers for the formals, to save the bother of creating symbols.
; Thus, we will be dealing with such ``terms'' as
; ((lambda (1 2) (1 1 2)) A B)
; which beta reduces to (1 A B).

; Not all functional variables will be integers.  Only the h_i of
; Huet-Lang will be integers.  The constrained functions of the
; pattern will be treated as functional variables also.  They retain
; their normal symbolp names.  Thus, a term like (X X), where X is a
; constrained function, is problematic.  X, as a function symbol, may
; be bound to a lambda expression and X, as a variable symbol, may be
; bound to a term.  To avoid this ambiguity, binding "pairs" are
; really triples: (pat fnp . val), where pat is an individual or
; functional variable, fnp is non-nil if pat is a functional
; variablep, and val is the binding.  Fnp can take on two values, T
; and DONE.  The value DONE is present pat is a constrained but
; undefined function or pat is a hereditarily constrained defined
; function that has been recursively explored by the one-way-unify
; process.

(in-package "ACL2")

(defun is-boundp (var fnp bindings)
  (cond ((endp bindings) nil)
        ((and (equal var (caar bindings))
              (iff fnp (cadar bindings)))
         (car bindings))
        (t (is-boundp var fnp (cdr bindings)))))

(defmacro hl-binding (trip) `(cddr ,trip))

; Substitutions always hit free variables, not bound ones.  So a
; substitution triple like (i fnp . x), where i is an integer, will
; always be a functional substitution and never be a substitution for
; the formal variable i.  That is, fnp will be non-nil in
; this case.  We do not optimize away this special case.

; It is actually unnecessary to cons up (lambda (1 2) (1 1 2)) since
; we will know (1 1 2) is a lambda expression.  In the rest of this
; file, we use the term ``lambda expression'' to mean the latter
; rather than the former, i.e., a term in which integers are used as
; ``variable symbols.''  Such an integer i denotes variable Vi and the
; term denotes an ACL2 lambda expression (LAMBDA (v1 ... vmax) term),
; for some integer max as large as any integer ``variable symbol'' in
; term.  Thus, (CONS 1 3) may denote (LAMBDA (V1 V2 V3 V4) (CONS V1
; V3)).  The actual arity of one of these abbreviated lambda's cannot
; be determined except by context.  We assume the original pattern and target
; are well-formed and use their function symbols with consistent arities.

; The function below shows how we do Beta reduction, given a
; pseudo-term containing integers among its variable symbols, and a
; list of arguments.  For example,
; (subst-by-position '(IF 1 1 3) '(a b c)) = '(IF A A C).

(program)

(mutual-recursion

(defun subst-into-pterm-by-position (pterm args)
  (cond ((variablep pterm)
         (cond ((integerp pterm) (nth (- pterm 1) args))
               (t pterm)))
        ((fquotep pterm) pterm)
        (t (fcons-term (ffn-symb pterm)
                       (subst-into-pterm-by-position-lst
                        (fargs pterm)
                        args)))))

(defun subst-into-pterm-by-position-lst (pterm-lst args)
  (cond ((endp pterm-lst) nil)
        (t (cons (subst-into-pterm-by-position (car pterm-lst) args)
                 (subst-into-pterm-by-position-lst (cdr pterm-lst) args))))))

; Note:  The definition above exploits the fact that VARIABLEP is ATOM, not
; SYMBOLP and FCONS-TERM is just CONS and does not try to do anything fancy
; with the ``function symbol.''

; In our recursive decent through a matching problem we will keep a
; variable hmax, indicating the largest function variable in the
; problem.  Thus, when we generate new function variables to carry out
; the Imitation rule, we use hmax+1 as the first.

; Finally, in our recursive descent we will keep a list of bindings
; that will enable us to construct a winning substitution for a given
; matching problem.  Such a list of bindings is not quite a proper
; substitution because the substitutions of functional variables must
; be applied to the right-hand sides.  That is, we might construct a
; list of bindings like this:

; ((V NIL . (CAR A))
;  (3 T   . (REV 1))
;  (2 T   . (LEN 1))
;  (1 T   . (CONS (2 1) (3 2))))

; This would actually denote the mixed substitution

; ((V  . (CAR A))
;  (F1 . (LAMBDA (V1 V2) (CONS (LEN V1) (REV V2)))))

; We call the raw list of bindings a ``pseudo-substitution'' and will
; traffic in them exclusively.  But it will be possible to convert a
; pseudo-substitution to a substitution for use outside the
; second-order matcher.

; We will have to pass pseudo-substitutions to recursive calls of the
; matcher.  Thus it is convenient to know the hmax for each
; pseudo-substitution.  Thus, we will pair each pseudo-substitution
; with its hmax (in the car) and pass those objects around.  We call
; them ``psubsts''.

(defun nats-from-to (i j)
; (nats-from-to 1 3) = '(1 2 3)
  (cond ((and (integerp i)
              (integerp j)
              (<= i j))
         (cons i (nats-from-to (+ 1 i) j)))
        (t nil)))

(defun make-new-h-terms (args i hargs)
  (cond ((endp args) nil)
        (t (cons (fcons-term i hargs)
                 (make-new-h-terms (cdr args)
                                   (+ 1 i)
                                   hargs)))))

; ---------------------------------------------------------------------------
; Minor Aside:  Restrictions on Bindings

; For reasons that will become obvious, we want to extend the basic
; Huet-Lang algorithm to allow the user to specify that the matching
; substitutions satisfy certain restrictions, e.g., that that the
; binding of a given variable not involve a given function symbol.  We
; may ultimately want to express these restrictions as predicates that
; are evaluated; but at the moment I only see the need for three so I
; hand-code them.  A ``restrictions'' list is an alist tripling
; variables (individual or functional), the flag NIL or T (to indicate
; whether this is an individual or functional var) with restrictions.
; A restriction is thus (var fnp . restriction).  The three
; restrictions we implement are:

; (:MUST-IMITATE fn)              - pterm is a pseudo-term, e.g., (CAR (1 X))
; (:MUST-NOT-CONTAIN fn1 ... fnk) - the fni are function symbols
; (:MUST-BE-VARIABLE)             - binding must be a variable symbol,
;                                   which means x has the form
;                                   (:CONSTANT var) actually.
;
; The meaning of a restrictions list is that we never allow a binding
; that would violate the restrictions.  We check this by actually
; creating the newly proposed bindings, i.e., adding the new triple, and
; then calling a predicate to ``ok'' it.  We cannot check it one
; binding at a time because we frequently have to check other bindings
; than the restricted one.  E.g., if function variable 1 is not
; supposed to be bound to a term involving fn1 and function variable 1
; is bound to a pterm involving function variable 2, then 2 inherits
; the restriction.  Rather than modify the restrictions as we go, we
; just ask, every time we produce a new bindings list, whether
; function variable 1 (still) satisfies its restriction.

(defun hl-functional-variablep (fn wrld)
  (or (integerp fn)
      (and (symbolp fn)
           (getprop fn 'hereditarily-constrained-fnnames nil
                    'current-acl2-world wrld))))

(defun hereditarily-constrained-defunp (fn wrld)
  (and (symbolp fn)
       (let ((val (getprop fn 'hereditarily-constrained-fnnames nil
                           'current-acl2-world wrld)))
         (and val (cdr val)))))

(defun initial-fnp (fn wrld)
  (if (hereditarily-constrained-defunp fn wrld)
      t
    'DONE))

; I like the prefix HL for Huet-Lang because it is also suggestive of
; ``Higher (Order) Logic.''

(mutual-recursion

(defun hl-ffnnamesp (fns pterm bindings wrld)

; We determine whether an element of fns is used as a function symbol
; in the instantiation of pterm under bindings.

  (cond ((variablep pterm)

; We have encountered pterm in a variable position.  It is either a
; symbol or an integer, the latter denoting a formal variable of an
; abbreviated lambda expression.  The latter are never bound in
; bindings.  If pterm is a symbol, it is an individual variable.  If
; it is bound as a variable in bindings, then it is bound to a ground term
; (individual variables always are).  So we nil out the bindings
; before asking whether any fns occur in the binding.  On the other
; hand, if pterm is an integer, then it can't be bound in bindings and
; so no fns occur in it.  The tricky thing here is that the integer
; pterms might actually BE bound in bindings!  But when 3, for
; example, is bound in bindings, then it is the function variable 3,
; not the formal individual variable 3, that is bound.  That is, (3 1
; 2 3) contains two 3's, one of which might be bound in bindings and
; one of which cannot be.

         (cond ((symbolp pterm)
                (let ((trip (is-boundp pterm nil bindings)))
                  (cond (trip (hl-ffnnamesp fns (hl-binding trip) nil wrld))
                        (t nil))))
               (t nil)))
        ((fquotep pterm) nil)
        ((member-equal (ffn-symb pterm) fns) t)
        ((hl-functional-variablep (ffn-symb pterm) wrld)
         (let ((trip (is-boundp (ffn-symb pterm) t bindings)))
           (cond (trip (or (hl-ffnnamesp fns (hl-binding trip) bindings wrld)
                           (hl-ffnnamesp-lst fns (fargs pterm) bindings
                                             wrld)))
                 (t (hl-ffnnamesp-lst fns (fargs pterm) bindings wrld)))))
        (t (hl-ffnnamesp-lst fns (fargs pterm) bindings wrld))))

(defun hl-ffnnamesp-lst (fns args bindings wrld)
  (cond ((endp args) nil)
        (t (or (hl-ffnnamesp fns (car args) bindings wrld)
               (hl-ffnnamesp-lst fns (cdr args) bindings wrld))))))

(defun hl-restrictionp (bindings var fnp restr wrld)

; We check whether bindings satisfies the restriction restr on var.

  (let ((trip (is-boundp var fnp bindings)))
    (cond
     ((null trip) t)
     ((eq (car restr) :MUST-IMITATE)
      (and (not (variablep (hl-binding trip)))
           (not (fquotep (hl-binding trip)))
           (equal (ffn-symb (hl-binding trip)) (cadr restr))))
     ((eq (car restr) :MUST-BE-VARIABLE)
      (let ((val (hl-binding trip)))
        (and (consp val)
             (eq (car val) :CONSTANT)
             (variablep (cadr val)))))
     ((eq (car restr) :MUST-NOT-CONTAIN)
      (not (hl-ffnnamesp (cdr restr) (hl-binding trip) bindings wrld)))
     (t nil))))

(defun hl-restrictionsp (bindings restrictions wrld)

; Does bindings satisfy all the restrictions?  Each element of restrictions
; is of the form (var fnp restr), where var is a variable (either
; individual or functional), fnp is t if var is a functional var,
; and restr is one of
; (:MUST-IMITATE g) - where g is a function symbol
; (:MUST-BE-VARIABLE)
; (:MUST-NOT-CONTAIN g1 ... gn) - where gi are function symbols.

  (cond ((endp restrictions) t)
        ((hl-restrictionp bindings
                          (caar restrictions)
                          (cadar restrictions)
                          (cddar restrictions)
                          wrld)
         (hl-restrictionsp bindings (cdr restrictions) wrld))
        (t nil)))

; End of Minor Aside
; ---------------------------------------------------------------------------
; Huet-Lang Matching - The Algorithm

; Here is the basic Huet-Lang second-order matching algorithm,
; extended with our notion of restrictions.

; Note: Pat is a term except it may have integers in some function
; symbol positions.  It is a pterm except that it never contains any
; integers in variable positions.  The only time integers appear in
; pterms is when the pterm is an abbreviated lambda and we never call
; hl-one-way-unify1 on a lambda body (without first having done beta
; reduction).

; Term is a term except that it may contain ``subterms'' of the form
; (:CONSTANT sym), where sym is a variable symbol.  Think of these
; subterms as Skolem constants, i.e., (sym).  Where do they come from
; and why are they there?  They are inserted into the term by
; convert-free-vars-to-constants, which replaces all (free) variables
; in the term by such constants.  Why do we use (:CONSTANT sym)
; instead of (sym)?  Because sym might be used as a function symbol in
; the term.  For example, if we converted (CONS A (A)) to (CONS (A)
; (A)) we would be making a mistake.  Why do we eliminate variables
; for constants?  The classic Huet-Lang algorithm produces lambda
; expressions that are closed.  That is, the only variables occurring
; in the body are the formals.  But in our functional instantiations
; we need to support lambda expressions such as (lambda (x y) (cons A
; x)) The basic problem with Huet-Lang is that when we match (f x)
; against A, say, the only match is to let f be the identity function
; and match x to A.  But if x cannot match A, we're hosed, as in (f
; '1) versus A.  But (f '1) does match (A), by letting f "imitate" (A)
; with (lambda (x) (A)).  So we need to use imitation when the
; first-order term is a variable.  But we cannot just dump the
; variable into the lambda body because then it appears to be bindable
; in subsequent matches.  We must replace the first order vars by
; constants of some form so they can get transported around in lambdas
; created by intermediate matches without getting confused with
; variables that occurred in the pattern originally.  Finally, we have
; to build the machinery to map these (:CONSTANT sym) expressions out
; and recover ACL2 terms.  That is tricky too because (lambda (x)
; (CONS x (:CONSTANT X))) cannot be converted to (lambda (x) (cons x
; x))!  We have to avoid capture by renaming the formals, e.g., to get
; (lambda (z) (cons z X)).

(mutual-recursion

(defun hl-one-way-unify1 (pat term hmax bindings restrictions wrld)

; We return a list of all the psubsts solving the given problem.

  (cond
   ((variablep pat)
    (let ((trip (is-boundp pat nil bindings)))

; Claim: Every variable bound by bindings is bound to a ground term.
; Note that this invariant is preserved below, when we bind pat to
; term.

      (cond (trip (cond ((equal (hl-binding trip) term)
                         (list (cons hmax bindings)) )
                        (t nil)))
            (t (let ((new-bindings
                      (cons (list* pat nil term) bindings)))
                 (cond
                  ((hl-restrictionsp new-bindings restrictions wrld)
                   (list (cons hmax new-bindings)))
                  (t nil)))))))
   ((or (fquotep pat)
        (eq (car pat) :CONSTANT))
    (cond ((equal pat term) (list (cons hmax bindings)))
          (t nil)))
   ((hl-functional-variablep (ffn-symb pat) wrld)  ;;; function variable
    (let ((trip (is-boundp (ffn-symb pat) t bindings)))
      (cond
       (trip

; (hl-binding temp) is an abbreviated lambda expression, body, denoting
; (lambda (v1 ... vn) body), so the pat is essentially
; ((lambda (v1 ... vn) body) pat1 ... patn) and we must beta-reduce it
; and work on the result.

        (hl-one-way-unify1
         (subst-into-pterm-by-position (hl-binding trip) (fargs pat))
         term
         hmax
         bindings
         restrictions
         wrld))
       ((variablep term)

; Projection:  We have to consider the possibility that the function
; variable is (lambda (v1 ... vn) vi), for each i, and that the actual
; corresponding to vi matches term.

        (hl-one-way-unify1-projection
         (ffn-symb pat)
         (fargs pat)
         1
         term
         hmax
         bindings
         restrictions
         wrld))
       ((or (fquotep term)
            (eq (car term) :CONSTANT))

; Term is 'evg or else is (:CONSTANT var).  Imagine that term were
; (FC) instead, for some concrete constant function FC.  This case is
; just like the case below, where term has a concrete function symbol
; except that here we pretend that ACL2 constants are represented as
; nests of (concrete) constructor function calls rather than quoted
; evgs.  So imitation binds the function variable to (lambda (v1
; ... vn) 'evg).  Read the code for hl-one-way-unify1-imitation.

; Note: We are taking a short cut here that introduces a form of
; incompleteness in our matcher!  See the Essay on Incompleteness at
; the conclusion of this clique of functions.

        (let ((new-bindings
               (cons (list* (ffn-symb pat)
                            (initial-fnp (ffn-symb pat) wrld)
                            term)
                     bindings))
              (psubst-lst
               (hl-one-way-unify1-projection
                (ffn-symb pat)
                (fargs pat)
                1
                term
                hmax
                bindings
                restrictions
                wrld)))
          (cond
           ((hl-restrictionsp new-bindings restrictions wrld)
            (cons (cons hmax new-bindings)
                  psubst-lst))
           (t psubst-lst))))
       (t

; In this case, the term has a concrete function symbol, F, and we must do
; both projection (as above) and imitation.  Imitation:  The function
; variable, fv, is bound to (lambda (V1 ... VN) (F (H1 v1 ... vn) ...)).

        (append (hl-one-way-unify1-imitation
                 pat
                 term
                 hmax
                 bindings
                 restrictions
                 wrld)
                (hl-one-way-unify1-projection
                 (ffn-symb pat)
                 (fargs pat)
                 1
                 term
                 hmax
                 bindings
                 restrictions
                 wrld))))))
   ((and (eq (ffn-symb pat) 'IF)
         (not (variablep (fargn pat 1)))
         (not (fquotep (fargn pat 1)))
         (symbolp (ffn-symb (fargn pat 1)))
         (hl-functional-variablep (ffn-symb (fargn pat 1)) wrld)
         (not (is-boundp (ffn-symb (fargn pat 1)) t bindings)))

; This is a special case where the pattern is (IF (fn ...) pat1 pat2),
; where fn is an unbound functional variable known to the user (i.e.,
; not one introduced by us).  In this special case we consider some
; alternative ways to match with term, depending on the shape of term.

    (append

; (a) We can just proceed to match pat with term, just as we would
; have without this special case.  Note that this code is duplicated
; in the t-clause, below, of the cond we're in.  Keep these in sync!

     (cond
      ((variablep term) nil)
      ((or (fquotep term)
           (eq (car term) :CONSTANT))
       nil)
      ((equal (ffn-symb pat) (ffn-symb term))
       (hl-one-way-unify1-lst (fargs pat) (fargs term)
                              hmax bindings restrictions wrld))
      (t nil))

; (b) If term is (IF term1 term2 term3), then we should also consider
; the possibility of matching pat with (if (NOT term1) term3 term2),
; except we use the IF form of NOT.

     (cond ((and (nvariablep term)
                 (not (fquotep term))
                 (eq (ffn-symb term) 'IF))
            (hl-one-way-unify1-lst (fargs pat)
                                   (list (fcons-term* 'IF (fargn term 1)
                                                      *nil* *t*)
                                         (fargn term 3)
                                         (fargn term 2))
                                   hmax bindings restrictions wrld))
           (t
            (append

; (c) If term is not an IF, we consider seeing it as (IF T term ...),
; except we do not have to match pat2 with ...!

             (hl-one-way-unify1-lst (list (fargn pat 1) (fargn pat 2))
                                    (list *t* term)
                                    hmax bindings restrictions wrld)

; (d) If term is not an IF, we consider seeing it as (IF NIL ... term),
; except we do not have to match pat2 with ....

             (hl-one-way-unify1-lst (list (fargn pat 1) (fargn pat 3))
                                    (list *nil* term)
                                    hmax bindings restrictions wrld))))))
   (t                          ;;; pat is LAMBDA application or concrete fn

; Note:  This is case (a) above and the two should be kept in sync.

    (cond
     ((variablep term) nil)
     ((or (fquotep term)
          (eq (car term) :CONSTANT))
      nil)
     ((equal (ffn-symb pat) (ffn-symb term))
      (hl-one-way-unify1-lst (fargs pat) (fargs term)
                             hmax bindings restrictions wrld))
     (t nil)))))

(defun hl-one-way-unify1-lst (pargs targs hmax bindings restrictions wrld)
  (cond
   ((endp pargs) (list (cons hmax bindings)))
   (t (let ((psubst-lst
             (hl-one-way-unify1 (car pargs) (car targs)
                                hmax bindings restrictions wrld)))
        (hl-one-way-unify1-lst-continue psubst-lst
                                        (cdr pargs)
                                        (cdr targs)
                                        restrictions
                                        wrld)))))

(defun hl-one-way-unify1-lst-continue
  (psubst-lst pargs targs restrictions wrld)
  (cond ((endp psubst-lst) nil)
        (t (append (hl-one-way-unify1-lst pargs
                                          targs
                                          (car (car psubst-lst))
                                          (cdr (car psubst-lst))
                                          restrictions
                                          wrld)
                   (hl-one-way-unify1-lst-continue (cdr psubst-lst)
                                                   pargs
                                                   targs
                                                   restrictions
                                                   wrld)))))

(defun hl-one-way-unify1-projection
  (fv pat-lst i term hmax bindings restrictions wrld)
  (cond ((endp pat-lst) nil)
        (t (let ((new-bindings
                  (cons (list* fv
                               (initial-fnp fv wrld)
                               i) ; (lambda (v1 ... vn) vi)
                        bindings)))
             (cond
              ((hl-restrictionsp new-bindings restrictions wrld)
               (append (hl-one-way-unify1
                        (car pat-lst)
                        term
                        hmax
                        new-bindings
                        restrictions
                        wrld)
                       (hl-one-way-unify1-projection fv (cdr pat-lst) (+ 1 i)
                                                     term hmax
                                                     bindings restrictions
                                                     wrld)))
              (t (hl-one-way-unify1-projection fv (cdr pat-lst) (+ 1 i)
                                               term hmax
                                               bindings restrictions
                                               wrld)))))))

(defun hl-one-way-unify1-imitation (pat term hmax bindings restrictions wrld)
  (let* ((fv (ffn-symb pat))
         (pat-args (fargs pat))
         (fc (ffn-symb term))
         (hargs (nats-from-to 1 (len pat-args)))
         (body (fcons-term fc
                           (make-new-h-terms (fargs term)
                                             (+ hmax 1)
                                             hargs))))
    (let ((new-bindings (cons (list* fv (initial-fnp fv wrld) body) bindings)))
      (cond ((hl-restrictionsp new-bindings restrictions wrld)
             (hl-one-way-unify1
              (subst-into-pterm-by-position body pat-args)
              term
              (+ hmax (len (fargs term)))
              new-bindings
              restrictions
              wrld))
            (t nil)))))
)

; Essay on Incompleteness: Our handling of quoted constants makes our
; matcher incomplete in the following sense.  We are acting like the
; concrete nest representing each constant is of depth 1, i.e., for
; every constant 'c there is a concrete constructor fc such that 'c is
; (fc).  But ``in reality,'' constants are composed of other
; constants.  So consider the matching problem (g x) versus '(0 . 0).
; Our code gives two solutions to this problem, one where x is the
; entire constant and g is the identity function, and the other where
; x is irrelevant and g is the constant function '(0 . 0).  But had we
; thought of '(0 . 0) as (cons (zero) (zero)) there would be five
; solutions, including one where x is (zero) and g is cons-onto-0,
; i.e., g := (lambda (v1) (cons v1 0)).  These solutions exploiting
; the internal structure of constants are missed by our code.

; It is thus possible that we will find NO solutions when in fact there are
; solutions.  Consider, for example,

; (IF (g x) (g y) x) versus (IF '(0 . 0) '(1 . 0) '0).

; Here, IF is just a convenient, concrete 3-place symbol.  We find no
; solutions (see footnote below for a description of the process).
; But had we phrased the problem as

; (IF (g x) (g y) x) versus (IF (CONS (Z) (Z)) (CONS (ONE) (Z)) (Z))

; we would find a solution, namely let g be cons-onto-0 and let x be
; 0 and y be 1.

; Footnote: To try to match

; (IF (g x) (g y) x) with (IF '(0 . 0) '(1 . 0) '0)

; we find two solutions to the first sub-problem, i.e., matching (g x)
; with '(0 . 0).  One of those lets g be the constant function '(0
; . 0), but that precludes us from solving the second sub-problem,
; i.e., matching (g y) with '(1 . 0).  The other solution to the first
; sub-problem is to let g be the identity and let x be '(0 . 0).  That
; allows us to solve the second sub-problem, but then we fail on the
; third because we need x to be '0, not '(0 . 0).

; ---------------------------------------------------------------------------
; Huet-Lang Matching:  Preliminaries for Top Level

; The code below eliminates the free vars in terms, turning them all into
; constants.

(mutual-recursion

(defun convert-free-vars-to-constants (term)
  (cond
   ((variablep term) (list :constant term))
   ((fquotep term) term)
   (t (fcons-term (ffn-symb term)
                  (convert-free-vars-to-constants-lst (fargs term))))))

(defun convert-free-vars-to-constants-lst (args)
  (cond ((endp args) nil)
        (t (cons (convert-free-vars-to-constants (car args))
                 (convert-free-vars-to-constants-lst (cdr args)))))))

; And this function reverses that process.

(mutual-recursion

(defun convert-constants-to-free-vars (term)
  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((eq (car term) :constant) (cadr term))
   (t (fcons-term (ffn-symb term)
                  (convert-constants-to-free-vars-lst (fargs term))))))

(defun convert-constants-to-free-vars-lst (args)
  (cond ((endp args) nil)
        (t (cons (convert-constants-to-free-vars (car args))
                 (convert-constants-to-free-vars-lst (cdr args)))))))

; To get rid of constant expressions in LAMBDA expressions we must
; avoid capture!  For example, (lambda (x y) (f x y (:constant y))),
; is NOT (lambda (x y) (f x y y)) but (lambda (x z) (f x z y))!  We need
; to (a) sweep a term and collect all the :constants; (b) generate new
; names for each of the constants appearing in the formals of the
; lambda; (c) rename the formals and their occurrences outside
; :constant expressions, and (d) eliminate the :constant expressions.
; We can do (c) and (d) in one pass.

(mutual-recursion

(defun collect-bound-constants (formals term ans)
  (cond
   ((variablep term) ans)
   ((fquotep term) ans)
   ((eq (car term) :constant)
    (cond ((member-eq (cadr term) formals)
           (add-to-set-eq (cadr term) ans))
          (t ans)))

; Note: Are there :constant expressions inside lambda bodies?  Could I
; see ((lambda (x y) (f x y (:constant y))) a b)?  I don't think so.
; I believe that all lambda applications appearing in a substitution
; appear in the original term.  The HL algorithm always beta-reduces
; any lambda application it might be ``tempted'' to create.

   (t (collect-bound-constants-lst formals (fargs term) ans))))

(defun collect-bound-constants-lst (formals args ans)
  (cond ((endp args) ans)
        (t (collect-bound-constants-lst
            formals
            (cdr args)
            (collect-bound-constants formals (car args) ans))))))

(defun genvar-lst (vars avoid-lst)
  (cond ((endp vars) nil)
        (t (let* ((old-var (car vars))
                  (new-var (genvar old-var "V" 1 avoid-lst)))
             (cons (cons old-var new-var)
                   (genvar-lst (cdr vars)
                                (cons new-var avoid-lst)))))))

(mutual-recursion

(defun rename-and-convert-constants (term alist)
  (cond ((variablep term)
         (let ((pair (assoc-eq term alist)))
           (cond (pair (cdr pair))
                 (t term))))
        ((fquotep term) term)
        ((eq (car term) :constant)
         (cadr term))
        (t (fcons-term (ffn-symb term)
                       (rename-and-convert-constants-lst (fargs term)
                                                         alist)))))

(defun rename-and-convert-constants-lst (lst alist)
  (cond ((endp lst) nil)
        (t (cons (rename-and-convert-constants (car lst) alist)
                 (rename-and-convert-constants-lst (cdr lst) alist))))))

(defun convert-constants-to-free-vars-in-lambda (lambda-expr)
  (let* ((formals (lambda-formals lambda-expr))
         (body (lambda-body lambda-expr))
         (constants (collect-bound-constants formals body nil))
         (alist (genvar-lst constants formals)))
    (make-lambda
     (rename-and-convert-constants-lst formals alist)
     (rename-and-convert-constants body alist))))

; Now we do the same for alists (substitutions) of both the variable and
; functional variety.

(defun convert-constants-to-free-vars-in-alist (alist)
  (cond
   ((endp alist) nil)
   (t (let* ((pair (car alist))
             (var (car pair))
             (val (cdr pair)))
        (cond
         ((and (consp val)
               (eq (car val) 'LAMBDA))
          (cons (cons var (convert-constants-to-free-vars-in-lambda val))
                (convert-constants-to-free-vars-in-alist (cdr alist))))
         (t
          (cons (cons var
                      (convert-constants-to-free-vars val))
                (convert-constants-to-free-vars-in-alist (cdr alist)))))))))

; And this does it to a list of substitutions!

(defun convert-constants-to-free-vars-in-alist-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (convert-constants-to-free-vars-in-alist (car lst))
                 (convert-constants-to-free-vars-in-alist-lst (cdr lst))))))

; Our next goal is to develop the code to convert a psubst to a mixed
; substitution (for individual variables and constrained function symbols).

(mutual-recursion

(defun hmax (term)

; Find the largest function variable in term.  We assume that all
; function variables are non-negative.

  (cond ((variablep term) -1)
        ((fquotep term) -1)
        ((integerp (ffn-symb term))
         (max (ffn-symb term)
              (hmax-lst (fargs term))))
        (t (hmax-lst (fargs term)))))

(defun hmax-lst (args)
  (cond ((endp args) -1)
        (t (max (hmax (car args))
                (hmax-lst (cdr args)))))))

(mutual-recursion

(defun subst-for-fn (fv body term)

; Replace all calls of function variable fv by body and do beta reduction.

  (cond ((variablep term) term)
        ((fquotep term) term)
        ((equal fv (ffn-symb term))
         (subst-into-pterm-by-position body (fargs term)))
        (t (fcons-term (ffn-symb term)
                       (subst-for-fn-lst fv body (fargs term))))))

(defun subst-for-fn-lst (fn body args)
  (cond ((endp args) nil)
        (t (cons (subst-for-fn fn body (car args))
                 (subst-for-fn-lst fn body (cdr args)))))))

(defun subst-for-fn-in-psubst (fv body psubst)
  (cond ((endp psubst) nil)
        ((cadar psubst) ; functional binding
         (cons (list* (caar psubst)
                      t
                      (subst-for-fn fv body (cddar psubst)))
               (subst-for-fn-in-psubst fv body (cdr psubst))))
        (t (cons (car psubst)
                 (subst-for-fn-in-psubst fv body (cdr psubst))))))

(defun decode-psubst (psubst wrld)

; We eliminate every reference to functional variables in the terms
; appearing in the substitution.  We assume a functional variable
; cannot appear before it was introduced.  That is, the order of the
; pairs in psubst is important: if the imitation rule bound fv to a
; term involving new function variables h1, ..., hn, then the bindings
; of the hi occur before that for fv, i.e., the pair binding fv was
; added to the list and then later pairs for the hi were added.

; Note that some of the functional variables appearing in the psubst
; were in the original problem and others were introduced by the
; Imitation rule during the matching.  Those that were in the original
; problem are bound in fv-name-and-formals-alist to their symbolic
; names and formals.  (Recall that our abbreviated lambda notation
; does not record the arity, much less the formals, of the function
; variables.)  The bindings of these original fv are converted to
; proper lambda expressions using these supplied formals.  The
; bindings of introduced fv (the hi) are discarded.

  (cond ((endp psubst) nil)
        ((cadar psubst)  ; a functional binding
         (let* ((fv (caar psubst))
                (body (cddar psubst))
                (new-psubst (subst-for-fn-in-psubst fv body (cdr psubst))))
           (cond
            ((symbolp fv)  ; this function comes from wrld
             (cons (cons fv
                         (list 'LAMBDA (formals fv wrld)
                               (subst-into-pterm-by-position
                                body
                                (formals fv wrld))))
                   (decode-psubst new-psubst wrld)))
            (t (decode-psubst new-psubst wrld)))))
        (t (cons (cons (caar psubst)
                       (cddar psubst))
                 (decode-psubst (cdr psubst) wrld)))))

(defun decode-psubst-lst (psubst-lst wrld)
  (cond ((endp psubst-lst) nil)
        (t (cons (decode-psubst (cdr (car psubst-lst)) wrld)
                 (decode-psubst-lst (cdr psubst-lst) wrld)))))


(defun make-fn-name-and-formals-alist (fns i wrld)

; Fns is a list of function symbols, some of which are constrained
; functions and some of which are not.  Collect the constrained
; function symbols from among the symbols in fns, assign to each a
; number k (starting at i), and return a list of elements of the form
; (k fn . formals).

  (cond ((endp fns) nil)
        ((getprop (car fns) 'constrainedp nil 'current-acl2-world wrld)
         (cons (list* i (car fns) (formals (car fns) wrld))
               (make-fn-name-and-formals-alist (cdr fns) (+ 1 i) wrld)))
        (t (make-fn-name-and-formals-alist (cdr fns) i wrld))))

(mutual-recursion

(defun convert-term-to-hl-term (term alist)

; Alist is a fn-name-and-formals-alist containing pairs of the form (k
; fn . formals).  We copy term and replace all calls of fn by k, for
; each fn in alist.

  (cond ((variablep term) term)
        ((fquotep term) term)
        (t (let ((k (car (assoc-equal-cadr (ffn-symb term) alist))))
             (fcons-term (or k (ffn-symb term))
                         (convert-term-to-hl-term-lst (fargs term) alist))))))

(defun convert-term-to-hl-term-lst (term-lst alist)
  (cond ((endp term-lst) nil)
        (t (cons (convert-term-to-hl-term (car term-lst) alist)
                 (convert-term-to-hl-term-lst (cdr term-lst) alist))))))

(defun strip-mixed-subst (alist)

; Split the mixed substitution into its two components, a variable
; substitution and a functional substitution, based on whether the
; substituted value is a lambda expression.

  (cond ((endp alist) (mv nil nil))
        (t (mv-let (var-alist fn-alist)
                   (strip-mixed-subst (cdr alist))
                   (let* ((pair (car alist))
                          (val (cdr pair)))
                     (cond
                      ((and (consp val)
                            (eq (car val) 'lambda))
                       (mv var-alist (cons pair fn-alist)))
                      (t (mv (cons pair var-alist) fn-alist))))))))

(defun sublis-mixed (alist term)

; Alist is a substitution in which some keys are paired with lambda
; expressions and others aren't.  Those keys paired with lambdas are
; (constrained) function symbols and those that aren't are individual
; variable symbols.  We instantiate term with this mixed substitution.
; We do it by first instantiating the individual variables.  Then we
; do a functional substitution with the lambda expressions.  We do it
; in this order because the functional instantiation may introduce
; free variables that are then hit by the individual var substitution.
; For example, consider the mixed substitution ((x . y) (f . (lambda
; (y) (cons x y)))) applied to (f x).  If we use the functional
; instantiation first, we get (cons x x) and then instantiate that
; with the variable substitution to get (cons y y).  If, on the other
; hand, we use the variable substitution first we get (f y) and then
; the functional instantiation produces (cons x y).

; Note that the notion of a mixed substitution precludes an entry like
; (F . EQUAL), since F would look like an individual variable.  We
; have to use (F . (LAMBDA (X Y) (EQUAL X Y))) to get that effect.

; Note: Recall that sublis-var and sublis-fn use cons-term to
; construct their answer terms and cons-term does computation on
; quoted constants.  Thus, while one might expect the instantiation of
; (binary-+ x x), when x is replaced by '2, to be (binary-+ '2 '2) it
; is actually '4.  Thus, this function is problematic if you're using
; it to check whether a substitution actually produces an instance
; identical to the desired target!

  (mv-let (var-alist fn-alist)
          (strip-mixed-subst alist)
          (mv-let
           (erp val)
           (sublis-fn
            (convert-constants-to-free-vars-in-alist fn-alist)
            (sublis-var (convert-constants-to-free-vars-in-alist var-alist)
                        term)
            nil)
           (cond (erp (er hard 'sublis-mixec
                          "Unhandled error, ~x0"
                          `(sublis-mixed ',alist ',term)))
                 (t val)))))

; ---------------------------------------------------------------------------
; Huet-Lang Matching:  Top Level

(defun hl-one-way-unify (pat term restrictions wrld)

; We determine whether there is a second-order instance of pat that
; matches term, respecting the given restrictions.  We treat all
; constrained functions in pat as instantiable.  We return a triple
; (mv flg psubst-lst mixed-subst-lst).  If flg is nil, no match is
; possible.  Else, mixed-subst-lst is a list of ``mixed
; substitutions'', each of which suffices to produce a match.  See
; sublis-mixed for a description of mixed substitutions.  Psubst-lst is
; in 1:1 correspondence with mixed-subst-lst but is in the internal
; form.

; In particular, if psubst corresponds to one of the mixed
; substitutions, subst, then psubst is a pair, (hmax . bindings).  If
; subst substitutes a lambda expression for a function variable, then
; bindings substitutes a pseudo-term for that function symbol.  E.g.,
; subst may contain the pair (FN . (LAMBDA (X Y) (EQUAL X Y))) where
; bindings has (FN . (EQUAL 1 2)).  In addition, bindings contains
; additional pairs that substitute for function variables introduced
; by the matching process (the ``Hi'' of the Huet-Lang algorithm's
; Imitation rule); those introduced function vars have been eliminated
; in the mixed substitution.  The hmax for each psubst pair is the
; number of function variables in the corresponding bindings, the
; highest indexed function variable.  Together the hmax and bindings
; may be used by hl-one-way-unify1 to extend the match.

  (let* ((psubst-lst
          (hl-one-way-unify1
           pat
           (convert-free-vars-to-constants term)
           -1
           nil
           restrictions
           wrld)))
    (cond
     (psubst-lst
      (mv t
          psubst-lst
          (convert-constants-to-free-vars-in-alist-lst
           (decode-psubst-lst psubst-lst wrld))))
     (t (mv nil nil nil)))))

; Notes:

; 1. See the Essay on Incompleteness above concerning our ill-treatment of
; quoted constants.

; 2. In functional-instantiation-notes.lisp I list a bunch of the uses
; of :functional-instance in our regression suite.  Below are some
; trial runs of the HL algorithm derived from the first four examples.
; I have ignored the use of constrained functions in the hyps, e.g.,
; ``pred'' in the first few problems below.  I don't have any good
; ideas about that, yet.

; Also, in the first few examples below, I match on the entire
; conclusion of the rule, as though I were trying to use it in a :by
; hint.  At d I revisit problem c and match only on the left-hand
; side, as though I were rewriting using the theorem about constrained
; functions.  There seem to be a lot more possible matches!

; ---------------------------------------------------------------------------
; Ranking Substitutions

; The lesson learned from these examples is that there are some
; plausible heuristic rules that allow me to discard (or at least give
; low priority to) some of the legal instantions.

; I disfavor substitutions that do not bind all the functional
; variables

; I disfavor substitutions that use identity (projection) lambdas like
; (lambda (...x...) x).  The idea is that if the user saw fit to
; provide a constrained function it is odd not to use it.

; I disfavor substitutions that use lambdas that do not use all their
; formals.  Why did the user provide a formal if it is not used?

; I disfavor substitutions that use lambdas that unnecessarily
; use free vars.  For example, (lambda (x) (cons x A)) when
; (lambda (x) (cons x x)) would work.

; I cannot think of any rational way to codify these heuristics and so
; I just compute scores for each of them, where each score is a
; rational 0<=r<=1, and then sum them.  Perhaps someday I'll weight
; the scores or do other things to distinguish them.

(defun get-fn-vars (alist ans)
  (cond ((endp alist) ans)
        ((and (consp (cdr (car alist)))
              (eq (car (cdr (car alist))) 'lambda))
         (get-fn-vars (cdr alist)
                      (add-to-set-eq (car (car alist)) ans)))
        (t (get-fn-vars (cdr alist) ans))))

(defun get-fn-vars-lst (lst ans)
  (cond ((endp lst) ans)
        (t (get-fn-vars-lst (cdr lst)
                            (get-fn-vars (car lst) ans)))))

(defun number-of-bound-fn-vars (fn-vars alist)
  (cond ((endp fn-vars) 0)
        ((assoc-eq (car fn-vars) alist)
         (+ 1 (number-of-bound-fn-vars (cdr fn-vars) alist)))
        (t (number-of-bound-fn-vars (cdr fn-vars) alist))))

(defun number-of-non-trivial-lambdas (alist)
; A trivial lambda is one that has a variable as a body.
  (cond ((endp alist) 0)
        ((and (consp (cdr (car alist)))
              (eq (car (cdr (car alist))) 'lambda))
         (if (variablep (lambda-body (cdr (car alist))))
             (number-of-non-trivial-lambdas (cdr alist))
           (+ 1 (number-of-non-trivial-lambdas (cdr alist)))))
        (t (number-of-non-trivial-lambdas (cdr alist)))))

(defun number-of-lambdas (alist)
  (cond ((endp alist) 0)
        ((and (consp (cdr (car alist)))
              (eq (car (cdr (car alist))) 'lambda))
         (+ 1 (number-of-lambdas (cdr alist))))
        (t (number-of-lambdas (cdr alist)))))

(defun number-of-used-formals (alist)
  (cond ((endp alist) 0)
        ((and (consp (cdr (car alist)))
              (eq (car (cdr (car alist))) 'lambda))
         (+ (len
             (intersection-eq (lambda-formals (cdr (car alist)))
                              (all-vars (lambda-body (cdr (car alist))))))
            (number-of-used-formals (cdr alist))))
        (t (number-of-used-formals (cdr alist)))))

(defun number-of-formals (alist)
  (cond ((endp alist) 0)
        ((and (consp (cdr (car alist)))
              (eq (car (cdr (car alist))) 'lambda))
         (+ (len (lambda-formals (cdr (car alist))))
            (number-of-formals (cdr alist))))
        (t (number-of-formals (cdr alist)))))

(defun number-of-free-vars (alist)
  (cond ((endp alist) 0)
        ((and (consp (cdr (car alist)))
              (eq (car (cdr (car alist))) 'lambda))
         (+ (len
             (set-difference-eq (all-vars (lambda-body (cdr (car alist))))
                                (lambda-formals (cdr (car alist)))))
            (number-of-free-vars (cdr alist))))
        (t (number-of-free-vars (cdr alist)))))

(defun number-of-vars (alist)
  (cond ((endp alist) 0)
        ((and (consp (cdr (car alist)))
              (eq (car (cdr (car alist))) 'lambda))
         (+ (len (all-vars (lambda-body (cdr (car alist)))))
            (number-of-vars (cdr alist))))
        (t (number-of-vars (cdr alist)))))


(defun rank-mixed-subst (fn-vars alist)

; We compute a rational number that scores alist.  At the moment it is
; just the sum of the several scores.  We add one to each denominator
; to make sure it is not 0.  We add one to each numerator to compensate, e.g.,
; if the number of non-trivial lambdas is equal to the number of lambdas, the
; score is 1.

  (let ((bound-fn-vars (/ (+ 1 (number-of-bound-fn-vars fn-vars alist))
                          (+ 1 (len fn-vars))))
        (non-trivial-lambdas (/ (+ 1 (number-of-non-trivial-lambdas alist))
                                (+ 1 (number-of-lambdas alist))))
        (used-formals (/ (+ 1 (number-of-used-formals alist))
                         (+ 1 (number-of-formals alist))))
        (free-vars (- 1 (/ (+ 1 (number-of-free-vars alist))
                           (+ 1 (number-of-vars alist))))))
    (+ bound-fn-vars
       non-trivial-lambdas
       used-formals
       free-vars)))

(defun rank-mixed-substs (fn-vars lst)
; Pair each alist in lst with its rank, in preparation for sorting.
  (cond ((endp lst) nil)
        (t (cons (cons (rank-mixed-subst fn-vars (car lst))
                       (car lst))
                 (rank-mixed-substs fn-vars (cdr lst))))))

(defun sort-mixed-substs-by-rank (lst)
  (merge-sort-car-> (rank-mixed-substs (get-fn-vars-lst lst nil) lst)))

; ---------------------------------------------------------------------------
; Rewriting

; I am going to implement a general rewrite engine that applies a set of
; ``rules'' ``in all possible ways''.  It is good to understand what I DON'T
; provide.
; (1) While many of the rules are equalities, e.g.,
;     (EQUAL (IF X Y Z) (IF (NOT X) Z Y))
;     I always use them as left-to-right rewriters.  Thus, ``all possible
;     ways'' does not include right-to-left use of the equalities!  If you
;     want that, you should add it as a rule.  The search strategy will
;     handle the looping.

; (2) Some of the rules are essentially metafunctions.  These are hand coded
;     but one could imagine proving them correct.  The metafunctions that are
;     provided are hard-wired in, in the sense that if a rule is
;     (:META FOLD-TO-ISOLATE)
;     then the function name FOLD-TO-ISOLATE must be coded into the apply-rule
;     function.  That is, this is not extensible by the user.

; (3) Since the rules loop or, more generally, do not terminate, there is no
;     absolute sense of ``all possible ways''.  So a counter is provided that
;     limits the number of times we iterate the rewriting process.

; In summary, I have implemented a fairly general ad hoc framework for
; applying a bunch of conflicting rules in all possible combinations
; (bounded by the counter).  But it is not as general as one might
; hope and the user is not allowed to extend it.  It is seen by me as
; a system-developer's tool that lets me easily fiddle with the rules I
; support without having to get into the internals of the search
; strategy again.

; The first :META rule I saw I needed does the following folding:
;  (if p (add1 (LEN (cdr x))) (add2 (LEN (cddr x))))
; is folded into:
;  ((lambda (p z) (if p (add1 z) (add2 z)))
;    p
;    (LEN (if p (cdr x) (cddr x))))
; I call this FOLD-TO-ISOLATE.

; The output has the advantage of having exactly one call of LEN in
; it, allowing the original expression to match with something like
; (tweak$ (LEN (step$ x))).  This metafunction must be supplied with
; the name of the function that is to be isolated.

(mutual-recursion

(defun count-calls (fn term)
  (cond ((variablep term) 0)
        ((fquotep term) 0)
        ((equal fn (ffn-symb term))
         (+ 1 (count-calls-lst fn (fargs term))))
        (t (count-calls-lst fn (fargs term)))))
(defun count-calls-lst (fn args)
  (cond ((endp args) 0)
        (t (+ (count-calls fn (car args))
              (count-calls-lst fn (cdr args)))))))

(mutual-recursion

(defun find-first-call (fn term)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((equal fn (ffn-symb term)) term)
        (t (find-first-call-lst fn (fargs term)))))

(defun find-first-call-lst (fn args)
  (cond ((endp args) nil)
        ((find-first-call fn (car args)))
        (t (find-first-call-lst fn (cdr args))))))

(mutual-recursion

(defun subst-for-call (new-term fn term)
  (cond ((variablep term) term)
        ((fquotep term) term)
        ((equal fn (ffn-symb term)) new-term)
        (t (fcons-term (ffn-symb term)
                       (subst-for-call-lst new-term fn (fargs term))))))
(defun subst-for-call-lst (new-term fn args)
  (cond ((endp args) nil)
        (t (cons (subst-for-call new-term fn (car args))
                 (subst-for-call-lst new-term fn (cdr args)))))))

(defun fold-to-isolate-args (p args1 args2)
  (cond ((endp args1) nil)
        ((equal (car args1) (car args2))
         (cons (car args1)
               (fold-to-isolate-args p (cdr args1) (cdr args2))))
        (t (cons (fcons-term* 'if p (car args1) (car args2))
                 (fold-to-isolate-args p (cdr args1) (cdr args2))))))

(mutual-recursion

(defun no-ifs-governing-call (fn term)
  (cond ((variablep term) t)
        ((fquotep term) t)
        ((equal (ffn-symb term) fn) t)
        ((eq (ffn-symb term) 'IF) nil)
        (t (no-ifs-governing-call-lst fn (fargs term)))))

(defun no-ifs-governing-call-lst (fn args)
  (cond ((endp args) t)
        (t (and (no-ifs-governing-call fn (car args))
                (no-ifs-governing-call-lst fn (cdr args)))))))


(defun fold-to-isolate (fn term)

; Here is an example of this function at work.  If fn is LEN and term
; is
;  (if (evenp n)
;      (binary-+ x (len (cdr x)))
;      (binary-* y (len (cdr z)))))
; then the output (mv t term'), where term' is:
;   ((lambda (y x n len)
;     (if (evenp n)
;         (binary-+ x len)
;         (binary-* y len)))
;     y x n (len (if (evenp n) (cdr x) (cdr z))))

; In the event that such a treatment of term is impossible, this function
; returns (mv nil term).

  (cond ((and fn                         ;;; sometimes fn = nil
              (nvariablep term)
              (not (fquotep term))
              (eq (ffn-symb term) 'IF)
              (equal (count-calls fn (fargn term 2)) 1)
              (equal (count-calls fn (fargn term 3)) 1)
              (no-ifs-governing-call fn (fargn term 2))
              (no-ifs-governing-call fn (fargn term 3)))
         (let* ((p (fargn term 1))
                (tb (fargn term 2))
                (fb (fargn term 3))
                (call1 (find-first-call fn tb))
                (call2 (find-first-call fn fb))
                (var (genvar 'fold-to-isolate
                             (symbol-name fn)
                             nil (all-vars term)))
                (new-body `(if ,p
                               ,(subst-for-call var fn tb)
                             ,(subst-for-call var fn fb)))
                (formals (append (remove1-eq var (all-vars new-body))
                                 (list var)))
                (val (fcons-term fn
                                 (fold-to-isolate-args p
                                                       (fargs call1)
                                                       (fargs call2)))))
           (mv t
               (fcons-term (make-lambda formals new-body)
                           (append (all-but-last formals) (list val))))))
        (t (mv nil term))))

(defun apply-rule (rule term toxic-fnname)

; A rule is either an equality term, (EQUAL lhs rhs), or else a meta
; rule of the form (:META FOLD-TO-ISOLATE).  We return (mv flg
; new-term), where flg indicates whether the rule fired.  No-change
; loser on term.

  (cond
   ((eq (car rule) :META)
    (fold-to-isolate toxic-fnname term))
   (t
    (let ((lhs (fargn rule 1))
          (rhs (fargn rule 2)))
      (mv-let (flg unify-subst)
              (one-way-unify lhs term)
              (cond
               (flg
                (mv t (sublis-var unify-subst rhs)))
               (t (mv nil term))))))))

(defun apply-rules (rules term toxic-fnname ans)

; We apply all the rules to term and union the results into ans.

  (cond
   ((endp rules) ans)
   (t (mv-let (flg new-term)
              (apply-rule (car rules) term toxic-fnname)
              (apply-rules (cdr rules) term toxic-fnname
                           (if flg (add-to-set-equal new-term ans) ans))))))

; We build in the rule
;  (equal (if test (fn ... x ...) (fn ... y ...))
;         (fn ... (if test x y) ...))
; in the general form where illustrated by the special case:
; (equal (if test (foo a x b u) (foo a y b v))
;        (foo a (if test x y) b (if test u v)))

(defun push-ifs-in-if-possible1 (test args1 args2)
  (cond
   ((endp args1) nil)
   ((equal (car args1) (car args2))
    (cons (car args1)
          (push-ifs-in-if-possible1 test (cdr args1) (cdr args2))))
   (t (cons (fcons-term* 'if test (car args1) (car args2))
            (push-ifs-in-if-possible1 test (cdr args1) (cdr args2))))))

(defun some-corresponding-args-are-equal (args1 args2)
  (cond
   ((endp args1) nil)
   ((equal (car args1) (car args2)) t)
   (t (some-corresponding-args-are-equal (cdr args1) (cdr args2)))))

(defun push-ifs-in-if-possible (term)
  (cond
   ((and (nvariablep term)
         (not (fquotep term))
         (eq (ffn-symb term) 'IF)
         (nvariablep (fargn term 2))
         (not (fquotep (fargn term 2)))
         (nvariablep (fargn term 3))
         (not (fquotep (fargn term 3)))
         (equal (ffn-symb (fargn term 2))
                (ffn-symb (fargn term 3)))
         (not (equal (fargn term 2) (fargn term 3)))
         (some-corresponding-args-are-equal (fargs (fargn term 2))
                                            (fargs (fargn term 3))))
    (list
     (cons-term (ffn-symb (fargn term 2))
                (push-ifs-in-if-possible1 (fargn term 1)
                                          (fargs (fargn term 2))
                                          (fargs (fargn term 3))))))
   (t nil)))

(defun apply-rules-lst (rules term-lst toxic-fnname ans)

; We apply all the rules to every term in term-lst and union the
; results into ans.  We act as though there were a rule (equal lhs
; lhs), i.e., the no-op rule that leaves each term unchanged.

  (cond
   ((endp term-lst) ans)
   (t (apply-rules-lst
       rules
       (cdr term-lst)
       toxic-fnname
       (add-to-set-equal (car term-lst)
                         (union-equal
                          (push-ifs-in-if-possible (car term-lst))
                          (apply-rules rules (car term-lst)
                                       toxic-fnname ans)))))))


; The following function, rewrite-in-all-possible-ways, takes a term
; and a list of rules.  It returns a list of terms.  Each term' in the
; output list is obtained from term by applying 0 or more rules to the
; subterms of term.  However, the name is a misnomer because we do not
; really apply rules in ALL possible ways.  Roughly speaking, we do not
; directly rewrite the output of any rule.  Instead, after applying 0 or
; more rules to each argument, we rewrite the calls.  We discuss the
; function after defining it.

(mutual-recursion

(defun rewrite-in-all-possible-ways (term rules toxic-fnname)
  (cond ((variablep term) (list term))
        ((fquotep term) (list term))
        (t (let* ((rewritten-args-bundle
                   (rewrite-in-all-possible-ways-args (fargs term) rules
                                                      toxic-fnname))
                  (temp
                   (all-picks (cons (list (ffn-symb term))
                                    rewritten-args-bundle)
                              nil)))
             (apply-rules-lst rules temp toxic-fnname nil)))))

(defun rewrite-in-all-possible-ways-args (lst rules toxic-fnname)
  (cond ((endp lst) nil)
        (t (cons (rewrite-in-all-possible-ways (car lst) rules toxic-fnname)
                 (rewrite-in-all-possible-ways-args (cdr lst) rules
                                                    toxic-fnname)))))
)

; Discussion.  Consider the following call.

#|(rewrite-in-all-possible-ways '(f (g '1))
                                '((equal (g '1) (g '2))     ; rule-g1
                                  (equal (g '2) (g '3))     ; rule-g2
                                  (equal (f (g '1)) (f '1)) ; rule-f-g1
                                  (equal (f (g '2)) (f '2))); rule-f-g2
                                nil
                                )|#

; We get back four results:

; ((F (G '2))  ; use rule-g1 on (g '1)
;  (F '2)      ; use rule-g1 on (g '1) and then rule-f-g2
;  (F (G '1))  ; use no rules
;  (F '1))     ; use rule-f-g1

; We never used rule-g2 and hence never produced (f (g '3)).  That is
; because we would have had to apply rule-g2 to the immediate output
; of rule-g1.  Instead, we ascended and rewrote the call.

; How then can we rewrite (f (g '1)) to (f (g '3))?  We have to apply
; this process again, possibly on each new term.

#|(rewrite-in-all-possible-ways '(f (g '2))
                                '((equal (g '1) (g '2))      ; rule-g1
                                  (equal (g '2) (g '3))      ; rule-g2
                                  (equal (f (g '1)) (f '1))  ; rule-f-g1
                                  (equal (f (g '2)) (f '2))) ; rule-f-g2
                                nil
                                )|#

; is ((F (G '3)) (F (G '2)) (F '2)), which contains the desired goal.
; Note that it also contains some of the previously produced new terms.

; This discussion leads to the following notion of ``exhaustive
; rewriting'' as codified in eriapw1 below. Since the rules are not
; guaranteed to terminate, we impose an artificial cutoff of n.

; However, before we define the function we introduce a terminating
; condition: we'll stop when we've produced a term that matches a
; given pattern.  That is, we do ``exhaustive'' rewriting to search
; for an instance of a pattern.  We will use 2nd order matching in the
; pattern.

(defun some-term-matches-pattern (pat terms psubst restrictions wrld)
  (if (endp terms)
      nil
    (or (hl-one-way-unify1 pat
                           (convert-free-vars-to-constants (car terms))
                           (car psubst)
                           (cdr psubst)
                           restrictions wrld)
        (some-term-matches-pattern pat (cdr terms) psubst
                                   restrictions wrld))))

(mutual-recursion

; "Eriapw1" stands for "exhaustive rewrite in all possible ways
; (auxiliary)".  It rewrites term with rules, using
; rewrite-in-all-possible-ways, and then rewrites each new term
; recursively until nothing changes.  N limits the number of
; recursions.  Seen, below, contains all the terms that either have
; already been rewritten or that are destined to be rewritten
; (including term itself).  Pat is the pattern we're looking for.
; We stop if and when we find it.

; We return (mv flg ans).  If flg is T then we found a term that
; matches pat and the winning Huet-Lang psubsts describing the matches
; are returned as ans.  If flg is NIL, then we did not find pat and
; ans is the list of all terms generated (seen).

(defun eriapw1 (pat term psubst rules seen n restrictions toxic-fnname wrld)
  (cond
   ((zp n) (mv nil seen))
   (t (let ((new-terms (set-difference-equal
                        (rewrite-in-all-possible-ways term rules toxic-fnname)
                        seen)))
        (cond
         ((endp new-terms) (mv nil seen))
         (t (let ((psubst-lst (some-term-matches-pattern pat new-terms
                                                         psubst
                                                         restrictions wrld)))
              (cond
               (psubst-lst (mv t psubst-lst))
               (t (eriapw1-lst
                   pat
                   new-terms
                   psubst
                   rules
                   seen
                   (- n 1)
                   restrictions
                   toxic-fnname
                   wrld))))))))))

(defun eriapw1-lst (pat term-lst psubst rules seen n
                        restrictions toxic-fnname wrld)

; Apply eriapw1 to every term in term-lst, accumulating the answers
; into seen until we find a match of pat.

  (cond ((endp term-lst) (mv nil seen))
        (t (mv-let (flg ans)
                   (eriapw1 pat
                            (car term-lst)
                            psubst
                            rules
                            (add-to-set-equal
                             (car term-lst)
                             seen)
                            n
                            restrictions
                            toxic-fnname
                            wrld)
; Note:  If flg is t, ans is a psubst-lst; else, ans is a list of terms seen.

                   (cond (flg (mv t ans))
                         (t (eriapw1-lst
                             pat
                             (cdr term-lst)
                             psubst
                             rules
                             ans ;;; <- note we use the new seen here!
                             n
                             restrictions
                             toxic-fnname
                             wrld)))))))
)

; Note that we have built in the rule
; (equal (if test (fn ... x ...) (fn ... y ...))
;        (fn ... (if test x y) ...))
; even though it doesn't appear on the list below!

; The first rule below is rather peculiar but allows us to recognize
; member-equal, for example, as an or of some predicate on successive
; tails.  The complication is that member-equal does not return the
; value of the predicate it uses, namely (equal e (car lst)), but lst
; instead.  This can be fixed by properly understanding the predicate
; it is testing!

(defconst *fixed-rematch-rules*
  '((equal (if (consp lst)
               (if test lst else1)
             else2)
           (if (consp lst)
               (if (if test lst 'nil)
                   (if test lst 'nil)
                 else1)
             else2))
    (equal (endp x) (not (consp x)))

; There are no NOTs in the concrete expression, so the first rule
; below will never fire.  That's why we have commented it out.  There
; are no NOTs in the pattern, so the second rule below will never
; produce a match.  The reason for both of these claims is that we're
; dealing with normalized bodies.

; Ah ha!  The reasoning above is flawed!  The pattern might be (if (h
; x) '1 '2) but the concrete term might be (if (consp a) '2 '1).  If
; we were to fire the second rule below on the concrete term we would
; get (if (not (consp a)) '1 '2).  Then, we could instantiate h to be
; (lambda (v) (not (consp v))) to win.  The only way we can win using
; this rule is that if the NOT which it introduces is sucked up into a
; functional variable.

; I still rule it out!  First, it loops.  Of course, I deal with loops
; and so that is not a killer.  But, second, it slows us down.  I
; think it is better to implement some kind of special hack to allow
; parity swaps inside the functional variable.

;   (equal (if (not x) y z) (if x z y))
;   (equal (if x y z) (if (not x) z y))

; These next three are subsumed by push-ifs-in-if-possible.

;   (equal (if x1 (if x2 y z) (if x3 y z))
;          (if (if x1 x2 x3) y z))
;   (equal (if y1 (if x y2 z) (if x y3 z))
;          (if x (if y1 y2 y3) z))
;   (equal (if z1 (if x y z2) (if x y z3))
;          (if x y (if z1 z2 z3)))

    (equal (if p out1 (if q out2 out3))
           (if (if p 't q) (if p out1 out2) out3))
    (:meta fold-to-isolate)))

(defun fn-rematch-rules-aux1 (v i ispecial vspecial arity)

; Here is an illuminating example of this function.
; (fn-rematch-rules-aux1 'V 1 3 'X 4) = (V1 V2 X V4)

  (cond ((<= i arity)
         (cons (cond ((equal i ispecial)
                      vspecial)
                     (t (packn (list v i))))
               (fn-rematch-rules-aux1 v (+ 1 i) ispecial vspecial arity)))
        (t nil)))

(defun fn-rematch-rules-aux2 (v w i arity)
  (cond ((<= i arity)
         (cons `(IF X ,(packn (list v i)) ,(packn (list w i)))
               (fn-rematch-rules-aux2 v w (+ 1 i) arity)))
        (t nil)))

(defun fn-rematch-rules1 (fn i arity)
  (cond
   ((<= i arity)
    `((equal (if xi
                 (,fn ,@(fn-rematch-rules-aux1 'V 1 i 'YI arity))
               (,fn ,@(fn-rematch-rules-aux1 'V 1 i 'ZI arity)))
             (,fn ,@(fn-rematch-rules-aux1 'V 1 i '(IF XI YI ZI) arity)))
      (equal (if x
                 (,fn ,@(fn-rematch-rules-aux1 'V 1 -1 '? arity))
               (,fn ,@(fn-rematch-rules-aux1 'W 1 -1 '? arity)))
             (,fn ,@(fn-rematch-rules-aux2 'V 'W 1 arity)))
      ,@
      (fn-rematch-rules1 fn (+ 1 i) arity)))
   (t *fixed-rematch-rules*)))

(defun fn-rematch-rules (fn wrld)

; Suppose arity is n.  Then (fn v1 ... vn) is a proper term.  For each
; argument position, i, we will build in the following rules

; [1]
; (equal (if xi (fn v1 ... yi ... vn) (fn v1 ... zi ... vn))
;        (fn v1 ... (if xi yi zi) ... vn))

; [2]
; (equal (if x (fn v1 ... vn) (fn w1 ... wn))
;        (fn (if x v1 w1) ... (if x vn wn)))

; [3]
; (equal (if p (fn v1 ... vn) (if q (fn w1 ... wn) x))
;        (if (if p 't q)
;            (if p (fn v1 ... vn) (fn w1 ... wn))
;            x))

; We literally use the variable symbols shown above!

  (cond ((and (symbolp fn)
              (arity fn wrld))
         (fn-rematch-rules1 fn 1 (arity fn wrld)))
        (t *fixed-rematch-rules*)))

(defun rematch (pat term psubst restrictions toxic-fnname n wrld)

; The name ``rematch'' stems from ``rewrite and match.''  Roughly
; speaking, this function rewrites term in all possible ways using
; rules (to level n) and stops when it finds a term that matches pat.
; We return a psubst list.  If it is is nil, pat was not found.

  (or (hl-one-way-unify1 pat
                         (convert-free-vars-to-constants term)
                         (car psubst)
                         (cdr psubst)
                         restrictions
                         wrld)
      (mv-let (flg ans)
              (eriapw1 pat term
                       psubst
                       (fn-rematch-rules toxic-fnname wrld)
                       (list term) n
                       restrictions
                       toxic-fnname
                       wrld)

; Hack:  If you want to see how many terms are being created, make this
; comment live code and redefine rematch in raw lisp.
;             (print (list 'rematch term '=> (len ans)))

              (cond
               (flg ans)
               (t nil)))))

; FYI  If you do a (rematch 'pat 'term ...) and get back (ans ms1 ms2 ...)
; then you can test it by doing

; `(thm (equal ,(sublis-mixed 'msi 'pat)
;              term))

; and then evaluating the result.

; ---------------------------------------------------------------------------
; Matching through Defuns

; A psubst is said to be ``unfinished'' if there is some binding pair
; with fnp T in it.

; The Plan

; (0) Create an initial list of psubsts by unifying the initial pat
;     and term.  Call this list psubst-pool.
; (1) Pick an unfinished psubst from the pool.  If there are none, return
;     the pool.  Otherwise, let psubst be the chosen unfinished psubst,
;     with functional variable f.  By definition, f is a defined,
;     hereditarily constrained function symbol.
; (2) Convert psusbt to a mixed subst, subst, and recover the binding
;     of f, (lambda (v1...) term).  Note that the formals of the defined
;     function f may be different from (v1 ...).
; (3) Is term a call of a defined function?  If not If not, delete
;     psubst from the psubst-pool and repeat from (1).  Else, term is
;     (g a1...) for some defined g.  Intuitively, the ai involve
;     the vi -- after all, (g a1 ...) is the body of a lambda with
;     local vars (v1...).  However, there may be free vars in the ai
;     and not every vi may be used.
; (4) Let f-formals be the formals of the lambda (not necessarily the
;     formals of f itself!).
; (5) Let f-body be the body of the defined function f, with the
;     formals of f replaced uniformly by f-formals.  Thus, it is now as
;     though f had been defined in the first place with the formals of the
;     lambda.
; (6) Standardize the f-formals away from the bound vars of the
;     psubst.  Call the new ones f-formals'.
; (7) Let f-body1 be the corresponding variant of f-body.  So now it
;     is thought f had been defined with formals, f-formals', that are
;     all free in the current psubst.
; (8) Let g-formals and g-body be the obvious things from the defun of g.
; (9) Instantiate g-body to get g-body1, replacing the formals of
;     g by the actuals, a1... -- after renaming the lambda formals (v1...)
;     used in the (a1...) according to the standardization adopted.
;(10) Compute the list of f-formals' that do not appear in the renamed
;     a'.  Bind them all to 'nil in the psubst and set the DONE
;     flag for the binding of f in that psubst.  Let the new psubst
;     be psubst1.
;(11) Use Huet-Lang to match f-body1 with g-body1, extending psubst.
;     Get back a list of extensions of psubst1.
;(12) Throw out of the extensions the variable bindings of the
;     f-formals'.  This produces extensions1.
;(13) Splice extensions1 into the pool in place of psubst.
;(14) Repeat from 1.

(defun unfinished-binding-pair (bindings)
  (cond ((endp bindings) nil)
        ((eq (cadr (car bindings)) T)
         (car bindings))
        (t (unfinished-binding-pair (cdr bindings)))))

(defun unfinished-psubstp (psubst)
; If psubst is unfinished, return the binding (fn T . term).
  (unfinished-binding-pair (cdr psubst)))

; HLD stands for "HL one way unify through Defuns"

(defun pick-an-unfinished-psubst (pool)
; If there is a psubst in pool that is unfinished, return it.
  (cond ((endp pool) nil)
        ((unfinished-psubstp (car pool)) (car pool))
        (t (pick-an-unfinished-psubst (cdr pool)))))

(defun minimal-genvar-lst (vars avoid-lst)
  (cond ((endp vars) nil)
        (t
         (let* ((old-var (car vars))
                (new-var (if (member-eq old-var avoid-lst)
                             (genvar old-var "V" 1 avoid-lst)
                           old-var)))
           (cons (cons old-var new-var)
                 (minimal-genvar-lst (cdr vars)
                                     (cons new-var avoid-lst)))))))

(defun psubst-variable-domain1 (bindings)
  (cond
   ((endp bindings) nil)
   ((cadr (car bindings)) (psubst-variable-domain1 (cdr bindings)))
   (t (cons (car (car bindings))
            (psubst-variable-domain1 (cdr bindings))))))

(defun psubst-variable-domain (psubst)
  (psubst-variable-domain1 (cdr psubst)))

(defun set-psubst-done1 (fn bindings)
  (cond ((endp bindings) nil)
        ((eq (car (car bindings)) fn)
         (cons (list* fn 'DONE (cddr (car bindings)))
               (cdr bindings)))
        (t (cons (car bindings)
                 (set-psubst-done1 fn (cdr bindings))))))

(defun set-psubst-done (fn psubst)
  (cons (car psubst)
        (set-psubst-done1 fn (cdr psubst))))


(defun splice-out-member (e seg lst)
  (cond
   ((endp lst) nil)
   ((equal e (car lst))
    (append seg (cdr lst)))
   (t (cons (car lst) (splice-out-member e seg (cdr lst))))))

(defun bind-nil1 (vars bindings)
  (cond ((endp vars) bindings)
        (t (cons (list* (car vars) nil *nil*)
                 (bind-nil1 (cdr vars) bindings)))))

(defun bind-nil (vars psubst)

; Bind the vars listed in vars to 'nil in psubst.

  (cons (car psubst) (bind-nil1 vars (cdr psubst))))

(defun delete-var-bindings2 (vars bindings)
  (cond
   ((endp bindings) nil)
   ((and (not (cadr (car bindings)))
         (member-eq (car (car bindings)) vars))
    (delete-var-bindings2 vars (cdr bindings)))
   (t (cons (car bindings)
            (delete-var-bindings2 vars (cdr bindings))))))

(defun delete-var-bindings1 (vars psubst)
  (cons (car psubst)
        (delete-var-bindings2 vars (cdr psubst))))

(defun delete-var-bindings (vars psubst-lst)
  (cond
   ((endp psubst-lst) nil)
   (t (cons (delete-var-bindings1 vars (car psubst-lst))
            (delete-var-bindings vars (cdr psubst-lst))))))

(defun hld-driver (psubst-pool restrictions toxic-fnname n wrld)
  (let ((psubst (pick-an-unfinished-psubst psubst-pool)))
    (cond
     ((not psubst) psubst-pool)
     (t (let* ((binding-pair (unfinished-psubstp psubst))
               (f (car binding-pair))
               (flambda (convert-constants-to-free-vars-in-lambda
                         (cdr (assoc-eq f
                                        (decode-psubst (cdr psubst) wrld)))))
               (term (lambda-body flambda)))
          (cond ((and (nvariablep term)
                      (not (fquotep term))
                      (not (flambda-applicationp term))
                      (body (ffn-symb term) nil wrld))
                 (let* ((f-formals (lambda-formals flambda))
                        (f-body (subcor-var (formals f wrld)
                                            f-formals
                                            (body f t wrld)))
                        (g (ffn-symb term))
                        (g-formals (formals g wrld))
                        (g-body (body g t wrld))
                        (g-actuals (fargs term))
                        (f-formals-renaming
                         (minimal-genvar-lst f-formals
                                             (psubst-variable-domain psubst)))
                        (f-body1
                         (sublis-var f-formals-renaming
                                     f-body))
                        (g-body1
                         (subcor-var g-formals
                                     (sublis-var-lst f-formals-renaming
                                                     g-actuals)
                                     g-body))
                        (psubst1
                         (bind-nil (set-difference-eq
                                    (strip-cdrs f-formals-renaming)
                                    (all-vars g-body1))
                                   (set-psubst-done f psubst)))
                        (extensions
                         (rematch f-body1
                                  g-body1
                                  psubst1
                                  restrictions toxic-fnname n
                                  wrld))
                        (extensions1
                         (delete-var-bindings (strip-cdrs f-formals-renaming)
                                              extensions))
                        (new-psubst-pool
                         (splice-out-member psubst
                                            extensions1
                                            psubst-pool)))
                   (hld-driver new-psubst-pool restrictions
                               toxic-fnname n wrld)))
                (t (hld-driver (remove1-equal psubst psubst-pool)
                               restrictions toxic-fnname n wrld))))))))

; The draconian restriction enforced by functional instantiation,
; concerning the avoidance of capture, means that some of the
; ``solutions'' found by hld-driver are not really solutions.  These
; non-solutions have to be filtered out.  We develop that filtering
; code below and then use it in the definition of the top-level hld.

; But let us explain.  Consider map-h and bumper1, as defined below.

; (defun map-h (x)
;  (if (endp x)
;       nil
;     (cons (h (car x)) (map-h (cdr x)))))

; (defun bumper1 (u v w)
;  (if (endp u)
;      nil
;    (cons (+ (* w (car u)) v)
;          (bumper1 (cdr u) v w))))

; where h is simply constrained.

; If you run

; (hld '(map-h x) '(bumper1 u v w) '(-1 . nil) nil nil 1 (w state))

; after modifying hld so as not to to filter out non-solutions, you
; get two solutions.  In the first, (H V1) is mapped to (+ (* W V1)
; V).  In the second, (H V1) is mapped to (+ (* W (CAR X)) V).  The
; second "solution" is not a solution!

; Here is the second "solution":

;  ((H . (LAMBDA (V1)
;                (BINARY-+ (BINARY-* W (CAR X)) V)))
;   (X . U)
;   (MAP-H . (LAMBDA (X) (BUMPER1 X V W))))

; In particular, its application to the defun of map-h fails to
; produce a theorem because it introduces a free X and is being
; applied to constraint, namely the defun of map-h, in which X
; appears.  The draconian restriction on functional substitution
; forces a renaming of that free X to, say, V2.  We then must prove
; the following functional instance of map-h, which is not a theorem:

; (EQUAL (BUMPER1 X V W)                         [lhs]
;        (AND (NOT (ENDP X))                     [rhs]
;             (CONS (+ (* W (CAR V2)) V)
;                   (BUMPER1 (CDR X) V W))))

; We renamed X to V2 because X was mentioned in the formula (the defun
; of map-h) being instantiated.  But suppose the formula had mentioned
; W instead (i.e., suppose the formal of map-h were W).  Then we would
; have renamed the free Ws to V2.  But W is among the free vars of
; MAP-H, and so it is ``appropriate'' for H to refer to it.  Put
; another way, we will end up with V2 in both [lhs] and [rhs].

; This actually raises its head in a worse way.  Can you instantiate

; (defun generic-run (s n)
;   (if (zp n)
;       s
;     (generic-run (h s) (- n 1))))

; to be

; (defun make-var-lst1 (root sym n acc)
;   (if (zp n)
;       acc
;     (make-var-lst1 root sym (1- n)
;                    (cons (intern-in-package-of-symbol
;                           (coerce
;                            (append root
;                                    (explode-nonnegative-integer (1- n) nil))
;                            'string)
;                           sym)
;                          acc))))

; You may think you can instantiate h with
;  (lambda (s)
;    (intern-in-package-of-symbol
;     (coerce
;      (append root
;              (explode-nonnegative-integer (1- n) nil))
;      'string)
;     sym))

; (which makes h ignore its argument s and instead introduce a free n)
; and this, indeed, seems to work until you discover the draconian restriction,
; which forces you to renames the free N, to say V1, to avoid capture.

; Think of this as a programmer might: Can h be defined as a function
; so that generic-run does the same thing as make-var-lst1?  Answer:
; no.  h takes s as an argument and if it ignores s then h must be a
; constant function.  And any instantiation of generic-run with a
; constant h will produce a function that returns a monotonous list
; (of whatever constant h returns).  But make-var-lst1 is not
; monotonous.

(defun appropriate-lambda-free-varsp1 (fn fns fn-free-vars fn-alist)

; Fn is a defined, hereditarily constrained function symbol bound in
; fn-alist, which is a functional substitution binding names to lambda
; expressions.  Fn-free-vars is the list of free vars of the binding
; of fn.  Fns is a list of all the hereditarily constrained functions
; reachable from fn (including fn), i.e., the value of the
; hereditarily-constrained-fnnames property of fn.  We check that for
; every h in fns (except fn), h is bound in fn-alist and the free vars
; of the binding of h are a subset of fn-free-vars.  If all the subset
; checks succeed, we say fn-alist is ``appropriate'' and return t.
; See appropriate-lambda-free-varsp for an explanation of this concept.

  (cond
   ((endp fns) t)
   ((eq fn (car fns))
    (appropriate-lambda-free-varsp1 fn (cdr fns) fn-free-vars fn-alist))
   (t (let ((pair (assoc-eq (car fns) fn-alist)))
        (and pair
             (subsetp-eq
              (set-difference-eq (all-vars (lambda-body (cdr pair)))
                                 (lambda-formals (cdr pair)))
              fn-free-vars)
             (appropriate-lambda-free-varsp1 fn (cdr fns)
                                             fn-free-vars fn-alist))))))

(defun appropriate-lambda-free-varsp2 (temp fn-alist wrld)

; Fn-alist is a functional substitution binding fnnames to lambda
; expressions.  Initially temp is fn-alist and we're sweeping down it.
; We check that every defined hereditarily constrained function fn
; bound in fn-alist has the property that every hereditarily
; constrained function reachable from it is bound in fn-alist to a
; lambda with no free-vars other than those in the binding of fn.  See
; appropriate-lambda-free-varsp for an explanation of this concept.

  (cond
   ((endp temp) t)
   (t (let* ((fn (car (car temp)))
             (fn-lambda (cdr (car temp)))
             (fns (getprop fn 'hereditarily-constrained-fnnames nil
                           'current-acl2-world wrld)))
        (cond
         ((and (consp fns)
               (cdr fns))

; Fn is a defined hereditarily constrained function symbol.

      (and (appropriate-lambda-free-varsp1
            fn
            fns
            (set-difference-eq (all-vars (lambda-body fn-lambda))
                               (lambda-formals fn-lambda))
            fn-alist)
           (appropriate-lambda-free-varsp2 (cdr temp) fn-alist wrld)))
         (t

; Fn is an undefined constrained function, so we skip it.

          (appropriate-lambda-free-varsp2 (cdr temp) fn-alist wrld)))))))

(defun appropriate-lambda-free-varsp (mixed-subst wrld)

; We say a mixed substitution is ``appropriate'' (with respect to its
; use of free vars) if, for every defined hereditarily constrained
; function symbol fn bound in its functional part, every hereditarily
; constrained function h reachable from the definition of fn is bound
; in the functional part of mixed-subst and the free vars of the
; binding are a subset of the free vars of the binding of fn.

; This concept is sufficient to avoid censor by the draconian
; restriction explained in rename-free-vars-in-fn-substitution,
; whereby functional substitutions are not allowed to introduce into a
; theorem or constraint any variable that might be captured.

; Note: It is important to strip out the var bindings (instead of
; trying to do it on the fly) since we assoc-eq for fn and could
; otherwise find a variable binding for the var of the same name.

  (mv-let (var-alist fn-alist)
          (strip-mixed-subst mixed-subst)
          (declare (ignore var-alist))
          (appropriate-lambda-free-varsp2 fn-alist fn-alist wrld)))

(defun collect-appropriate-lambda-free-vars-lst (alist-lst wrld)
  (cond
   ((endp alist-lst) nil)
   ((appropriate-lambda-free-varsp (car alist-lst) wrld)
    (cons (car alist-lst)
          (collect-appropriate-lambda-free-vars-lst (cdr alist-lst) wrld)))
   (t (collect-appropriate-lambda-free-vars-lst (cdr alist-lst) wrld))))

; Now I develop the code to convert a pair of substitutions in
; translated user-level format, one being a var-to-term substitution
; and the other being a functional substitution, to the form of a
; psubst.

(defun convert-var-alist-to-binding-pairs (var-alist)
  (cond ((endp var-alist) nil)
        (t (cons (list* (car (car var-alist))
                        nil
                        (convert-free-vars-to-constants
                         (cdr (car var-alist))))
                 (convert-var-alist-to-binding-pairs (cdr var-alist))))))

(defun formal-to-natp (var formals i)
  (cond ((endp formals) nil)
        ((eq var (car formals)) i)
        (t (formal-to-natp var (cdr formals) (+ 1 i)))))

(mutual-recursion

(defun convert-lambda-to-pseudo-term (formals term)

; To every var in formals we assign a natural number, successively
; from 1 in the order that they occur in formals.  We copy term and
; replace every formal by the corresponding natural and every other
; variable by a :constant.  Thus, if formals is (x y) and term is (foo
; x y z), we return (foo 1 2 (:constant z)).

  (cond
   ((variablep term)
    (let ((n (formal-to-natp term formals 1)))
      (if n n (list :constant term))))
   ((fquotep term) term)

; Note that if the term contains a lambda application, we ignore it!
; That is, we leave lambdas in the term and they get treated as
; function ``symbols,'' i.e., we don't do any fancy matching of them.

   (t (fcons-term (ffn-symb term)
                  (convert-lambda-to-pseudo-term-lst formals (fargs term))))))

(defun convert-lambda-to-pseudo-term-lst (formals args)
  (cond ((endp args) nil)
        (t (cons (convert-lambda-to-pseudo-term formals (car args))
                 (convert-lambda-to-pseudo-term-lst formals (cdr args))))))

)

(defun convert-fn-alist-to-binding-pairs (fn-alist wrld)
  (cond ((endp fn-alist) nil)
        (t (let* ((fn (car (car fn-alist)))
                  (fnp (initial-fnp fn wrld))
                  (gn (cdr (car fn-alist)))
                  (lambda-formals
                   (if (symbolp gn) (formals gn wrld) (lambda-formals gn)))
                  (lambda-body
                   (if (symbolp gn)
                       (fcons-term gn lambda-formals)
                     (lambda-body gn))))
           (cons (list* fn
                        fnp
                        (convert-lambda-to-pseudo-term lambda-formals
                                                       lambda-body))
                 (convert-fn-alist-to-binding-pairs (cdr fn-alist) wrld))))))

(defun convert-var-and-fn-alists-to-psubst (var-alist fn-alist wrld)

; Var-alist is a list of pairs, (var . term), and fn-alist is a list
; of pairs (fnsymb . fn), where term is a translated term and fn is
; either a function symbol or a translated lambda expression.  We must
; convert the lambda expressions to the psubst form.  For example,
; (lambda (x) (cons x (cons y 'nil))) must become (cons 1 (cons
; (:constant y) 'nil))

  (cons -1
        (append (convert-var-alist-to-binding-pairs var-alist)
                (convert-fn-alist-to-binding-pairs fn-alist wrld))))

; So here is the top-level function.

(defun hld (pat term psubst0 restrictions toxic-fnname n wrld)

; Unify pat and term and then do each psubst until they're all DONE.
; The unification must extend psubst0.  Convert each of the unifying
; extensions to mixed substitutions, filter out the inappropriate ones
; and sort them by rank.

; Note: After decoding the psubsts into mixed substitutions,
; duplications may be present.  However, in the one case I looked at,

; (hld '(generic-exists x) '(member x l) nil nil nil 1 (w state))

; where (defun generic-exists (x) (if (endp x) nil (or (h x)
; (generic-exists (cdr x))))), exact duplications are not present
; among the psubsts.  It just happens that some distinct psubsts
; decode into the same mixed substs.  I suspect this is the common
; case so I'll remove duplicates after decoding.  Of course, removing
; them on-the-fly would reduce the number of combinations we consider
; -- but it could be that incomplete psubsts that decode to the same
; mixed subst might be extensible in different ways.

  (let ((psubst-pool
         (rematch pat term psubst0 restrictions toxic-fnname n wrld)))
    (sort-mixed-substs-by-rank
     (remove-duplicates-equal
      (collect-appropriate-lambda-free-vars-lst
       (convert-constants-to-free-vars-in-alist-lst
        (decode-psubst-lst
         (hld-driver psubst-pool restrictions toxic-fnname n wrld)
         wrld))
       wrld)))))


; ---------------------------------------------------------------------------
; Producing Instantiations and Functional Instantiations

(defun extract-mixed-subst-functional-part (alist)
  (cond
   ((endp alist) nil)
   ((and (consp (cdr (car alist)))
         (eq (car (cdr (car alist))) 'LAMBDA))
    (cons (list (car (car alist))
                (cdr (car alist)))
          (extract-mixed-subst-functional-part (cdr alist))))
   (t (extract-mixed-subst-functional-part (cdr alist)))))

(defun extract-mixed-subst-variable-part (alist)
  (cond
   ((endp alist) nil)
   ((and (consp (cdr (car alist)))
         (eq (car (cdr (car alist))) 'LAMBDA))
    (extract-mixed-subst-variable-part (cdr alist)))
   (t (cons (list (car (car alist))
                  (cdr (car alist)))
            (extract-mixed-subst-variable-part (cdr alist))))))

(defun convert-mixed-substs-to-use-hints (name mixed-substs)
  (cond
   ((endp mixed-substs) nil)
   (t (cons `(:INSTANCE
              (:FUNCTIONAL-INSTANCE ,name
                                    ,@(extract-mixed-subst-functional-part
                                       (car mixed-substs)))
              ,@(extract-mixed-subst-variable-part
                 (car mixed-substs)))
            (convert-mixed-substs-to-use-hints name (cdr mixed-substs))))))

; This function doesn't filter.

(defun auto-functional-instantiate-fn (name term wrld)
  (let* ((thm (getprop name 'theorem nil 'current-acl2-world wrld))
         (concl (case-match thm
                            (('IMPLIES & ('EQUAL lhs &))
                             lhs)
                            (('IMPLIES & ('IFF lhs &))
                             lhs)
                            (('IMPLIES & concl)
                             concl)
                            (('EQUAL lhs &)
                             lhs)
                            (('IFF lhs &)
                             lhs)
                            (& thm)))
         (mixed-substs (hld concl term nil nil nil 5 wrld)))
    (convert-mixed-substs-to-use-hints name
                                       mixed-substs)))


(mutual-recursion

(defun hereditarily-constrained-fnnames (term wrld ans)
  (cond
   ((variablep term) ans)
   ((fquotep term) ans)
   ((flambdap (ffn-symb term))
    (hereditarily-constrained-fnnames
     (lambda-body (ffn-symb term))
     wrld
     (hereditarily-constrained-fnnames-lst (fargs term) wrld ans)))
   ((cdr (getprop (ffn-symb term)
                  'hereditarily-constrained-fnnames
                  nil
                  'current-acl2-world
                  wrld))

; This function symbol is a DEFINED hereditarily constrained function.

    (hereditarily-constrained-fnnames-lst (fargs term) wrld
                                          (add-to-set-eq (ffn-symb term) ans)))
   (t (hereditarily-constrained-fnnames-lst (fargs term) wrld ans))))

(defun hereditarily-constrained-fnnames-lst (lst wrld ans)
  (cond ((endp lst) ans)
        (t (hereditarily-constrained-fnnames-lst
            (cdr lst) wrld
            (hereditarily-constrained-fnnames (car lst) wrld ans))))))

; We are about to start computing a functional substitution.  We
; enforce a draconian rule regarding the use of free vars in such
; substitutions.  We need to massage our substitution accordingly and
; we do it with rename-free-vars-in-fn-substitution, a few functions
; below.

(mutual-recursion

(defun sublis-var-free (bound-vars alist term)

; Bound-vars is a list of variables and alist is a substitution on
; variables.  Term is a term, except that it may contain lambda's
; containing free vars.  We treat bound-vars as bound in it
; and all other vars as free.  We replace the free vars in term as
; specified by alist.

  (cond ((variablep term)
         (cond ((member-eq term bound-vars) term)
               (t (let ((pair (assoc-eq term alist)))
                    (if pair (cdr pair) term)))))
        ((fquotep term) term)
        ((flambdap (ffn-symb term))
         (fcons-term (make-lambda (lambda-formals (ffn-symb term))
                                  (sublis-var-free
                                   (append (lambda-formals (ffn-symb term))
                                           bound-vars)
                                   alist
                                   (lambda-body (ffn-symb term))))
                     (sublis-var-free-lst bound-vars alist (fargs term))))
        (t (fcons-term (ffn-symb term)
                       (sublis-var-free-lst bound-vars alist (fargs term))))))

(defun sublis-var-free-lst (bound-vars alist lst)
  (cond ((endp lst) nil)
        (t (cons (sublis-var-free bound-vars alist (car lst))
                 (sublis-var-free-lst bound-vars alist (cdr lst))))))
)

(defun rename-free-vars-in-fn-substitution1 (renaming alist)

; Renaming is an alist pairing variables to variables, i.e., v might
; be mapped to u as with (v . u); alist is a functional substitution
; pairing function symbols to lambda expressions.  We apply renaming
; to each lambda expression, replacing free occurrences only.  I.e.,
; we will replace the free occurrences of each v with u.

  (cond
   ((endp alist) nil)
   (t (cons (cons (car (car alist))
                  (make-lambda (lambda-formals (cdr (car alist)))
                               (sublis-var-free
                                (lambda-formals (cdr (car alist)))
                                renaming
                                (lambda-body (cdr (car alist))))))
            (rename-free-vars-in-fn-substitution1 renaming (cdr alist))))))

(mutual-recursion

(defun all-bound-vars (term ans)

; We return a list containing all the variables used in lambda formals
; in term.

  (cond
   ((variablep term) ans)
   ((fquotep term) ans)
   ((flambdap (ffn-symb term))
    (all-bound-vars (lambda-body (ffn-symb term))
                    (all-bound-vars-lst (fargs term)
                                        (union-eq
                                         (lambda-formals (ffn-symb term))
                                         ans))))
   (t (all-bound-vars-lst (fargs term) ans))))

(defun all-bound-vars-lst (lst ans)
  (cond ((endp lst) ans)
        (t (all-bound-vars-lst (cdr lst)
                               (all-bound-vars (car lst) ans)))))
)

(defun all-bound-vars-alist (alist ans)

; Alist is a functional substitution alist pairing function symbols
; to lambda expressions.

  (cond ((endp alist) ans)
        (t (all-bound-vars-alist (cdr alist)
                                 (all-bound-vars
                                  (lambda-body (cdr (car alist)))
                                  (union-eq (lambda-formals (cdr (car alist)))
                                            ans))))))

(mutual-recursion ; from ACL2 Version_3.0

(defun free-or-bound-vars (term ans)
  (cond ((variablep term) (add-to-set-eq term ans))
        ((fquotep term) ans)
        ((flambda-applicationp term)
         (free-or-bound-vars
          (lambda-body (ffn-symb term))
          (free-or-bound-vars-lst (fargs term)
                                  (union-eq (lambda-formals (ffn-symb term))
                                            ans))))
        (t (free-or-bound-vars-lst (fargs term) ans))))

(defun free-or-bound-vars-lst (terms ans)
  (cond ((null terms) ans)
        (t (free-or-bound-vars-lst
            (cdr terms)
            (free-or-bound-vars (car terms) ans)))))

)

(defun lambda-free-vars (alist) ; from ACL2 Version_3.0

; We compute the free variables occuring the the lambda expressions in
; the range of the translated functional substitution alist.

  (cond ((null alist) nil)
        ((flambdap (cdar alist))
         (union-eq (set-difference-eq (all-vars (lambda-body (cdar alist)))
                                      (lambda-formals (cdar alist)))
                   (lambda-free-vars (cdr alist))))
        (t (lambda-free-vars (cdr alist)))))

(defun rename-free-vars-in-fn-substitution (thm alist wrld)

; Let thm be a term we will functionally instantiate with the
; functional substitution alist.  There is a draconian restriction on
; such instantiations, described in the following error message:

; ACL2 Error in ...: Your functional substitution contains one or more
; free occurrences of the variable X in its range.  We enforce a
; draconian rule to avoid ``capturing'' such variables: if a
; substitution contains a free variable v in its range then we do not
; permit the substitution to be applied to any term that uses v as a
; variable symbol (whether freely or within a lambda or let
; binding). ... You must therefore change your functional substitution
; so that it stays clear of all the variables used in the target
; formula and the corresponding constraints.

; This function massages alist to permit its legal use.  Operationally,
; we compute four intermediate results:

; (a) avoid: the list of all variables used in any way in
;     thm, the constraints generated by applying alist, or bound
;     in alist; the last source of variables was sort of surprising:
;     suppose the alist contains (lambda (v1) (foo x v1)); then we
;     must rename x; but we cannot rename x to v1 or it will get
;     captured;
; (b) free: the list of all variables used freely in any
;     lambda expression in alist;
; (c) renaming: an alist pairing each v in free with a new variable
;     u, not occurring in avoid; when possible we allow v to be
;     "renamed" to itself, but this means our alist will have the
;     pair (v . v) in it;
; (d) unrenaming-substitution: this is like the inverse to renaming
;     except that instead of containing pairs (u . v) it contains
;     doublets (u v) as is required in the instantiation hint
;     that replaces the new u's by the originally requested v's,
;     (:instantiate ... (u v) ...); noop doublets like (u u) may
;     appear;
; (e) renamed-alist: the result of applying renaming to the given
;     functional substitution alist, replacing each FREE occurrence of v
;     by u; note that there may be bound occurrences of v, which we leave
;     untouched;

; We return (mv renamed-alist unrenaming-substitution).

  (mv-let
   (new-constraints new-event-names new-new-entries)
   (relevant-constraints thm alist nil wrld)
   (declare (ignore new-event-names new-new-entries))
   (let* ((avoid (union-eq
                  (free-or-bound-vars-lst (cons thm new-constraints) nil)
                  (all-bound-vars-alist alist nil)))
          (free (lambda-free-vars alist))
          (renaming (minimal-genvar-lst free avoid))
          (unrenaming-substitution
           (pairlis$ (strip-cdrs renaming)
                     (pairlis-x2 (strip-cars renaming) nil)))
          (renamed-alist
           (rename-free-vars-in-fn-substitution1 renaming alist)))
     (mv renamed-alist unrenaming-substitution))))


(set-state-ok t)

; Next, I define a command, called definst (for define instance), that
; is sort of like a new event, that derives a new theorem from an old
; one by automatically functionally instantiating it for a given
; concrete function.  This works only for very special cases.  The new
; command is not an event but currently generates an event, so I can
; play with it without messing with the very complicated protocol for
; adding a new event form.  Two example calls of definst are shown
; below.  After each we give a equivalent event.

; (definst map-h-append bumper)

; is the same as

; (defthm map-h-append[bumper]
;   <map-h-append/mixed-subst>
;   :hints
;   (("Goal" :use ((:instance
;                   (:functional-instance map-h-append <decoded mixed-subst>)))
;            :do-not-induct t
;            <other Goal hints>)
;    <other hints>))

; The other option is

; (definst map-h-append ((x a) (map-h (lambda (x) ...)) (h (lambda (x) ...))))

; which is like the first example, but the mixed substitution is specified by
; the user instead of being computed.

; Except for the first two, the arguments of definst are the same as
; for defthm.  At the moment I do not try to merge the :hints in rest
; with the one I generate.

(defun definst-fn (rootname args rest state)
  (let ((wrld (w state)))
    (cond
     ((and (symbolp rootname)
           (getprop rootname 'theorem nil 'current-acl2-world wrld))
      (let* ((ctx (cons 'definst rootname))
             (thm (getprop rootname 'theorem nil 'current-acl2-world wrld))
             (fns (hereditarily-constrained-fnnames thm wrld nil))

; These next bindings may be nil until we finish certain checks.
; But it is nice to give them sensible names.

            (hfn (car fns))  ; the defined hereditarily constrained fn
            (cfn args)       ; the concrete fn
            )
        (cond
         ((and (consp fns)
               (null (cdr fns)))
          (er-let*
            ((mixed-subst
              (cond
               ((and (symbolp args)
                     (body args t wrld))
                (let* ((ans (hld (fcons-term hfn (formals hfn wrld))
                                 (fcons-term cfn (formals cfn wrld))
                                 '(-1 . nil) ; psubst0
                                 nil
                                 nil
                                 1
                                 (w state)))
                       (subst
                        (cdr ; the cdr removes the score
                         (car ans))))
                  (cond
                   (ans
                    (mv-let (var-alist fn-alist)
                            (strip-mixed-subst subst)
                            (declare (ignore var-alist))
                            (mv-let (renamed-fn-alist inverse-subst)
                                    (rename-free-vars-in-fn-substitution
                                     thm fn-alist wrld)
                                    (declare (ignore inverse-subst))
                                    (value renamed-fn-alist))))
                   (t (er soft ctx
                          "No plausible instantiation was found to ~
                            match the defined hereditarily constrained ~
                            function ~x0 to the concrete function ~x1."
                          hfn cfn)))))
               ((symbol-alistp args)

; We do not know for sure that args is a well-formed mixed
; substitution.  Technically, it probably ought to be translated.  But
; since we're just going to plug it in and generate an event, we'll
; assume that ill-formedness will be detected eventually.

                (value args))
               (t (er soft ctx
                      "The second argument of definst must be either ~
                       a defined function symbol or a mixed substitution, ~
                       i.e., an alist pairing symbols to terms, function ~
                       symbols, or lambda expressions.")))))
            (let ((goal-thm (sublis-mixed mixed-subst thm))

; When the substitution is computed by us, there is no variable part.
; So the :INSTANCE wrapper below is trivial.  But when the specifies a
; substitution we might as well allow a variable part.

                  (use-hint `(:INSTANCE
                              (:FUNCTIONAL-INSTANCE
                               ,rootname
                               ,@(extract-mixed-subst-functional-part
                                  mixed-subst))
                              ,@(extract-mixed-subst-variable-part
                                 mixed-subst)))
                  (new-name (packn `(,rootname "-" ,cfn))))
              (value
               `(defthm ,new-name ,goal-thm
                  :hints
                  (("Goal" :use (,use-hint) :do-not-induct t))
                  ,@rest)))))
         (t (er soft ctx
                "The first argument to definst must be the name ~
                 of a theorem involving exactly one defined ~
                 hereditarily constrained function.  But ~x0 has ~x1."
                rootname
                (len fns))))))
     (t (er soft 'definst
            "The first argument to definst must be a symbol ~
             naming a theorem and ~x0 is not."
            rootname)))))

(defmacro definst (rootname args &rest rest)
  `(make-event (definst-fn ',rootname ',args ',rest state)))

