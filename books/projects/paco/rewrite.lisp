(in-package "PACO")

; Next we develop clausify, the function that reduces an IF-expression
; to a set of clauses.

; The basic idea here is to normalize the term and then walk the
; branches that terminate in non-T, accumulating literals.

; For example,
; (if p
;     (if q T r)
;   (if s NIL T))
; generates ((P (NOT S)) ((NOT P) Q R)) which is equivalent to
; (implies (not P) (not S))
; and
; (implies (and P (not Q)) R).

; The ACL2 version of clausify is complicated by the fact that it
; avoids IF-normalization.  It compiles the term into a program for a
; certain abstract machine and then explores all paths through the
; program.  This makes its space-behavior linear in the size of the
; term, whereas the Paco function is exponential.

(defun strip-branches (term clause clauses)

; Term is in IF-normal form.  All terminal literals are T, NIL, or
; function applications.  No branch terminating in NIL is
; contradictory.

  (cond ((variablep term)
         (cons (revappend (cons term clause) nil) clauses))
        ((fquotep term)
         (cond ((equal term *t*) clauses)
               (t (cons (revappend clause nil) clauses))))
        ((eq (ffn-symb term) 'IF)
         (let* ((test (fargn term 1))
                (clauses (strip-branches (fargn term 2)
                                         (cons (dumb-negate-lit test) clause)
                                         clauses)))
           (strip-branches (fargn term 3)
                           (cons test clause)
                           clauses)))
        (t (cons (revappend (cons term clause) nil) clauses))))

(defun clausify (term ens wrld)
  (strip-branches (normalize term t nil ens wrld) nil nil))

(defun if-tautologyp (term ens wrld)

; The main application of this function is to determine whether a
; rewritten hypothesis is a tautology.  For that reason, we do not
; expand non-rec fns in term.  Thus, we do not recognize certain
; common tautologies, like (IF P 'T (NOT P)), while we would if we
; expanded the NOT.

  (equal (normalize term t nil ens wrld) *t*))

(mutual-recursion

(defun expand-some-non-rec-fns (fns term wrld)
  (cond ((variablep term) term)
        ((fquotep term) term)
        (t (let ((args (expand-some-non-rec-fns-lst fns (fargs term) wrld)))
             (cond ((member-equal (ffn-symb term) fns)
                    (subcor-var (formals (ffn-symb term) wrld)
                                args
                                (body (ffn-symb term) t wrld)))
                   (t (cons-term (ffn-symb term) args)))))))

(defun expand-some-non-rec-fns-lst (fns lst wrld)
  (cond ((endp lst) nil)
        (t (cons (expand-some-non-rec-fns fns (car lst) wrld)
                 (expand-some-non-rec-fns-lst fns (cdr lst) wrld)))))

)

; We now begin the development of the rewriter itself.

(defun smallest-term (term terms)

; Return the smallest term in (cons term terms), under term-order.

  (cond ((endp terms) term)
        ((term-order (car terms) term) (smallest-term (car terms) (cdr terms)))
        (t (smallest-term term (cdr terms)))))

(defun find-smallest-equal-term (term type-alist eterms)
  (cond
   ((endp type-alist)
    (smallest-term term eterms))
   ((and (ts= (cdr (car type-alist)) *ts-t*)
         (nvariablep (car (car type-alist)))
         (eq (ffn-symb (car (car type-alist))) 'EQUAL))
    (let ((arg1 (fargn (car (car type-alist)) 1))
          (arg2 (fargn (car (car type-alist)) 2)))
      (cond
       ((equal term arg1)
        (find-smallest-equal-term term (cdr type-alist) (cons arg2 eterms)))
       ((equal term arg2)
        (find-smallest-equal-term term (cdr type-alist) (cons arg1 eterms)))
       ((member-equal arg1 eterms)
        (find-smallest-equal-term term (cdr type-alist) (cons arg2 eterms)))
       ((member-equal arg2 eterms)
        (find-smallest-equal-term term (cdr type-alist) (cons arg1 eterms)))
       (t (find-smallest-equal-term term (cdr type-alist) eterms)))))
   (t (find-smallest-equal-term term (cdr type-alist) eterms))))

(defun rewrite-solidify (term type-alist iff-flg ens wrld)

; We simplify term wrt type-alist.  In particular, if term is known to
; be in a singleton type-set, we return the corresponding constant
; (reduced mod iff-flg).  In addition, if term is equated to a series
; of other terms, we return the smallest (in term-order).  The
; type-set for all the equivalent terms should be the same.

  (cond
   ((quotep term)
    (cond ((equal term *nil*) *nil*)
          (iff-flg *t*)
          (t term)))
   (t (let ((ts (type-set term type-alist nil ens wrld *type-set-nnn*)))
        (cond
         ((ts= ts *ts-t*) *t*)
         ((ts= ts *ts-nil*) *nil*)
         ((and iff-flg (not (ts-intersectp ts *ts-nil*))) *t*)
         ((ts= ts *ts-zero*) *0*)
         (t (find-smallest-equal-term term type-alist nil)))))))

(defun loop-stopperp-rec (loop-stopper unify-subst)

; Only call this at the top level when loop-stopper is non-nil.

  (cond
   ((endp loop-stopper) nil)
   (t
    (let ((pre (cdr (assoc-eq (car (car loop-stopper)) unify-subst)))
          (post (cdr (assoc-eq (cadr (car loop-stopper)) unify-subst))))
      (cond
       ((equal pre post)
        (loop-stopperp-rec (cdr loop-stopper) unify-subst))
       (t (term-order post pre)))))))

(defun loop-stopperp (loop-stopper unify-subst)
  (or (null loop-stopper)
      (loop-stopperp-rec loop-stopper unify-subst)))

(defrec rewrite-rule ((nume . hyps)
                      (equiv lhs . rhs)
                      subclass . heuristic-info))

; Hyps is a list of terms, equiv is EQUAL or IFF, lhs and rhs are
; terms.  The presence of such a rule means (implies hyps (equiv lhs
; rhs)) is a theorem.  Subclass is either:

; 'backchain - the traditional rewrite rule.  In this case, :heuristic-info is
;   the loop-stopper for the rule: a list of elements of the form (x . y),
;   indicating that in replacing lhs by rhs (the binding of) y moves forward to
;   the spot occupied by (the binding of) x, and that x and y only appear on
;   the left-hand side as arguments to functions in fns.  Thus, to prevent
;   loops we adopt the heuristic convention of replacing lhs by rhs only if
;   there exists a pair (x . y) such that the binding of y is smaller than
;   that of x and all earlier pairs have equal bindings.

; 'definition - a rule implementing a non-abbreviational definitional
;   equation.  In this case :heuristic-info is the pair (recursivep
;   . controller-alists) where recursivep is nil (if this is a nonrec
;   definition) or a truelist of symbols naming all the fns in the
;   ``clique'' (singly recursive functions have a singleton list as
;   their recursivep property); and controller-alists is a non-empty
;   list of alists, each pairing each fn named in recursivep to a mask
;   of t's and nil's in 1:1 correspondence with the formals of the fn
;   and indicating with t's which arguments control the recursion for
;   this definition.

; 'meta - a rule justified by a metatheorem.  In this case, the lhs is
;   the metafunction symbol to be applied and hyps is the
;   metafunction symbol to generate the hyps.  If the rhs is the
;   symbol 'extended then both metafunctions are extended and take two
;   arguments, the target term and the mfc.  Otherwise, they just take
;   one argument.

; This layout is unoptimized.

(defrec rewrite-constant
  ((expand-lst . terms-to-be-ignored-by-rewrite)
   (top-clause . current-clause)
   (ens . current-literal)
   . fns-to-be-ignored))

; The expand-lst and the terms-to-be-ignored-by-rewrite have dual uses
; in ACL2.  They are used by induct to communicate to rewrite and they
; are used to implement parts of the user-supplied hint mechanism.  In
; Paco, they only see the use by induct.

; The current-literal is a record, not a literal.  Its not-flg and atm
; are always used together so we bundle them so we can extract them
; both at once.

(defrec current-literal (not-flg . atm))

; We here implement the check that the term we are about to rewrite is
; not a member of :terms-to-be-ignored-by-rewrite.  The trouble is,
; the ``term we are about to rewrite'' is represented by a term and a
; substitution alist.  We do not want to create the instantiation.  So
; we first need the concept of whether a term is equal to another term
; mod a substitution.

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
         (cond ((cons-term-primitivep (ffn-symb term1))
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

; Is (sublis-var alist1 term1) a member-equal of term2-lst?

  (cond ((endp term2-lst) nil)
        ((equal-mod-alist term1 alist1 (car term2-lst))
         t)
        (t (member-equal-mod-alist term1 alist1 (cdr term2-lst)))))

(defun not-to-be-rewrittenp1 (fn lst)

; This function determines whether fn is the ffn-symb of any term on
; lst.  We assume lst is a true list of non-variablep non-quotep
; terms.

  (cond ((endp lst)
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

(defrec metafunction-context
  (type-alist obj iff-flg wrld fnstack ancestors rcnst))

(defun ev-synp (synp-term unify-subst mfc wrld)

; Synp-term is the quotation of the term to be evaluated.  Unify-subst is the
; unifying substitution presently in force, and mfc is the meta-level context
; (formerly referred to as "metafunction-context").

  (let* ((unify-subst1 (if mfc
                           (cons (cons 'mfc mfc)
                                 unify-subst)
                         unify-subst)))
    (eval (cadr synp-term) unify-subst1 wrld)))

(defun tautologyp (term ens wrld)

; If this function returns t, then term is a theorem.  This function
; can be made as fancy as you want, as long as it recognizes theorems.

  (let ((fns '(if iff not implies eq atom eql = /= null zerop synp plusp
                  minusp listp prog2$ force case-split)))

; Note that fns contains IF as its first element.  If term mentions
; none of these functions, there is no point in doing expansion or
; if-distribution.  We just reduce to catch the trivial cases like
; (consp (cons x y)).  But if term does contain any of these
; functions, we expand all of them (cdring past the undefined IF on
; the front).

    (if (ffnnamesp fns term)
        (if-tautologyp
         (expand-some-non-rec-fns (cdr fns) term wrld)
         ens
         wrld)
      (equal (reduce term t nil ens wrld t)
             *t*))))

(defun refinementp (equiv iff-flg)

; We determine whether equiv is a refinment of the equivalence relation
; indicated by iff-flg, where nil means EQUAL and t means IFF.

  (if iff-flg
      (or (eq equiv 'equal) (eq equiv 'iff))
    (eq equiv 'equal)))

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

  (cond ((endp fnstack) nil)
        ((consp (car fnstack))
         (or (eq fn (caar fnstack)) ; and hence (not (eq (caar fnstack) :term))
             (being-openedp-rec fn (cdr fnstack))))
        (t (or (eq fn (car fnstack))
               (being-openedp-rec fn (cdr fnstack))))))

(defmacro being-openedp (fn fnstack clique)

; We found a 1.8% slowdown when we modified the code, in a preliminary cut at
; v2-7, to improve the speed of being-openedp when large cliques are on the
; fnstack by looking up the representative of fn on the fnstack, rather than
; looking up fn itself.  Presumably that slowdown resulted from the new calls
; to getprop to get the 'recursivep property.  Here we avoid computing that
; getprop (in the case that clique is a getprop expression) in a case we
; suspect is pretty common:  fnstack is empty.  The fnstack argument will
; always be a symbolp expression, so we do not need to let-bind it below.

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

  (cond ((endp fnstack) nil)
        ((and (consp (car fnstack))
              (not (eq (caar fnstack) :term)))
         t)
        (t (recursive-fn-on-fnstackp (cdr fnstack)))))

(defun some-fnstack-term-dumb-occur (fnstack term)
  (cond ((endp fnstack) nil)
        ((and (consp (car fnstack))
              (eq (caar fnstack) :term)
              (dumb-occur (cdar fnstack) term))
         t)
        (t (some-fnstack-term-dumb-occur (cdr fnstack) term))))

(mutual-recursion

(defun occur-cnt-rec (term1 term2 acc)

; Return a lower bound on the number of times term1 occurs in term2.
; We do not go inside of quotes.

  (cond ((equal term1 term2) (1+ acc))
        ((variablep term2) acc)
        ((fquotep term2) acc)
        (t (occur-cnt-lst term1 (fargs term2) acc))))

(defun occur-cnt-lst (term1 lst acc)
  (cond ((endp lst) acc)
        (t (occur-cnt-rec term1
                          (car lst)
                          (occur-cnt-lst term1 (cdr lst) acc)))))
)

(defun occur-cnt (term1 term2)
  (occur-cnt-rec term1 term2 0))

(mutual-recursion

(defun count-ifs (term)
  (cond ((variablep term) 0)
        ((fquotep term) 0)
        ((eq (ffn-symb term) 'if)
         (+ 1
            (count-ifs (fargn term 1))
            (count-ifs (fargn term 2))
            (count-ifs (fargn term 3))))
        (t (count-ifs-lst (fargs term)))))

(defun count-ifs-lst (lst)
  (cond ((endp lst) 0)
        (t (+ (count-ifs (car lst))
              (count-ifs-lst (cdr lst))))))

)

(defun too-many-ifs1 (args val lhs rhs)
  (cond
   ((endp args) nil)
   (t (let ((x (count-ifs (car args))))
        (cond ((int= x 0)
               (too-many-ifs1 (cdr args) val lhs rhs))
              (t (let ((lhs (+ lhs (* x (occur-cnt (car args) val)))))
                   (cond ((> lhs rhs) t)
                         (t (too-many-ifs1 (cdr args) val lhs rhs))))))))))

(defun too-many-ifs (args val)

; Let args be the list of actuals to a nonrec fn.  Let val be the
; rewritten body.  We wish to determine whether the expansion of the
; fn call introduces too many IFs all at once.  Our motivation comes
; from an example like (M2 (ZTAK & & &) (ZTAK & & &) (ZTAK & & &))
; where the careless opening up of everybody produces a formula with
; several hundred IFs in it because of M2's duplication of the IFs
; coming from the simplification of the ZTAKs.  My first thought was
; to never expand a nonrec fn -- at the top level of the clause -- if
; it had some IFs in its args and to wait till CLAUSIFY has cleaned
; things up.  That slowed a proveall down by a factor of 2 -- and by a
; factor of 13 in PRIME-LIST-TIMES-LIST -- because of the ridiculously
; slow expansion of such basic nonrec fns as AND, OR, NOT, and NLISTP.

; This function computes:

; (> (ITERATE FOR ARG IN ARGS SUM (* (COUNT-IFS ARG) (OCCUR-CNT ARG VAL)))
;    (ITERATE FOR ARG IN ARGS SUM (COUNT-IFS ARG)))

; but does it slightly more efficiently by observing that if no IFs
; occur in any arg then there is no point in doing the OCCUR-CNTs and
; that once the left hand side has been pushed beyond the right there
; is no point in continuing.

  (let ((rhs (count-ifs-lst args)))
    (cond ((int= rhs 0) nil)
          (t (too-many-ifs1 args val 0 rhs)))))

(defun all-args-occur-in-top-clausep (args top-clause)
  (cond ((endp args) t)
        (t (and (dumb-occur-lst (car args) top-clause)
                (all-args-occur-in-top-clausep (cdr args) top-clause)))))

(defun cons-count-ac (x i)
  (cond ((atom x) i)
        (t (cons-count-ac (cdr x) (cons-count-ac (car x) (1+ i))))))

(defun cons-count (x)
  (cons-count-ac x 0))

(mutual-recursion

(defun max-form-count (term)

; This function is used in the control of recursive fn expansion.
; Many years ago, we used the fn count part of var-fn-count in this
; role.  Then we decided that for controlling expansion we should not
; count (IF x y z) to have size 1+|x|+|y|+|z| because the IF will be
; distributed and the y or the z will rest in the argument position of
; the recursive call.  So we started to compute the maximum fn count
; in the branches.  Then we added explicit values (this really was
; years ago!) and decided not to consider 1000 to be better than 999,
; since otherwise (< x 1000) would open.  So we measure quoted
; constants by their Lisp size.

  (cond ((variablep term) 0)
        ((fquotep term) (cons-count (cadr term)))
        ((eq (ffn-symb term) 'if)
         (max (max-form-count (fargn term 2))
              (max-form-count (fargn term 3))))
        (t (1+ (max-form-count-lst (fargs term))))))

(defun max-form-count-lst (lst)
  (cond ((endp lst) 0)
        (t (+ (max-form-count (car lst))
              (max-form-count-lst (cdr lst))))))

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

  (cond ((endp args) 0)
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

(defun some-controller-pocket-simplerp
  (call result controller-alists)

; Call has rewritten to something involving result.  Both call and
; result are applications of functions in the same mutually recursive
; clique.

; Controller-alists is a list of alists.  Each alist associates a fn
; in the clique to a controller pocket.  A controller pocket is a list
; in 1:1 correspondence with the formals of the fn with a t in those
; slots that are controllers and a nil in the others.  Thus, each
; alist assigns a complexity to both call and to result.

; We determine whether there exists an alist in controller-alists that
; assigns a lower complexity to result than to call.

  (cond ((endp controller-alists) nil)
        ((< (controller-complexity t result (car controller-alists))
            (controller-complexity t call (car controller-alists)))
         t)
        (t (some-controller-pocket-simplerp call
                                            result
                                            (cdr controller-alists)))))

(defun constant-controller-pocketp1 (args controller-pocket)
  (cond ((endp args) t)
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
  (call result controller-alists)

; Call and result are both applications of functions in the same
; mutually recursive clique.  Controller-alists is a list of alists.
; Each alist assigns to each fn in the clique a controller pocket.
; We determine whether some alist in controller-alists assigns
; controllers in such a way that the controllers of result are
; constant and the complexity of the non-controllers in result
; is less than that of the non-controllers in call.

  (cond ((endp controller-alists) nil)
        ((and (constant-controller-pocketp result (car controller-alists))
              (< (controller-complexity nil result (car controller-alists))
                 (controller-complexity nil call (car controller-alists))))
         t)
        (t (some-controller-pocket-constant-and-non-controller-simplerp
            call result (cdr controller-alists)))))

(mutual-recursion

(defun rewrite-fncallp (call result cliquep top-clause current-clause
                             controller-alists)

; Call has rewritten to (some term involving) result.  We want to know
; if we should replace call by result or leave the call unopened.  The
; ffn-symb of call is known to be a recursive function symbol, fn.  It
; is not a lambda-expression.  Cliquep is nil if fn is singly
; recursive and is the list of functions in fn's clique if it is
; mutually recursive.  Top-clause and current-clause are two clauses
; from simplify-clause0 (the input clause there and the result of
; removing trivial equations).  Controller-alists is the
; 'controller-alists property of fn.

; The controller-alists property of fn is a list of alists.  Each
; alist pairs every function in fn's mutually recursive clique with a
; controller pocket.  Thus, if fn is singly recursive,
; controller-alists looks like this:
; (((fn . controller-pocket1))...((fn . controller-pocketk))).
; But if fn is mutually recursive with clique fn1...fnm, then each
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
                           controller-alists))
   ((if cliquep
        (member-eq (ffn-symb result) cliquep)
      (eq (ffn-symb result) (ffn-symb call)))
    (and (or (all-args-occur-in-top-clausep (fargs result)
                                            top-clause)
             (dumb-occur-lst result current-clause)
             (some-controller-pocket-simplerp
              call
              result
              controller-alists)
             (some-controller-pocket-constant-and-non-controller-simplerp
              call
              result
              controller-alists))
         (rewrite-fncallp-listp call (fargs result)
                                cliquep
                                top-clause
                                current-clause
                                controller-alists)))
   (t (rewrite-fncallp-listp call (fargs result)
                             cliquep
                             top-clause
                             current-clause
                             controller-alists))))

(defun rewrite-fncallp-listp (call lst cliquep top-clause current-clause
                                   controller-alists)
  (cond ((endp lst) t)
        (t (and (rewrite-fncallp call (car lst)
                                 cliquep
                                 top-clause
                                 current-clause
                                 controller-alists)
                (rewrite-fncallp-listp call (cdr lst)
                                       cliquep
                                       top-clause
                                       current-clause
                                       controller-alists)))))

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
  (cond ((endp lst) nil)
        (t (or (contains-rewriteable-callp fn (car lst)
                                           cliquep
                                           terms-to-be-ignored-by-rewrite)
               (contains-rewriteable-callp-lst
                fn (cdr lst)
                cliquep
                terms-to-be-ignored-by-rewrite)))))

)

(defun free-p (x)
  (and (consp x) (eq (car x) :free)))

(defun expand-permission-p (term expand-lst)

; This is a generalized version of member-equal that asks whether
; expand-lst gives term permission to be expanded.  Here, term is a
; function application.

  (if (endp expand-lst)
      nil
      (or (let ((x (car expand-lst)))
            (or (and (eq x :LAMBDAS)
                     (flambda-applicationp term))
                (if (free-p x)
                    (mv-let (flg sbst)
                            (one-way-unify1 (caddr x) term (cadr x))
                            (declare (ignore sbst))
                            flg)
                  (equal x term))))
          (expand-permission-p term (cdr expand-lst)))))

; There are many discrepancies between Paco's rewriter and ACL2's.
; The most important is that Paco does not support linear arithmetic.
; Another major omission is that Paco does not support equivalence or
; congruence relations.  Paco does not support enabling or disabling
; of runes -- indeed, it has no concept of rune or of an enabled
; structure.  In addition, Paco does not support HIDE, FORCE,
; CASE-SPLIT, BIND-FREE or the search for multiple instantiations of
; free vars.  HIDE would not be difficult to add but seemed to be too
; minor to warrant the complexity.  FORCE and CASE-SPLIT require the
; presence of ttrees or other dependency tracking to implement.
; BIND-FREE seemed too complicated for the first pass.  However, Paco
; does support SYNTAXP and metafunctions, which require some of the
; same basic machinery as BIND-FREE.


; Essay on Rewrite Entry and the Extra Arguments

; The next major concern is the fact that rewrite and its peers in the
; rewrite clique take so many arguments.  Each function in the clique
; takes some arguments specific to itself and some other ``extra''
; arguments shared by every other function in the clique.  Most often,
; when functions in the clique call other functions, the extra
; arguments are passed as is, e.g., type-alist and wrld.  We make a
; convenient macro, (rewrite-entry term :key1 val1 ...) that extends
; term by passing all the extra args as is, except for the ones indicated
; by keywords.

; The extra arguments are
#|

 ; &extra formals
 type-alist obj iff-flg wrld fnstack ancestors rcnst nnn

|#

; Important Note:  The string "&extra formals" is included where ever
; this list has been copied.

; Convention: Not every function uses all 7 of the extra formals.
; Ignored formals are so declared and we pass nil into such a slot
; (to be consistent while avoiding the appearance of using the old value).

(defun plist-to-alist (lst)

; Convert '(key1 val1 key2 val2 ...) to '((key1 . val1) (key2 . val2) ...).
; In use here, the keys are all in the keyword package.

  (cond ((endp lst) nil)
        (t (cons (cons (car lst) (cadr lst))
                 (plist-to-alist (cddr lst))))))

(defun add-rewrite-args (extra-formals keyword-extra-formals alist)

; extra-formals is '(type-alist ...)
; keyword-extra-formals is '(:type-alist ...)
; alist pairs keyword extra formals and terms

; We return a list in 1:1 correspondence with extra-formals.  The
; element corresponding to an extra-formal is the value specified by
; the alist if one is so specified, otherwise it is the extra-formal
; itself.

  (cond ((endp extra-formals) nil)
        (t (cons (let ((pair (assoc-eq (car keyword-extra-formals)
                                       alist)))
                   (cond (pair (cdr pair))
                         (t (car extra-formals))))
                 (add-rewrite-args (cdr extra-formals)
                                   (cdr keyword-extra-formals)
                                   alist)))))

(defmacro rewrite-entry (&rest args)
  (declare (xargs :guard (and (true-listp args)
                              (keyword-value-listp (cdr args)))))
  (append (car args)
          (add-rewrite-args '( ; &extra formals
                              type-alist obj iff-flg wrld fnstack
                              ancestors rcnst nnn)
                            '( ; &extra formals -- keyword versions
                              :type-alist :obj :iff-flg :wrld :fnstack
                              :ancestors :rcnst :nnn)
                            (plist-to-alist (cdr args)))))


; The rewrite clique:

(local (defthm rewrite-admission-lemma1
         (implies (consp x)
                  (acl2::posp (acl2-count x)))))

(local (defthm rewrite-admission-lemma2
         (implies (not (equal (caddr x) (cadddr x)))
                  (< (+ 1 (acl2-count (cadr x))
                        (acl2-count (caddr x))
                        (acl2-count (cadddr x)))
                     (acl2-count x)))))

(mutual-recursion

(defun rewrite (term alist
                ; &extra formals
                type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

  (declare (xargs :measure (lex4 (nfix nnn) 6 (acl2-count term) 0)
                  :hints (("Goal"
                           :in-theory
                           (disable assume-true-false
                                    type-set
                                    ancestors-check
                                    sublis-var
                                    enabled-numep
                                    one-way-unify acl2-count
                                    member-eq acl2::member-equal
                                    refinementp
                                    legal-variablep
                                    apply
                                    search-type-alist
                                    var-fn-count
                                    logand)))))

  (cond ((zp nnn) (sublis-var alist term))
        ((variablep term)
         (rewrite-solidify (sublis-var alist term)
                           type-alist iff-flg
                           (access rewrite-constant rcnst :ens) wrld))
        ((fquotep term)
         (if iff-flg
             (if (equal term *nil*) *nil* *t*)
           term))
        ((eq (ffn-symb term) 'if)

; We handle (if x y y) as a special case since it allows us to avoid
; rewriting x.

         (cond
          ((equal (fargn term 2) (fargn term 3))
           (rewrite-entry
            (rewrite (fargn term 2) alist)))
          (t
           (let ((rewritten-test
                  (rewrite-entry
                   (rewrite (fargn term 1) alist)
                   :obj
                   (case obj
                     ((t)
                      (cond ((equal (fargn term 2) *nil*)
                             nil)
                            ((equal (fargn term 3) *nil*)
                             t)
                            (t '?)))
                     ((nil)
                      (cond ((equal (fargn term 2) *t*)
                             nil)
                            ((equal (fargn term 3) *t*)
                             t)
                            (t '?)))
                     (t '?))
                   :iff-flg t)))
             (rewrite-entry
              (rewrite-if rewritten-test
                          (fargn term 1)
                          (fargn term 2)
                          (fargn term 3)
                          alist))))))
        ((eq (ffn-symb term) 'IMPLIES)

; We handle IMPLIES specially.  We rewrite both the hyps and the concl
; under the original type-alist, and then immediately return the
; resulting expansion of the body of IMPLIES.  This prevents the concl
; from being rewritten under the (presumably) more powerful type-alist
; gotten from assuming the hyps true until after any normalization has
; occurred.

         (subcor-var (formals 'IMPLIES wrld)
                     (list (rewrite-entry (rewrite (fargn term 1) alist)
                                          :obj '?
                                          :iff-flg t)
                           (rewrite-entry (rewrite (fargn term 2) alist)
                                          :obj '?
                                          :iff-flg t))
                     (body 'IMPLIES t wrld)))
        ((not-to-be-rewrittenp term alist
                               (access rewrite-constant
                                       rcnst
                                       :terms-to-be-ignored-by-rewrite))
         (rewrite-solidify (sublis-var alist term)
                           type-alist iff-flg
                           (access rewrite-constant rcnst :ens)
                           wrld))
        (t
         (let ((fn (ffn-symb term))
               (rewritten-args (rewrite-entry (rewrite-args (fargs term) alist)
                                :obj '?
                                :iff-flg nil)))
           (cond
            ((and (all-quoteps rewritten-args)
                  (enabled-numep (fn-nume :EXECUTABLE-COUNTERPART fn wrld)
                                 (access rewrite-constant rcnst :ens)))
             (mv-let (erp val)
                     (apply fn
                            (strip-cadrs rewritten-args)
                            wrld)
                     (cond (erp (cons-term fn rewritten-args))
                           (t
                            (<rewrite-id>
                             (kwote val))))))
            (t
             (rewrite-entry
              (rewrite-with-lemmas
               (rewrite-entry
                (rewrite-primitive fn rewritten-args)
                :nnn (- nnn 1))))))))))

(defun rewrite-if (test unrewritten-test left right alist
                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

  (declare (xargs :measure (lex4 (nfix nnn)
                                 6
                                 (+ 1
                                    (acl2-count unrewritten-test)
                                    (acl2-count left)
                                    (acl2-count right))
                                 (acl2-count test))))

; Test is the result of rewriting unrewritten-test under the same alist and
; extra formals.  Except, unrewritten-test can be nil, in which case we of
; course make no such claim.

  (cond
   ((zp nnn)
    (fcons-term* 'if
                 test
                 (sublis-var alist left)
                 (sublis-var alist right)))
   ((and (nvariablep test)
         (not (fquotep test))
         (eq (ffn-symb test) 'if)
         (equal (fargn test 2) *nil*)
         (equal (fargn test 3) *t*))
    (rewrite-entry (rewrite-if (fargn test 1) nil right left alist)))
   ((quotep test)

; It often happens that the test rewrites to *t* or *nil* and we can
; avoid the assume-true-false below.

    (if (cadr test)
        (if (and unrewritten-test ; optimization (see e.g. rewrite-if above)
                 iff-flg
                 (equal unrewritten-test left))

; We are in the process of rewriting a term of the form (if x x y), which
; presumably came from an untranslated term of the form (or x y).  We do not
; want to rewrite x more than once if we can get away with it.  We are using
; the fact that the following is a theorem:  (iff (if x x y) (if x t y)).
; We will use this observation later in the body of this function as well.

            *t*
          (rewrite-entry (rewrite left alist)))
      (rewrite-entry (rewrite right alist))))
   (t (mv-let
       (must-be-true must-be-false true-type-alist false-type-alist)
       (assume-true-false test type-alist nil
                          (access rewrite-constant rcnst :ens)
                          wrld *type-set-nnn*)
       (cond
        (must-be-true
         (if (and unrewritten-test
                  iff-flg
                  (equal unrewritten-test left))
             *t*
           (rewrite-entry (rewrite left alist)
                          :type-alist true-type-alist)))
        (must-be-false
         (rewrite-entry (rewrite right alist)
                        :type-alist false-type-alist))
        (t (let ((rewritten-left
                  (if (and unrewritten-test
                           iff-flg
                           (equal unrewritten-test left))
                      *t*
                    (rewrite-entry (rewrite left alist)
                                   :type-alist true-type-alist)))
                 (rewritten-right
                  (rewrite-entry (rewrite right alist)
                                 :type-alist false-type-alist)))
             (cons-term-if test rewritten-left rewritten-right
                           iff-flg type-alist
                           (access rewrite-constant rcnst :ens)
                           wrld))))))))

(defun rewrite-args (args alist
                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

  (declare (xargs :measure (lex4 (nfix nnn) 6 (acl2-count args) 0))
           (ignore iff-flg))

  (cond ((zp nnn)
         (sublis-var-lst alist args))
        ((endp args)
         nil)
        (t (cons
            (rewrite-entry (rewrite (car args) alist)
                           :iff-flg nil)
            (rewrite-entry (rewrite-args (cdr args) alist)
                           :iff-flg nil)))))

(defun rewrite-primitive (fn args
                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

  (declare (xargs :measure (lex4 (nfix nnn) 6 (acl2-count args) 0))
           (ignore obj))

  (cond
   ((zp nnn) (cons-term fn args))
   ((flambdap fn) (fcons-term fn args))
   ((eq fn 'equal)
    (rewrite-entry (rewrite-equal (car args) (cadr args))
                   :obj nil
                   :iff-flg nil))
   (t (rewrite-solidify (cons-term fn args) type-alist iff-flg
                        (access rewrite-constant rcnst :ens)
                        wrld))))

(defun rewrite-equal (lhs rhs
                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

; We rewrite and return a term equivalent to (EQUAL lhs rhs).

  (declare (xargs :measure (lex4 (nfix nnn)
                                 5
                                 (+ 1
                                    (acl2-count lhs)
                                    (acl2-count rhs))
                                 0))
           (ignore obj iff-flg))

  (cond
   ((zp nnn) (cons-term 'equal (list lhs rhs)))
   ((equal lhs rhs) *t*)
   ((and (quotep lhs)
         (quotep rhs))
    *nil*)
   (t
    (let* ((ens (access rewrite-constant rcnst :ens))
           (ts-lhs (type-set lhs type-alist nil ens wrld *type-set-nnn*))
           (ts-rhs (type-set rhs type-alist nil ens wrld *type-set-nnn*)))
      (cond
       ((not (ts-intersectp ts-lhs ts-rhs)) *nil*)
       ((equal-x-cons-x-yp lhs rhs) *nil*)
       ((and (ts-subsetp ts-lhs *ts-boolean*)
             (equal rhs *t*))
        lhs)
       ((and (ts-subsetp ts-rhs *ts-boolean*)
             (equal lhs *t*))
        rhs)
       ((equal lhs *nil*)
        (fcons-term* 'if rhs *nil* *t*))
       ((equal rhs *nil*)
        (fcons-term* 'if lhs *nil* *t*))
       ((equalityp lhs)
        (fcons-term* 'if lhs
                     (fcons-term* 'equal rhs *t*)
                     (fcons-term* 'if rhs *nil* *t*)))
       ((equalityp rhs)
        (fcons-term* 'if rhs
                     (fcons-term* 'equal lhs *t*)
                     (fcons-term* 'if lhs *nil* *t*)))
       ((and (ts-subsetp ts-lhs *ts-cons*)
             (ts-subsetp ts-rhs *ts-cons*))

; If lhs and rhs are both of type cons, we recursively rewrite the
; equality of their cars and then of their cdrs.  If either of these
; two tests fails, this equality is nil.  If both succeed, this one is
; t.  Otherwise, we don't rewrite term.

        (let* ((alist (list (cons 'lhs lhs)
                            (cons 'rhs rhs)))
               (rewritten-car
                (rewrite-entry (rewrite '(equal (car lhs) (car rhs))
                                        alist)
                               :obj '?
                               :iff-flg t
                               :nnn (- nnn 1))))
                  (cond
                   ((equal rewritten-car *t*)
                    (let ((rewritten-cdr
                           (rewrite-entry (rewrite '(equal (cdr lhs)
                                                           (cdr rhs))
                                                   alist)
                                          :obj '?
                                          :iff-flg t
                                          :nnn (- nnn 1))))
                      (cond ((equal rewritten-cdr *t*)
                             *t*)
                            ((equal rewritten-cdr *nil*)
                             *nil*)
                            (t (fcons-term* 'equal lhs rhs)))))
                   ((equal rewritten-car *nil*)
                    *nil*)

                   (t
                    (let ((rewritten-cdr
                           (rewrite-entry (rewrite '(equal (cdr lhs)
                                                           (cdr rhs))
                                                   alist)
                                          :obj '?
                                          :iff-flg t
                                          :nnn (- nnn 1))))
                      (cond ((equal rewritten-cdr *nil*)
                             *nil*)
                            (t (fcons-term* 'equal lhs rhs))))))))
       (t (fcons-term* 'equal lhs rhs)))))))

(defun relieve-hyp (term unify-subst
                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

; This function is a No-Change Loser.

  (declare (xargs :measure (lex4 (nfix nnn) 0 0 0))
           (ignore obj iff-flg))

  (cond ((zp nnn) (mv nil unify-subst))
        ((and (nvariablep term)
              (not (fquotep term))
              (eq (ffn-symb term) 'synp))
         (let ((mfc (if (member-eq 'mfc (all-vars (cadr (fargn term 3))))
                        (make metafunction-context
                              :type-alist type-alist
                              :obj '?
                              :iff-flg nil
                              :wrld wrld
                              :fnstack fnstack
                              :ancestors ancestors
                              :rcnst rcnst)
                      nil))
               (synp-fn (car (cadr (fargn term 2)))))
           (mv-let (erp val)
                   (ev-synp (fargn term 3) unify-subst mfc wrld)
                   (cond
                    ((or erp (null val)) (mv nil unify-subst))
                    ((eq synp-fn 'SYNTAXP) (mv val unify-subst))

; Here we could handle BIND-FREE forms as in ACL2, but I don't want to be
; distracted by them.

                    (t (mv nil unify-subst))))))
        ((and (equalityp term)
              (variablep (fargn term 1))
              (not (assoc-eq (fargn term 1) unify-subst))
              (not (free-varsp (fargn term 2) unify-subst)))
         (let ((rewritten-rhs
                (rewrite-entry
                 (rewrite (fargn term 2)
                          unify-subst)
                 :obj '?
                 :iff-flg nil
                 :nnn (- nnn 1))))
           (mv t
               (cons (cons (fargn term 1) rewritten-rhs)
                     unify-subst))))
        (t
         (mv-let
          (flg unify-subst)
          (lookup-hyp term type-alist wrld unify-subst
		      (access rewrite-constant rcnst :ens))
          (cond
           (flg (mv t unify-subst))
           ((free-varsp term unify-subst) (mv nil unify-subst))
           (t
            (let ((inst-hyp (sublis-var unify-subst term)))
              (mv-let
               (on-ancestorsp assumed-true)
               (ancestors-check inst-hyp ancestors)
               (cond
                (on-ancestorsp (mv assumed-true unify-subst))
                (t
                 (mv-let
                  (knownp nilp)
                  (known-whether-nil inst-hyp type-alist
                                     (access rewrite-constant rcnst :ens)
                                     wrld)
                  (cond
                   (knownp (mv (not nilp) unify-subst))
                   (t
                    (mv-let
                     (not-flg atm)
                     (strip-not term)
                     (let ((rewritten-atm
                            (rewrite-entry
                             (rewrite atm unify-subst)
                             :obj (if not-flg nil t)
                             :iff-flg t
                             :ancestors (push-ancestor
                                         (dumb-negate-lit inst-hyp)
                                         ancestors)
                             :nnn (- nnn 1))))
                      (cond
                       (not-flg
                        (mv (equal rewritten-atm *nil*) unify-subst))
                       ((if-tautologyp rewritten-atm
                                       (access rewrite-constant rcnst :ens)
                                       wrld)
                        (mv t unify-subst))
                       (t (mv nil unify-subst))))))))))))))))))

(defun relieve-hyps (hyps unify-subst
                   ; &extra formals
                     type-alist obj iff-flg wrld fnstack ancestors
                     rcnst nnn)

; We return t or nil indicating success and an extended unify-subst.
; This function is a No-Change Loser.

  (declare (xargs :measure (lex4 (nfix nnn) 1 (acl2-count hyps) 0))
           (ignore obj iff-flg))

  (cond ((endp hyps) (mv t unify-subst))
        (t (mv-let (flg unify-subst)
                   (rewrite-entry (relieve-hyp (car hyps) unify-subst)
                                  :obj nil
                                  :iff-flg nil)
                   (cond
                    (flg
                     (rewrite-entry (relieve-hyps (cdr hyps) unify-subst)
                                    :obj nil
                                    :iff-flg nil))
                    (t (mv nil unify-subst)))))))

(defun rewrite-with-lemma (term lemma
                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

; The two values returned by this function are t or nil, indicating
; whether lemma was used to rewrite term, and the rewritten version of
; term.  This is a No-Change Loser.

  (declare (xargs :measure (lex4 (nfix nnn) 4 0 0)))

  (cond
   ((zp nnn) (mv nil term))
   ((eq (access rewrite-rule lemma :subclass) 'meta)
    (cond
     ((refinementp (access rewrite-rule lemma :equiv) iff-flg)

; Metafunctions come in two flavors.  Vanilla metafunctions take just
; one arg, the term to be rewritten.  Extended metafunctions take
; three args.  We cons up the args here and use this list of args
; twice below, once to eval the metafunction and once to eval the hyp
; fn.  The :rhs of the rewrite-rule is the special flag 'extended
; if we are in the extended case; otherwise, :rhs is nil.  We must
; manufacture a context in the former case.

      (let* ((args
              (cond
               ((eq (access rewrite-rule lemma :rhs)
                    'extended)
                (list term
                      (make metafunction-context
                            :type-alist type-alist
                            :obj obj
                            :iff-flg iff-flg
                            :wrld wrld
                            :fnstack fnstack
                            :ancestors ancestors
                            :rcnst rcnst)))
               (t (list term)))))
        (mv-let
         (erp val)
         (apply (access rewrite-rule lemma :lhs) args wrld)
         (cond
          (erp
           (mv nil term))
          ((equal term val)
           (mv nil term))
          ((termp val wrld)
           (let ((hyp-fn (access rewrite-rule lemma :hyps)))
             (mv-let
              (erp evaled-hyp)
              (if (eq hyp-fn nil)
                  (mv nil *t*)
                (apply hyp-fn args wrld))
              (cond
               (erp (mv nil term))
               ((termp evaled-hyp wrld)
                (cond
                 ((ffnnamep 'synp evaled-hyp)
                  (mv nil term))
                 (t
                  (mv-let
                   (relieve-hyps-ans unify-subst)
                   (rewrite-entry (relieve-hyps
                                   (flatten-ands-in-lit

; Note: The sublis-var below normalizes the explicit constant
; constructors in evaled-hyp, e.g., (cons '1 '2) becomes '(1 . 2).

                                    (sublis-var nil evaled-hyp))

; The meta function has rewritten term to val and has generated a
; hypothesis called evaled-hyp.  Now ignore the metafunction and just
; imagine that we have a rewrite rule (implies evaled-hyp (equiv term
; val)).  The unifying substitution just maps the vars of term to
; themselves.  There may be additional vars in both evaled-hyp and in
; val.  But they are free at the time we do this relieve-hyps.

                                   (let ((vars (all-vars term)))
                                     (pairlis vars vars)))
                                  :obj nil
                                  :geneqv nil)
                   (cond
                    (relieve-hyps-ans
                     (let ((rewritten-rhs
                            (rewrite-entry
                             (rewrite

; Note: The sublis-var below normalizes the explicit constant
; constructors in val, e.g., (cons '1 '2) becomes '(1 . 2).

                              (sublis-var nil val)

; At one point we ignored the unify-subst constructed above and used a
; nil here.  That was unsound if val involved free vars bound by the
; relief of the evaled-hyp.  We must rewrite val under the extended
; substitution.  Often that is just the identity substitution.

                              unify-subst)
                             :nnn (- nnn 1))))
                       (mv t rewritten-rhs)))
                    (t (mv nil term)))))))
               (t (mv nil term))))))
          (t (mv nil term))))))
     (t (mv nil term))))
   ((not (refinementp (access rewrite-rule lemma :equiv) iff-flg))
    (mv nil term))
   ((eq (access rewrite-rule lemma :subclass) 'definition)
    (let ((rewritten-term
           (rewrite-entry (rewrite-fncall lemma term))))
      (mv (not (equal term rewritten-term)) rewritten-term)))
   ((and (or (null (access rewrite-rule lemma :hyps))
             (not (eq obj t))
             (not (equal (access rewrite-rule lemma :rhs) *nil*)))
         (or (flambdap (ffn-symb term)) ; hence not on fnstack
             (not (being-openedp (ffn-symb term) fnstack
                                 (getprop (ffn-symb term) 'recursivep nil
                                          wrld)))
             (not (ffnnamep (ffn-symb term)
                            (access rewrite-rule lemma :rhs)))))
    (let ((lhs (access rewrite-rule lemma :lhs)))
      (mv-let (unify-ans unify-subst)
              (one-way-unify lhs term)
              (cond
               (unify-ans
                (cond
                 ((null (loop-stopperp
                         (access rewrite-rule lemma :heuristic-info)
                         unify-subst))
                  (mv nil term))
                 (t
                  (mv-let
                   (relieve-hyps-ans unify-subst)
                   (rewrite-entry
                    (relieve-hyps (access rewrite-rule lemma :hyps)
                                  unify-subst)
                    :obj nil
                    :geneqv nil)
                   (cond
                    (relieve-hyps-ans
                     (let ((rewritten-rhs
                            (rewrite-entry
                             (rewrite
                              (access rewrite-rule lemma :rhs)
                              unify-subst)
                             :nnn (- nnn 1))))
                      (mv t rewritten-rhs)))
                    (t (mv nil term)))))))
               (t (mv nil term))))))
          (t (mv nil term))))

(defun rewrite-with-lemmas1 (term lemmas
                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)


; Try to rewrite term with the lemmas in lemmas.  Return t or nil
; indicating success, and the rewritten term.  This function is a
; No-Change Loser.

  (declare (xargs :measure (lex4 (nfix nnn) 5 (acl2-count lemmas) 0)))

  (cond ((zp nnn) (mv nil term))
        ((endp lemmas) (mv nil term))
        ((not (enabled-numep (access rewrite-rule (car lemmas) :nume)
                             (access rewrite-constant rcnst :ens)))
         (rewrite-entry
          (rewrite-with-lemmas1 term (cdr lemmas))))
        (t
         (mv-let
          (rewrittenp rewritten-term)
          (<rewrite-with-lemmas1-id>
           (rewrite-entry (rewrite-with-lemma term (car lemmas))))
          (cond (rewrittenp
                 (mv t rewritten-term))
                (t (rewrite-entry
                    (rewrite-with-lemmas1 term (cdr lemmas)))))))))

(defun rewrite-fncall (rule term

                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

; Rule is a :REWRITE rule of subclass DEFINITION or else it is nil.
; Rule is nil iff term is a lambda application.  The value returned by
; this function is the (possibly) rewritten term.

; Term is of the form (fn . args).

  (declare (xargs :measure (lex4 (nfix nnn) 3 0 0)))

  (let* ((fn (ffn-symb term))
         (args (fargs term))
         (body (if (null rule)
                   (lambda-body fn)
                 (access rewrite-rule rule :rhs)))
         (recursivep (and rule ; it's a don't-care if (flambdap fn)
                          (car (access rewrite-rule rule :heuristic-info))))
         (ens (access rewrite-constant rcnst :ens)))
    (cond ((zp nnn) term)
          ((and (not (flambdap fn))
                (being-openedp fn fnstack recursivep))
           (rewrite-solidify term type-alist iff-flg ens wrld))
          ((null rule)  ; i.e., (flambdap fn)
           (let ((rewritten-body
                  (rewrite-entry (rewrite body
                                          (pairlis (lambda-formals fn) args))
                                 :fnstack fnstack
                                 :nnn (- nnn 1))))

; Observe that we do not put the lambda-expression onto the fnstack.
; We act just as though we were rewriting a term under a substitution.
; But we do decide on heuristic grounds whether to keep the expansion.
; See the handling of non-recursive functions below for some comments
; relating to the too-many-ifs code.

            (cond
             ((and (not (recursive-fn-on-fnstackp fnstack))
                   (too-many-ifs args rewritten-body))
              (rewrite-solidify term type-alist iff-flg ens wrld))
             (t rewritten-body))))
          (t
           (let* ((new-fnstack (cons (or recursivep fn) fnstack)))
             (mv-let
              (unify-ans unify-subst)
              (one-way-unify (access rewrite-rule rule :lhs)
                             term)
              (cond
               (unify-ans
                (mv-let
                 (relieve-hyps-ans unify-subst)
                 (rewrite-entry
                  (relieve-hyps (access rewrite-rule rule :hyps)
                                unify-subst)
                  :obj nil
                  :iff-flg nil)
                 (cond
                  (relieve-hyps-ans
                   (let ((rewritten-body
                          (rewrite-entry (rewrite body unify-subst)
                                         :fnstack new-fnstack
                                         :nnn (- nnn 1))))
                    (cond
                     ((null recursivep)

; We are dealing with a nonrecursive fn.  If we are at the top-level of the
; clause but the expanded body has too many IFs in it compared to the number
; in the args, we do not use the expanded body.  We know the IFs in
; the args will be clausified out soon and then this will be permitted to
; open.

                      (cond
                       ((and (not (recursive-fn-on-fnstackp fnstack))
                             (too-many-ifs args rewritten-body))
                        (rewrite-solidify term type-alist iff-flg ens wrld))
                       (t rewritten-body)))
                     ((rewrite-fncallp
                       term rewritten-body
                       (if (cdr recursivep) recursivep nil)
                       (access rewrite-constant rcnst
                               :top-clause)
                       (access rewrite-constant rcnst
                               :current-clause)
                       (cdr (access rewrite-rule rule :heuristic-info)))
                      (cond
                       ((contains-rewriteable-callp
                         fn rewritten-body
                         (if (cdr recursivep)
                             recursivep
                           nil)
                         (access rewrite-constant
                                 rcnst :terms-to-be-ignored-by-rewrite))

; Ok, we are prepared to rewrite the once rewritten body.  But beware!  There
; is an infinite loop lurking here.  It can be broken by using :fnstack
; new-fnstack below, but we do something weaker; more on this below.  The
; problem is the interaction between opening up function definitions and use of
; equalities on the type-alist.  Suppose that (foo x) is defined to be (bar
; (foo (cdr x))) in a certain case.  But imagine that on the type-alist we have
; (foo (cdr x)) = (foo x).  Then rewritten-body, here, is (bar (foo x)).
; Because it contains a rewriteable call we rewrite it again.  If we do so with
; the old fnstack, we will open (foo x) to (bar (foo x)) again and infinitely
; regress.

; This same loop occurs in Nqthm, though it has never been fired in anger, as
; far as we know.  While the loop can be broken by using new-fnstack, that
; approach has a bad side-effect: (member x '(a b c)) is not runout.  It opens
; to (if (equal x 'a) (member x '(b c))) and because new-fnstack mentions
; member, we don't expand the inner call.

; In Version  2.5 and before we handled this rare loop in a very non-rugged
; way, using fnstack unchanged in the recursive call below: If the term we're
; expanding reoccurs in the rewritten body, we won't rewrite the rewritten
; body.  In that approach, if we're expanding (foo x a) and it rewrites to (bar
; (foo (cdr x) a)) and thence to (bar (foo x a)), we'll break the loop.  BUT if
; it goes instead to (bar (foo x a')), we'll just naively go around the loop.

; Starting with Version  2.6, we extend fnstack with (:term . rewritten-body)
; in the recursive call to rewrite, below.  But first, we check the fnstack to
; see if an entry (:term . x) is already there for some subterm x of the
; rewritten body.  This is the only place that we pay attention to elements of
; fnstack of the form (:term . x).

                        (cond
                         ((or (dumb-occur term rewritten-body)
                              (some-fnstack-term-dumb-occur fnstack
                                                            rewritten-body))
                          rewritten-body)
                         (t
                          (let ((rewritten-body
                                 (rewrite-entry
                                  (rewrite rewritten-body nil)
; See the reference to fnstack in the comment above.
                                  :fnstack (cons (cons :term term)
                                                 fnstack)
                                  :nnn (- nnn 1))))
                            rewritten-body))))
                       (t
                        rewritten-body)))
                     (t (rewrite-solidify term type-alist iff-flg ens wrld)))))
                  (t (rewrite-solidify term type-alist iff-flg ens wrld)))))
               (t (rewrite-solidify term type-alist iff-flg ens wrld)))))))))

(defun rewrite-with-lemmas (term
                   ; &extra formals
                   type-alist obj iff-flg wrld fnstack ancestors rcnst nnn)

  (declare (xargs :measure (lex4 (nfix nnn) 6 0 0)))
  (cond
   ((zp nnn) term)
   ((variablep term)
    (rewrite-solidify term type-alist iff-flg
                      (access rewrite-constant rcnst :ens)
                      wrld))
   ((fquotep term) term)
   ((member-equal (ffn-symb term)
                  (access rewrite-constant rcnst :fns-to-be-ignored))
    term)
   ((flambda-applicationp term)
    (cond ((expand-permission-p term
                                (access rewrite-constant rcnst :expand-lst))
           (rewrite-entry
            (rewrite (lambda-body (ffn-symb term))
                     (pairlis (lambda-formals (ffn-symb term))
                              (fargs term)))
            :nnn (- nnn 1)))
          (t (rewrite-entry (rewrite-fncall nil term)))))
   (t (mv-let
       (rewrittenp rewritten-term)
       (rewrite-entry
        (rewrite-with-lemmas1 term
                              (getprop (ffn-symb term) 'lemmas nil wrld)))
       (cond
        (rewrittenp rewritten-term)
        ((and (expand-permission-p term
                                   (access rewrite-constant rcnst :expand-lst))
              (not (being-openedp (ffn-symb term) fnstack
                                  (getprop (ffn-symb term) 'recursivep nil
                                           wrld))))
         (rewrite-entry (rewrite
                         (body (ffn-symb term) t wrld)
                         (pairlis (formals (ffn-symb term) wrld)
                                  (fargs term)))
                        :nnn (- nnn 1)))
        (t (rewrite-solidify term type-alist iff-flg
                             (access rewrite-constant rcnst :ens)
                             wrld)))))))

)

(defconst *rewrite-nnn* 100)


