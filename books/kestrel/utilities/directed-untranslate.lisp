; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Alessandro Coglio, Eric Smith, and Stephen Westfold for helpful
; feedback.

; TODO:

; - Handle more built-in macros, such as case and, perhaps more completely,
;   b*.

; - Perhaps improve lambdafy-rec to deal with dropped conjuncts and disjuncts;
;   see adjust-sterm-for-tterm.

; - Perhaps preserve type declarations.

(in-package "ACL2")

(include-book "make-executable")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc directed-untranslate
  :parents (kestrel-utilities system-utilities-non-built-in)
  :short "Create a user-level form that reflects a given user-level form's
 structure."
  :long "<p>See @(see term) for relevant background about user-level ``terms''
 and actual ``translated'' terms.</p>

 @({
 General Form:
 (directed-untranslate uterm tterm sterm iff-flg stobjs-out wrld)
 })

 <p>where:</p>

 <ul>

 <li>@('uterm') is an untranslated form that translates to the term,
 @('tterm');</li>

 <li>@('sterm') is a term, which might share a lot of structure with
 @('tterm') (we may think of @('sterm') as a simplified version of
 @('tterm'));</li>

 <li>@('iff-flg') is a Boolean;</li>

 <li>@('stobjs-out') is either @('nil') or a @(tsee true-listp) each of whose
 members is either @('nil') or the name of a @(see stobj), with no stobj name
 repeated; and</li>

 <li>@('wrld') is a logical @('world'), typically @('(w state)').</li>

 </ul>

 <p>The result is an untranslated form whose translation is provably equal to
 @('sterm'), except that if @('iff-flg') is true then these need only be
 Boolean equivalent rather than equal.  The goal is that the shared structure
 between @('tterm') and @('sterm') is reflected in similar sharing between
 @('uterm') and the result.  If @('stobjs-out') is not @('nil'), then an
 attempt is made to produce a result with multiple-value return, whose i-th
 element is an ordinary value or a stobj, @('st'), according to whether the
 i-th element of @('stobjs-out') is @('nil') or @('st'), respectively.</p>

 @({
 Example Form:
 (directed-untranslate
  '(and a (if b c nil))         ; uterm
  '(if a (if b c 'nil) 'nil)    ; tterm
  '(if a2 (if b2 c2 'nil) 'nil) ; sterm, a form to be untranslated
  nil nil
  (w state))
 })

 <p>The returned value from the example above is:</p>

 @({
 (AND A2 (IF B2 C2 NIL))
 })

 <p>Compare this with the value returned by calling the system function
 @('untranslate') instead on the final three arguments:</p>

 @({
 ACL2 !>(untranslate '(if a2 (if b2 c2 'nil) 'nil) nil (w state))
 (AND A2 B2 C2)
 ACL2 !>
 })

 <p>The original structure of the given ``uterm'', @('(and a (if b c nil))'),
 has been preserved by @('directed-untranslate'), but not by @('untranslate').
 Thus, @('directed-untranslate') may be particularly useful when a given form,
 @('uterm'), translates to a term, @('tterm'), which in turn simplifies to a
 related term, @('sterm'), and your goal is to untranslate @('sterm') in a way
 that preserves structure from @('uterm').</p>

 <p><b>Remarks</b>.</p>

 <ol>

 <li>The @('directed-untranslate') utility is based on heuristics that may not
 always produce the result you want.  They have been designed to work best in
 the case that @('sterm') is a simplification of @('tterm').</li>

 <ul>

 <li>For an example of the heuristics, suppose that @('uterm') let-binds a
 variable, @('v'), which thus is @(see lambda)-bound in @('tterm') to some
 expression, @('expr').  If @('v') has essentially been replaced by a value
 @('expr'') that occurs in @('sterm'), then an attempt is often made to use
 lambda abstraction to let-bind @('v') to @('expr'') in the result.  (No such
 attempt is made if @('expr') has essentially disappeared in @('sterm').)  The
 utility, @('directed-untranslate-no-lets'), is similar but does not make such
 an attempt.</li>

 <li>For another example, results involving @(tsee b*) are biased towards the
 intended primary use case, in which sterm is a simplification of tterm and the
 result is intended to be in simplified form.  In particular, bindings of the
 form @('(var val)') that specify an ignored or ignorable variable are handled
 as follows.

 <ul>

  <li>A @('b*') binding <tt>(- val)</tt> in @('uterm') translates to @('(prog2$
  val ...)'), so is generally preserved if there is a corresponding @(tsee
  prog2$) call in @('sterm').</li>

  <li>A @('b*') binding of @('(& val)') or @('(?!x val)') in @('uterm') is
  completely discarded in translation to @('tterm'), so is presumably not
  present in @('sterm'), hence is also discarded in the result.</li>

  <li>A @('b*') binding @('(?x val)') in @('uterm') generates an @('ignorable')
  declaration, so is generally preserved if and only if @('x') occurs free in
  @('sterm').  (If the binding were restored after being simplified away, it
  could contain an unsimplified term, which we deem to be undesirable.)</li>

 </ul></li>

 </ul>

 <li>@('Directed-untranslate') may be improved over time; hence it may produce
 different results as the tool uses increasingly sophisticated heuristics.  For
 example, here are some features that are not yet implemented but might be in
 the future, quite possibly only upon request.

 <ul>

 <li>A better untranslation might be obtainable when the simplified
 term (@('sterm')) has similar structure to a proper subterm of the original
 term @('@('tterm')').  As it stands now, the original untranslated term @('uterm')
 is probably useless in that case.</li>

 <li>More macros could quite reasonably be handled, but aren't yet, such as
 @(tsee case).</li>

 <li>Support for @(tsee b*) may be improved by comprehending more binders.</li>

 </ul></li>

 </ol>

 <p>End of Remarks.</p>")

(defun dcl-guardian-p (g)

; See remove-declare-effects.

  (declare (xargs :guard t))
  (case-match g
    (('check-dcl-guardian term
                          ('quote term))
     (prog2$ term t))
    (('return-last ''progn
                   ('check-dcl-guardian term
                                        ('quote term))
                   g2)
     (prog2$ term (dcl-guardian-p g2)))
    (& nil)))

(defun remove-declare-effects (tterm)

; This function returns a term that is provably equivalent to tterm.  In the
; case that tterm results from translation of a let, let*, or mv-let term, we
; attempt to remove the effect of declare forms.

; In particular, we deal with type declarations as follows.  Define a
; dcl-guardian term to be a term other than *t* that is created by a call of
; dcl-guardian.  We strip off such terms from tterm.

  (declare (xargs :guard t))
  (case-match tterm
    (('return-last ''progn g u)
     (cond ((dcl-guardian-p g)
            u)
           (t tterm)))
    ((('lambda formals ('return-last ''progn g u))
      . args)
     (cond ((dcl-guardian-p g)
            `((lambda ,formals ,(remove-declare-effects u))
              ,@args))
           (t tterm)))
    (('hide x) ; Deal with ignore and ignorable declarations.
     x)
    (& tterm)))

(program)

(defun check-du-inv-fn (uterm tterm wrld)
  (mv-let (erp val)
    (translate-cmp uterm t nil t 'check-du-inv-fn wrld
                   (default-state-vars nil))
    (cond (erp (er hard 'check-du-inv
                   "Translation failed during directed-untranslate for the ~
                    form ~x0.  The error is as follows:~|~%~@1"
                   uterm val))
          ((equal (remove-declare-effects val)
                  (remove-declare-effects tterm))
           t)
          (t (er hard 'check-du-inv
                 "Implementation error: Translation check failed during ~
                  directed-untranslate: uterm does not translate to tterm ~
                  (even after ignoring certain effects from declare forms, if ~
                  any).~|uterm: ~x0~|tterm: ~x1"
                 uterm tterm)))))

(defmacro check-du-inv (uterm tterm wrld form)

; By default (i.e., when feature :skip-check-du-inv is not set), we always
; check that tterm is the translation of uterm.  Note that we do not
; necessarily expect that the translation of (directed-untranslate uterm tterm
; sterm iff-flg wrld) is sterm; so we use check-du-inv on inputs of
; directed-untranslate(-rec), not its output.

  #-skip-check-du-inv
  `(assert$ (check-du-inv-fn ,uterm ,tterm ,wrld) ,form)
  #+skip-check-du-inv
  (declare (ignore uterm tterm wrld))
  #+skip-check-du-inv
  form)

(defun macro-abbrev-p-rec (sym body wrld)

; Sym is a macro name with the indicated body.  If this macro simply expands to
; a call of another symbol on its formals, return that symbol unless it is
; another macro, in which case, recur.  Otherwise return nil.

  (let ((args (macro-args sym wrld)))
    (and (null (collect-lambda-keywordps args))
         (case-match body
           (('cons ('quote fn) formal-args)
            (and (equal formal-args (make-true-list-cons-nest args))
                 (let ((new-body (getpropc fn 'macro-body t wrld)))
                   (cond ((eq new-body t) fn)
                         (t (macro-abbrev-p-rec fn new-body wrld))))))
           (& nil)))))

(defun macro-abbrev-p (sym wrld)
  (let ((body (getpropc sym 'macro-body t wrld)))
    (and (not (eq body t))
         (macro-abbrev-p-rec sym body wrld))))

(defun directed-untranslate-drop-conjuncts-rec (uterm tterm sterm top)
  (case-match tterm
    (('if tterm-1 tterm-2 *nil*)
     (cond ((and (ffn-symb-p sterm 'if)
                 (equal tterm-1 (fargn sterm 1)))
            (if top
                (mv nil nil)
              (mv uterm tterm)))
           (t (case-match uterm
                (('and)
                 (mv t tterm))
                (('and y)
                 (mv y tterm))
                (('and & . y)
                 (directed-untranslate-drop-conjuncts-rec
                  (if (cdr y) (cons 'and y) (car y))
                  tterm-2 sterm nil))
                (('if & y 'nil)
                 (directed-untranslate-drop-conjuncts-rec
                  y tterm-2 sterm nil))
                (('if & y ''nil)
                 (directed-untranslate-drop-conjuncts-rec
                  y tterm-2 sterm nil))
                (& (mv nil nil))))))
    (!sterm (if top
                (mv nil nil)
              (mv uterm tterm)))
    (& (mv nil nil))))

(defun directed-untranslate-drop-conjuncts (uterm tterm sterm)

; Tterm is the translation of uterm, where uterm represents a conjunction (and
; x1 x2 ... xn), perhaps instead represented as (if x1 & nil), or (if x1 &
; 'nil).  If sterm is the translation for some k of (and xk . rest), even if
; subsequent conjuncts differ, then return (mv uterm' tterm'), where uterm'
; represents (and xk ... xn) and tterm' representes the corresponding subterm
; of tterm; else return (mv nil nil).  But note: instead return (mv nil nil) if
; tterm is equal to sterm.

  (directed-untranslate-drop-conjuncts-rec uterm tterm sterm t))

(defconst *boolean-primitives*

; These are function symbols from (strip-cars *primitive-formals-and-guards*)
; that always return a Boolean.

  '(acl2-numberp bad-atom<= < characterp complex-rationalp consp equal integerp
                 rationalp stringp symbolp))

(defun boolean-fnp (fn wrld)
  (cond
   ((not (symbolp fn)) nil)
   ((member-eq fn *boolean-primitives*) t)
   (t
    (let ((tp (cert-data-tp-from-runic-type-prescription fn wrld)))
      (and tp
           (null (access type-prescription tp :vars))
           (assert$ (null (access type-prescription tp :hyps))
                    (ts-subsetp
                     (access type-prescription tp :basic-ts)
                     *ts-boolean*)))))))

(defun directed-untranslate-drop-disjuncts-rec (uterm tterm sterm top
                                                      iff-flg wrld)
  (case-match tterm
    (('if tterm-1 tterm-1a tterm-2)
     (cond
      ((or (equal tterm-1a tterm-1)
           (and (equal tterm-1a *t*)
                (or iff-flg
                    (and (nvariablep tterm-1)
                         (not (fquotep tterm-1))
                         (boolean-fnp (ffn-symb tterm-1) wrld)))))
       (cond ((and (ffn-symb-p sterm 'if)
                   (equal tterm-1 (fargn sterm 1)))
              (if top
                  (mv nil nil)
                (mv uterm tterm)))
             (t (case-match uterm
                  (('or)
                   (mv nil tterm))
                  (('or y)
                   (mv y tterm))
                  (('or & . y)
                   (directed-untranslate-drop-disjuncts-rec
                    (if (cdr y) (cons 'or y) (car y))
                    tterm-2 sterm nil iff-flg wrld))
                  (('if x x1 y)
                   (cond ((or (equal x1 x)
                              (equal x1 t)
                              (equal x1 *t*))
                          (directed-untranslate-drop-disjuncts-rec
                           y tterm-2 sterm nil iff-flg wrld))
                         (t (mv nil nil))))
                  (& (mv nil nil))))))
      (t (mv nil nil))))
    (!sterm (if top
                (mv nil nil)
              (mv uterm tterm)))
    (& (mv nil nil))))

(defun directed-untranslate-drop-disjuncts (uterm tterm sterm iff-flg wrld)

; This is analogous to directed-untranslate-drop-conjuncts, but for
; disjunctions.

  (directed-untranslate-drop-disjuncts-rec uterm tterm sterm t iff-flg
                                           wrld))

(defconst *car-cdr-macro-alist*

; We associate each car/cdr macro M, such as CADDR, with operations f (car or
; cdr) and g such that M(x) = f(g(x)).

; (loop for x in *ca<d^n>r-alist*
;       collect
;       (let ((name (symbol-name (car x))))
;         (list (car x)
;               (intern (coerce (list #\C (char name 1) #\R) 'string)
;                       "ACL2")
;               (intern (concatenate 'string "C" (subseq name 2 (length name)))
;                       "ACL2"))))

  '((CADR CAR CDR) (CDAR CDR CAR) (CAAR CAR CAR) (CDDR CDR CDR)
    (CAADR CAR CADR) (CDADR CDR CADR) (CADAR CAR CDAR) (CDDAR CDR CDAR)
    (CAAAR CAR CAAR) (CDAAR CDR CAAR) (CADDR CAR CDDR) (CDDDR CDR CDDR)
    (CAAADR CAR CAADR) (CADADR CAR CDADR)
    (CAADAR CAR CADAR) (CADDAR CAR CDDAR)
    (CDAADR CDR CAADR) (CDDADR CDR CDADR)
    (CDADAR CDR CADAR) (CDDDAR CDR CDDAR)
    (CAAAAR CAR CAAAR) (CADAAR CAR CDAAR)
    (CAADDR CAR CADDR) (CADDDR CAR CDDDR)
    (CDAAAR CDR CAAAR) (CDDAAR CDR CDAAR)
    (CDADDR CDR CADDR) (CDDDDR CDR CDDDR)))

(defun bind-?-final (alist free-vars old-formals)

; See weak-one-way-unify; here we finish off alist by associating every unbound
; variable with itself.

  (cond ((endp alist) nil)
        ((eq (caar alist) :?)
         (assert$

; Since free-vars is the free variables of the new term, which was created by
; generalizing with the top-level alist using fresh variables, this assertion
; should hold.  We bind the old formal to itself; see the discussion about this
; in weak-one-way-unify.

          (or (eq (cdar alist) (car old-formals))
              (not (member-eq (cdar alist) free-vars)))
          (acons (car old-formals)
                 (car old-formals)
                 (bind-?-final (cdr alist) free-vars (cdr old-formals)))))
        (t (cons (car alist)
                 (bind-?-final (cdr alist) free-vars (cdr old-formals))))))

(defun extend-gen-alist1 (sterm var alist)

; Add the pair (sterm . var) to alist, removing the existing pair whose cdr is
; var.

  (cond ((endp alist)
         (er hard 'extend-gen-alist1
             "Not found in alist: variable ~x0."
             var))
        ((eq (cdar alist) var)
         (acons sterm var (cdr alist)))
        (t (cons (car alist)
                 (extend-gen-alist1 sterm var (cdr alist))))))

(defun extend-gen-alist (var sterm alist)

; Alist represents a mapping of variables to terms, but pairs are reversed from
; what one might expect; each pair is (term . variable).  This function either
; returns alist or updates alist to associate var with a term, heuristically
; determined.  If var is not already associated with a term in alist, then we
; simply associate var with sterm.  We actually return two values, where the
; second is the new alist.  The first is a corresponding modification of sterm,
; except that nil is allowed if sterm is unchanged.

; We have a heuristic decision to make.  Our intention is to perform lambda
; abstraction using alist, in essence, creating a (translated) LET expression
; whose bindings are generated by alist.  It might be best to bind a variable
; to the largest possible expression, intuitively to get the most abstraction.
; But it might be best to bind a variable to the smallest possible expression,
; to get the most sharing.  If there are two candidates and neither occurs in
; the other, we could even consider trying to bind to their largest common
; subexpression.  Consider the following example.

; Suppose we are simplifying (let ((x (f (g y)))) (cons x (h x))), and we have
; a rewrite rule (h (f v)) = v.  Then when we simplify, we get (cons (f (g y))
; (g y)).  If we bind x to (f (g y)) then the result is:

;  [1]   (let ((x (f (g y)))) (cons x (g y))).

; But if we bind x to (g y), then the result is:

;  [2]   (let ((x (g y))) (cons (f x) x))

; Which do we prefer?  The first has the advantage that the original binding is
; intact, which is great if our goal is to preserve structure.  The second has
; the advantage of enhanced sharing -- imagine y being replaced by a complex
; expression.

; For our intended application, preserving structure may be more important than
; sharing.  Moreover, if we use [2], that could give us a binding to a very
; small shared expression.  In the example above, imagine that instead of (cons
; x (h x)) we have (list x x (h x) (h x)), that f is very complicated, but that
; (g y) is literally (g y).  Then we have:

;  [1]   (let ((x (f (g y)))) (list x x (g y) (g y))).

;  [2]   (let ((x (g y))) (list (f x) (f x) x x))

; If f is very complicated, then [1] may be preferred.  But if g is very
; complicated, then [2] may be preferred.  Moreover, if y is a complex term
; rather just a variable and f is a simple "wrapper" such as (loghead 32 _),
; then we may prefer (2) so that we can see the "intended" sharing of x.

; For now we'll settle the argument by doing what's simplest for the
; implementation, which is binding x the first time we have an opportunity and
; sticking with that binding.  Otherwise we would likely need to backtrack to
; the top level and then run from scratch with a term associated with x,
; instead of :? .

  (let ((old (rassoc-eq var alist)))
    (assert$

; This call is descended from the call of weak-one-way-unify in lambdafy-rec,
; where we attempt to match a lambda body whose variables are all among its
; lambda formals, which in turn are used to form the initial gen-alist.  Then
; weak-one-way-unify-rec preserves the invariant that every variable of tterm
; is bound (as a cdr) in the alist.  One such variable is var, so we expect it
; to be a cdr of alist; hence this assertion.

     old
     (cond ((eq (car old) :?)

; We extend alist in place in order to streamline the ultimate application of
; sublis-expr.

            (cond ((mv-marker-type-p sterm)

; If sterm represents multiple values, then we do not want to generate a
; binding of the form (var sterm), since that would be illegal; and even if it
; were made legal, ultimately we would be substituting a variable, var, where a
; multiple-value expression, sterm, formerly occurred -- which would likely
; generate a syntactic error in the ultimate definition.

                   (mv nil alist))
                  (t
                   (mv var (extend-gen-alist1 sterm var alist)))))
           (t (mv (if (dumb-occur (car old) sterm)
                      (subst-expr var (car old) sterm)
                    nil)
                  alist))))))

(defun mv-nths-p (mv-var mv-nths k)
  (cond ((endp mv-nths) t)
        (t (let ((term (car mv-nths)))
             (and (ffn-symb-p term 'mv-nth)
                  (quotep (fargn term 1))
                  (eql k (unquote (fargn term 1)))
                  (eq mv-var (fargn term 2))
                  (mv-nths-p mv-var (cdr mv-nths) (1+ k)))))))

(defun adjust-sterm-for-tterm (tterm sterm)

; This function can return a term logically equivalent to sterm that is a
; closer syntactic match to tterm.  (But it doesn't introduce lambdas into
; sterm; for that, see lambdafy-rec.)  Otherwise, it returns nil.

; Since (unlike directed-untranslate-rec) we don't have uterm as an input, we
; can't call directed-untranslate-drop-disjuncts or
; directed-untranslate-drop-conjuncts here.  We might consider adding such
; functionality here on behalf of the present function's call from
; weak-one-way-unify.  But then maybe a flag should say whether we're calling
; this function on behalf of weak-one-way-unify, where we want to do such
; drops, or directed-untranslate, where we don't want the present function to
; do that (since directed-untranslate already invokes
; directed-untranslate-drop-disjuncts and directed-untranslate-drop-conjuncts).

  (mv-let
    (flg sterm)
    (case-match tterm

; Some clauses below are dodgy for the following reason.  Recall that normally
; we think of sterm as a simplified term.  So if tterm is, say (if (atom x) y
; z), and sterm is (if (consp x) z y), then why is it OK to re-introduce atom
; into the result?  After all, maybe (definitely) atom expanded, introducing
; consp, and we would be undoing that simplification.  However, we don't feel
; too bad about that, because the goal of directed-untranslate is presumably to
; preserve structure, and atom is in the list
; *expandable-boot-strap-non-rec-fns*, so it can't truly be disabled -- it's
; more like a macro in that sense than a function.

      (('if ('not (not-consp &)) & &)
       (cond
        ((member-eq not-consp '(endp atom))
         (case-match sterm
           (('if ('consp y) stbr sfbr)
            (mv t (fcons-term* 'if
                               (fcons-term* 'not (fcons-term* not-consp y))
                               stbr
                               sfbr)))
           (('if ('not ('consp y)) stbr sfbr)
            (mv t (fcons-term* 'if
                               (fcons-term* 'not (fcons-term* not-consp y))
                               sfbr
                               stbr)))
           (& (mv nil sterm))))
        (t (mv nil sterm))))
      (('if (not-consp &) ttbr tfbr)
       (cond
        ((member-eq not-consp '(endp atom))
         (case-match sterm
           (('if ('consp y) stbr sfbr)
            (cond ((and (not (equal ttbr stbr))
                        (not (equal tfbr sfbr)))
                   (mv t (fcons-term* 'if
                                      (fcons-term* not-consp y)
                                      sfbr
                                      stbr)))
                  (t (mv nil sterm))))
           (('if ('not ('consp y)) stbr sfbr)
            (mv t (fcons-term* 'if
                               (fcons-term* not-consp y)
                               stbr
                               sfbr)))
           (& (mv nil sterm))))
        (t (mv nil sterm))))
      ((('lambda (mv-var)
          (('lambda formals &) . mv-nths))
        &)
       (cond ((mv-nths-p mv-var mv-nths 0)
              (case-match sterm
                ((('lambda !formals s-lambda-body) . s-args)
                 (mv t
                     `((lambda (,mv-var)
                         ((lambda ,formals ,s-lambda-body) ,@mv-nths))
                       ,(make-true-list-cons-nest s-args))))
                (& (mv nil sterm))))
             (t (mv nil sterm))))
      ((equality-fn & &)
       (cond ((and (ffn-symb-p sterm 'equal)
                   (member-eq equality-fn '(eq eql =)))
              (mv t (fcons-term equality-fn (fargs sterm))))
             (t (mv nil sterm))))
      (('null &)
       (case-match sterm
         (('not x)
          (mv t (fcons-term* 'null x)))
         (('if x *nil* *t*)
          (mv t (fcons-term* 'null x)))
         (& (mv nil sterm))))
      (('return-last ''mbe1-raw *t* x) ; ('mbt x)

; This COND branch was originally intended to assist the apt::simplify
; transformation in its handling of MBT.  That task is best handled instead by
; that transformation, which is doing so as of this writing.  However, other
; transformations apparently depend on this as well (as reported by Stephen
; Westfold), so this branch remains for now.

       (cond ((not (ffn-symb-p sterm 'return-last))
              (cond ((equal sterm x)
                     (mv t tterm))
                    ((if-tautologyp `(iff ,sterm ,x))
                     (mv t
                         (fcons-term* 'return-last
                                      ''mbe1-raw
                                      *t*
                                      sterm)))
                    ((if-tautologyp `(iff ,(dumb-negate-lit sterm) ,x))
                     (mv t
                         (fcons-term* 'not
                                      (fcons-term* 'return-last
                                                   ''mbe1-raw
                                                   *t*
                                                   (dumb-negate-lit sterm)))))
                    (t (mv nil sterm))))
             (t (mv nil sterm))))
      (& (mv nil sterm)))
    (or
     (case-match tterm
       (('if (not-or-null &) ttbr tfbr)
        (and (member-eq not-or-null '(not null))
             (case-match sterm
               (('if tst stbr sfbr)
                (case-match tst
                  (('not &) nil)
                  (('null &) nil)
                  (('if & *nil* *t*) nil)
                  (&

; It is tempting to switch branches so that the tests might match up.  But if
; the true or false branches already line up, then we don't do the swap, not
; only because it seems unnecessary but also because it will loop with a case
; below.

                   (and (not (equal ttbr stbr))
                        (not (equal tfbr sfbr))
                        (fcons-term* 'if
                                     (dumb-negate-lit tst)
                                     sfbr
                                     stbr)))))
               (& nil))))
       (& nil))

; The following is a reasonable thing to do: swap the true and false branches
; when that allows either the true branches or the false branches to match up
; between tterm and sterm.  But suppose we encounter tterm and sterm as
; (if ttest1 ttbr1 tfbr1) and (if stest stbr1 sfbr1), and now also suppose
; that later we find this tterm/sterm pair, with the same stest:
; (if ttest2 ttbr2 tfbr2) and (if stest stbr2 sfbr1).
; Quite possibly we should swap branches in both sterms, but maybe only one
; meets the criterion below.  It might be better, then, to swap neither.
; Perhaps some memoization would help, but that would make things awkward to
; get right when it's tterm2/sterm2 that meets the criteria.
#||
     (case-match tterm
       (('if & ttbr tfbr)
        (case-match sterm
          (('if stst stbr sfbr)
           (and (or (equal tfbr stbr)
                    (equal ttbr sfbr))
                (fcons-term* 'if (dumb-negate-lit stst) sfbr stbr)))
          (& nil)))
       (& nil))
||#

     (and (ffn-symb-p tterm 'not)
          (case-match sterm
            (('if x *nil* *t*)
             (dumb-negate-lit x))
            (& nil)))
     (and (ffn-symb-p tterm 'implies)

; If tterm (equivalently, uterm) is (implies & &), then use ordinary
; untranslate unless sterm is recognizable as a form of (implies x y), in which
; case recur by using directed-untranslate appropriately on x and y.

          (mv-let (flg x y)
            (case-match sterm
              (('if x ('if y *t* *nil*) *t*)
               (mv t x y))
              (('if x y *t*)
               (mv t x y))
              (('if x *t* ('if y *t* *nil*))
               (mv t (list 'not x) y))
              (&
               (mv nil nil nil)))
            (and flg
                 (fcons-term* 'implies x y))))
     (and flg sterm))))

(defun alpha-convert-lambda (formals-tail all-formals body avoid-vars acc)

; We return a term (mv new-formals new-body) so that (lambda new-formals
; new-body) is alpha-equivalent to (lambda formals body), and so that
; new-formals is disjoint from avoid-vars and, like formals, duplicate-free.

; Acc is nil at the top level.  It accumulates the new formals.

  (cond ((endp formals-tail)
         (let ((new-formals (reverse acc)))
           (mv new-formals
               (sublis-var (pairlis$ all-formals new-formals)
                           body))))
        ((member-eq (car formals-tail) avoid-vars)
         (mv-let (str n)
           (strip-final-digits (symbol-name (car formals-tail)))
           (let ((new-var (genvar (find-pkg-witness (car formals-tail))
                                  str
                                  (1+ n)
                                  avoid-vars)))
             (alpha-convert-lambda (cdr formals-tail)
                                   all-formals
                                   body
                                   (cons new-var avoid-vars)
                                   (cons new-var acc)))))
        (t
         (alpha-convert-lambda (cdr formals-tail) all-formals body
                               (cons (car formals-tail) avoid-vars)
                               (cons (car formals-tail) acc)))))

(defun lambdafy-restore1 (old-formals new-formals vars acc-formals acc-alist)

; At the top-level, acc-formals and acc-alist are nil; the discussion below is
; for such a call.

; Old-formals and new-formals have the same length.  We return a modified
; version of new-formals, obtained by replacing each member var-new with a
; corresponding member var-old of old-formals whenever var-old is not in vars.
; The idea is that we prefer old-formals but we must avoid vars.  See
; lambdafy-restore for further discussion.

  (cond ((endp old-formals)
         (mv (reverse acc-formals)
             acc-alist))
        ((member-eq (car old-formals) vars)
         (lambdafy-restore1 (cdr old-formals) (cdr new-formals) vars
                            (cons (car new-formals) acc-formals)
                            acc-alist))
        (t
         (lambdafy-restore1 (cdr old-formals) (cdr new-formals) vars
                            (cons (car old-formals) acc-formals)
                            (acons (car new-formals) (car old-formals) acc-alist)))))

(defun lambdafy-restore (old-formals new-formals body)

; We return a lambda that is alpha-equivalent to

;   (lambda (append new-formals extra-vars) body)

; where extra-vars is a duplicate-free list containing the variables occurring
; in body but not belonging to new-formals.  We replace each variable v of
; new-formals with the corresponding variable v' of old-formals (those two
; lists have the same length), but only for v' not in extra-vars.

; The motivation comes from how we use this function in (lambdafy-rec tterm
; sterm), where tterm is a lambda call.  We are trying to modify sterm so that
; it is a lambda call analogous to tterm.  Ideally the lambda-formals for
; tterm, which are the old-formals passed to the present function, would be the
; same as those for sterm, but we must avoid capture; see for example the
; example labeled "A problem with capture" near the end of this file.  So we
; first rename the formals to avoid capture, obtaining the new-formals passed
; to the present function.  Then we take the lambda computed for sterm and
; adjust it, here, to restore the old formals when there is no possibility of
; capture.

; We actually return (mv lam new-extra-vars), where lam is the new lambda and
; new-extra-vars is the extra formals of lam appended to the end of the
; modified new-formals.

; (Note that almost every example (i.e., call of local-test) in
; directed-untranslate-tests.lisp will fail if we redefine lambdafy-restore to
; return (mv (make-lambda new-formals body) nil), thus leaving new-formals
; unmodified in the result.  For an example where extra-vars is not nil, see
; the call of directed-untranslate in the example (defconst *sterm0-simp* ...)
; near the end of this file.)

  (let ((body-vars (all-vars body)))
    (mv-let (modified-formals alist)
      (lambdafy-restore1 old-formals new-formals body-vars nil nil)
      (let* ((new-body (sublis-var alist body))
             (new-extra-vars
              (set-difference-eq (all-vars new-body) modified-formals)))
        (mv (make-lambda (append? modified-formals new-extra-vars)
                         new-body)
            new-extra-vars)))))

(defun gen-alist-args (gen-alist vars)

; Gen-alist is an alist that associates terms with variables, where (u . v)
; indicates that the term u is generalized to the variable v in a term b with
; free variables var.  The goal is to produce a suitable lambda, which we might
; write as (let ( ... (v u) ... ) b'), where b' is the result of applying such
; a generalization to b.  If however v does not occur in b, we could drop the
; binding (v u).  Instead, we prefer to leave the binding (because our
; unification algorithm looks for lambdas with formals of the same length), but
; to replace u by nil, which can be useful for other routines.

  (cond ((endp gen-alist) nil)
        (t (cons (if (member-eq (cdar gen-alist) vars)
                     (caar gen-alist)
                   *nil*)
                 (gen-alist-args (cdr gen-alist) vars)))))

(mutual-recursion

(defun equal-mod-mv-list (t1 t2)
  (cond
   ((equal t1 t2) t)
   ((or (variablep t2)
        (fquotep t2))
    nil)
   ((and (eq (ffn-symb t2) 'mv-list)
         (equal-mod-mv-list t1 (fargn t2 2))))
   ((or (variablep t1)
        (fquotep t1))
    nil)
   ((flambdap (ffn-symb t1))
    (and (flambdap (ffn-symb t2))
         (equal (lambda-formals (ffn-symb t1))
                (lambda-formals (ffn-symb t2)))
         (equal-mod-mv-list (lambda-body (ffn-symb t1))
                            (lambda-body (ffn-symb t2)))
         (equal-mod-mv-list-lst (fargs t1) (fargs t2))))
   (t (and (eq (ffn-symb t1) (ffn-symb t2))
           (equal-mod-mv-list-lst (fargs t1) (fargs t2))))))

(defun equal-mod-mv-list-lst (lst1 lst2)
  (cond ((endp lst1)
         (assert$ (endp lst2) t))
        (t (and (equal-mod-mv-list (car lst1) (car lst2))
                (assert$ (consp lst2)
                         (equal-mod-mv-list-lst (cdr lst1) (cdr lst2)))))))
)

(mutual-recursion

(defun occurrence-mod-mv-list (t1 t2)

; T1 and t2 are terms.  If t1 occurs in t2, perhaps ignoring mv-list calls in
; t2, then we return such an occurrence but with those mv-list calls left in
; place.  Otherwise we return nil.  Note that list dumb-occur, we do not look
; inside quoteps.

  (cond
   ((equal-mod-mv-list t1 t2) t2)
   ((or (variablep t2)
        (fquotep t2))
    nil)
   (t (occurrence-mod-mv-list-lst t1 (fargs t2)))))

(defun occurrence-mod-mv-list-lst (t1 lst)
  (cond ((endp lst) nil)
        (t (or (occurrence-mod-mv-list t1 (car lst))
               (occurrence-mod-mv-list-lst t1 (cdr lst))))))
)

(defun lambda-subst (formals actuals term)

; Formals and actuals are in one-one correspondence.  Suppose that the
; following condition holds: for each corresponding formal and actual, either
; formal equals actual or else actual occurs in term.  Then we collect all of
; the latter cases (where also formal does not equal actual) and return the
; corresponding sublists of formals and actuals.  But if the condition fails,
; then we return (mv :fail <don't-care>).

  (cond ((endp formals) (mv nil nil))
        ((eq (car formals) (car actuals))
         (lambda-subst (cdr formals) (cdr actuals) term))
        (t (let ((found (occurrence-mod-mv-list (car actuals) term)))
             (cond (found (mv-let (f1 a1)
                            (lambda-subst (cdr formals) (cdr actuals) term)
                            (cond ((eq f1 :fail)
                                   (mv :fail nil))
                                  (t (mv (cons (car formals) f1)
                                         (cons found a1))))))
                   (t (mv :fail nil)))))))

(defun some-var-dumb-occur (lst1 term)
  (cond ((null lst1) nil)
        ((dumb-occur-var (car lst1) term) t)
        (t (some-var-dumb-occur (cdr lst1) term))))

(mutual-recursion

(defun weak-one-way-unify (tterm sterm new-formals old-formals exec-p wrld)

; See the Essay on Handling of Lambda Applications by Directed-untranslate.

; Tterm is a term all of whose free variables are among new-formals, which are
; disjoint from the free variables of sterm.  Somewhat like
; directed-untranslate, this function exploits analogies in tterm and sterm.
; This function attempts to flesh out alist to the inverse of a substitution
; that heuristically aligns sterm with tterm.  Initially alist contains pairs
; (:? . var) where each var is a distinct variable.  When the generalization of
; a subterm x of sterm by var would make sterm "more like" tterm, then that
; entry is replaced by (x . var).  Moreover, a new sterm is returned that
; reflects such substitutions.

; Ultimately, we return (mv new-sterm new-alist), where (the inverse of)
; new-alist binds the variables of new-formals (which constitutes its range) to
; terms in its domains, and new-sterm results from sterm by applying
; replacements indicated by new-alist and possibly also from introducing
; lambdas.  If B is the bindings resulting by reversing each pair in new-alist,
; then (let B new-sterm) should be provably equal to sterm.

; An interesting case is when a variable v in the range of alist receives no
; binding by weak-one-way-unify-rec, i.e., the pair (:? . v) is in the alist
; returned by weak-one-way-unify-rec.  In that case we replace :? by v, so that
; v is bound to itself.  Let us see why this choice is both sound and
; heuristically desirable.  (1) First note that our intention is to
; lambda-abstract with the inverse of new-alist; for example, if new-alist is
; ((E1 . v1) (E2 . v2)) and new-sterm is (f E1 E2) then we will produce the
; term ((lambda (v1 v2) (f v1 v2)) E1 E2).  We need this to be equivalent to (f
; E1 E2), which it will be if v1 and v2 are fresh with respect to sterm.  (2)
; Suppose that in this example, E2 is v2 and new-alist was produced by
; replacing the binding (:?  . v2) with (v2 . v2) as described above.  The term
; ((lambda (v1 v2) (f v1 v2)) E1 E2) is then ((lambda (v1 v2) (f v1 v2)) E1
; v2), which naively would seem to untranslate to (let ((v1 E1) (v2 v2)) (f v1
; v2)), but it is illuminating to see that it actually untranslates to (let
; ((v1 E1)) (f v1 (g x) v2)).  Thus, by binding v2 to itself, in effect we have
; punted on trying to bind v2, which is appropriate since
; weak-one-way-unify-rec didn't suggest a binding.

  (let ((alist (pairlis-x1 :? new-formals)))
    (mv-let (sterm? alist)
      (weak-one-way-unify-rec tterm sterm alist exec-p wrld)
      (let ((sterm (or sterm? sterm)))
        (mv sterm
            (bind-?-final alist (all-vars sterm) old-formals))))))

(defun weak-one-way-unify-rec (tterm sterm alist exec-p wrld)

; This function is just as described in weak-one-way-unify, with two
; exceptions.  First, the present function makes no attempt to add pairs using
; bind-?-final (as in weak-one-way-unify).  Second, the first value returned is
; nil if sterm has not changed.

; Invariant: Every variable free in tterm should be bound in (a cdr of) alist.

  (cond
   ((and (nvariablep sterm)
         (eq (ffn-symb sterm) 'mv-list)
         (not (and (nvariablep tterm)
                   (eq (ffn-symb tterm) 'mv-list))))
    (mv-let (new-sterm alist)
      (weak-one-way-unify-rec tterm (fargn sterm 2) alist exec-p wrld)
      (mv (and new-sterm (fcons-term* 'mv-list (fargn sterm 1) new-sterm))
          alist)))
   ((variablep tterm)
    (extend-gen-alist tterm sterm alist))
   ((fquotep tterm)
    (mv nil alist))
   ((or (variablep sterm)
        (fquotep sterm)

; At one time the following disjunct was important: we had an example where (f2
; z x1 y1) was matched to (binary-append (f3 x) y), so that x1 was bound to y
; when instead y1 should have been bound to y.  That example no longer applies;
; perhaps some other code avoids this problem.  But we leave the disjunct here
; for robustness.

        (and (not (lambda-applicationp tterm))
             (not (eql (length (fargs tterm))
                       (length (fargs sterm))))))
    (mv nil alist))
   (t
    (let* ((lambdafied-sterm
            (and (lambda-applicationp tterm)
                 (not (lambda-applicationp sterm))
                 (lambdafy-rec tterm sterm exec-p wrld)))
           (sterm (or lambdafied-sterm
                      (adjust-sterm-for-tterm tterm sterm)
                      sterm)))
      (mv-let
        (new-args new-alist)
        (weak-one-way-unify-lst (fargs tterm) (fargs sterm) alist exec-p wrld)
        (let ((new-sterm?
               (and (or lambdafied-sterm new-args)
                    (fcons-term (ffn-symb sterm)
                                (or new-args
                                    (fargs sterm))))))
          (mv new-sterm? new-alist)))))))

(defun weak-one-way-unify-lst (tterm-lst sterm-lst alist exec-p wrld)
  (cond ((equal (length tterm-lst)
                (length sterm-lst))
         (weak-one-way-unify-lst-rec tterm-lst sterm-lst alist exec-p wrld))
        (t (mv nil alist))))

(defun weak-one-way-unify-lst-rec (tterm-lst sterm-lst alist exec-p wrld)
  (cond ((endp sterm-lst) (mv nil alist))
        (t (mv-let (new-sterm alist)
             (weak-one-way-unify-rec (car tterm-lst)
                                     (car sterm-lst)
                                     alist exec-p wrld)
             (mv-let (new-sterm-lst alist)
               (weak-one-way-unify-lst-rec (cdr tterm-lst)
                                           (cdr sterm-lst)
                                           alist exec-p wrld)
               (mv (cond (new-sterm
                          (cons new-sterm
                                (or new-sterm-lst
                                    (cdr sterm-lst))))
                         (new-sterm-lst
                          (cons (car sterm-lst)
                                new-sterm-lst))
                         (t nil))
                   alist))))))

(defun lambdafy-rec (tterm sterm exec-p wrld)

; See the Essay on Handling of Lambda Applications by Directed-untranslate.

; If the return value lterm is not nil, then lterm is a term that is provably
; equivalent to sterm, but we heuristically attempt to match the lambda
; structure of tterm.  We make no attempt to have decent heuristics unless
; sterm is free of lambda applications.  We do, however, try to handle the case
; that sterm has different free variables than those in tterm since when we
; recur, we match sterms against lambda-bodies of tterms.

  (cond
   ((or (variablep tterm)
        (fquotep tterm)
        (not (flambdap (ffn-symb tterm))))
    sterm)
   (t

; There are two cases below, (or case1 case2).  Case2 is the normal case.  In
; case1 we deal with the case that tterm is of the form (let ((v u)) b) -- more
; precisely, ((lambda (v) b) u) -- where u occurs in sterm and v does not.  In
; that case we decide right now that the result will be of the form ((lambda
; (v) body) u), for some body.  We actually handle the case of more than one
; lambda formal, provided every lambda formal is bound to itself

    (or (case-match tterm
          ((('lambda formals body) . actuals)
           (mv-let (f1 a1)
             (lambda-subst formals actuals sterm)
             (and (not (eq f1 :fail))
                  f1 ; optimization
                  (not (some-var-dumb-occur f1 sterm))
                  (let* ((gen-sterm (sublis-expr (pairlis$ a1 f1) sterm))
                         (lambdafied-sterm
                          (lambdafy-rec body gen-sterm exec-p wrld))
                         (extra-vars ; to create a proper lambda application
                          (set-difference-eq (all-vars lambdafied-sterm)
                                             formals)))
                    `((lambda ,(append? formals extra-vars)
                        ,lambdafied-sterm)
                      ,@(append? (if exec-p
                                     (remake-executable-lst actuals wrld)
                                   actuals)
                                 extra-vars)))))))
        (let* ((tfn (ffn-symb tterm))
               (old-tformals (lambda-formals tfn))
               (tfn-body (lambda-body tfn)))
          (mv-let (new-tformals new-tbody)
            (alpha-convert-lambda old-tformals old-tformals tfn-body
                                  (all-vars sterm)
                                  nil)
            (mv-let (new-sterm gen-alist)
              (weak-one-way-unify new-tbody
                                  sterm
                                  new-tformals
                                  old-tformals
                                  exec-p
                                  wrld)

; We must basically ignore tterm at this point.  Its body helped us to
; generalize sterm to new-sterm and record that generalization in gen-alist.
; Because we were careful to use fresh variables in new-formals to avoid
; capture, we can bind those variables with gen-alist to create a
; lambda-application that is equivalent to sterm.  See also weak-one-way-unify.

              (let* ((new-tformals (strip-cdrs gen-alist))

; Since weak-one-way-unify(-rec) substitutes into sterm as it updates
; gen-alist, one might expect the following sublis-expr to be unnecessary.  But
; suppose that a term u only matches a variable v at the second occurrence of
; u.  Then we need to generalize that first occurrence of u to v as well.  We
; have seen this happen in practice [obscure note: see first S.W. example in
; Kestrel simplify-defun test file].

                     (new-body (sublis-expr gen-alist new-sterm))
                     (new-args (gen-alist-args gen-alist (all-vars new-body))))
                (mv-let (lam new-extra-vars)

; Replace some variables in new-tformals by corresponding variables in
; old-tformals when that is sound.

                  (lambdafy-restore old-tformals new-tformals new-body)
                  (fcons-term lam
                              (append?
                               (if exec-p
                                   (remake-executable-lst new-args wrld)
                                 new-args)
                               new-extra-vars)))))))))))

(defun lambdafy (tterm sterm exec-p wrld)
  (let ((tterm

; We expect that, for example, a call of member in (the user-level term that
; led to) tterm will become a call of member-equal in sterm.  More generally,
; all guard-holders will likely be expanded away in sterm.  Consider the
; following example, where the first argument is the translation of
; (member x (fix-true-listp lst)).

;  (lambdafy
;   '((lambda (x l)
;       (return-last 'mbe1-raw
;                    (member-eql-exec x l)
;                    (return-last 'progn
;                                 (member-eql-exec$guard-check x l)
;                                 (member-equal x l))))
;     x (fix-true-listp lst) nil (w state))
;   '(member-equal x lst))

; Without the call of remove-guard-holders just below, the result is as
; follows.

;   ((LAMBDA (X L LST) (MEMBER-EQUAL X LST))
;    X L LST)

; Thus, we are making it easier to get a nice result from callers of lambdafy,
; in particular, directed-untranslate-rec.

         (remove-guard-holders tterm wrld)))
    (lambdafy-rec tterm sterm exec-p wrld)))
)

(defun extend-let (uterm tterm)
  (assert$ (and (consp uterm)
                (eq (car uterm) 'let)
                (lambda-applicationp tterm))
           (let ((missing (set-difference-eq (lambda-formals (ffn-symb tterm))
                                             (strip-cars (cadr uterm)))))
             (cond (missing
                    `(let ,(append (cadr uterm)
                                   (pairlis$ missing (pairlis$ missing nil)))
                       ,@(cddr uterm)))
                   (t uterm)))))

(defun drop-unused-formals-1 (formals actuals unused-vars)
  (cond ((endp formals)
         (assert$ (endp actuals) (mv nil nil)))
        ((member-eq (car formals) unused-vars)
         (drop-unused-formals-1 (cdr formals) (cdr actuals) unused-vars))
        (t (mv-let (f2 a2)
             (drop-unused-formals-1 (cdr formals) (cdr actuals) unused-vars)
             (mv (cons (car formals) f2)
                 (cons (car actuals) a2))))))

(mutual-recursion

(defun drop-unused-formals (term)
  (cond ((or (variablep term)
             (fquotep term))
         term)
        ((flambdap (ffn-symb term)) ; ((lambda formals body) . actuals)
         (let* ((lam (ffn-symb term))
                (formals (lambda-formals lam))
                (body (drop-unused-formals (lambda-body lam)))
                (unused-vars (set-difference-eq formals (all-vars body)))
                (actuals (fargs term)))
           (mv-let (formals2 actuals2)
             (cond ((null unused-vars) ; optimization
                    (mv formals actuals))
                   (t (drop-unused-formals-1 formals actuals unused-vars)))
             (fcons-term (make-lambda formals2 body)
                         actuals2))))
        (t (fcons-term (ffn-symb term)
                       (drop-unused-formals-lst (fargs term))))))

(defun drop-unused-formals-lst (x)
  (cond ((endp x) nil)
        (t (cons (drop-unused-formals (car x))
                 (drop-unused-formals-lst (cdr x))))))
)

(defun du-untranslate (term iff-flg wrld)

; This version of untranslate removes empty let bindings.  At one time during
; development of directed-untranslate it made a difference to do so; even if
; that's no longer necessary, it seems harmless to redress that grievance in
; case this ever comes up.

  (let ((ans (remove-mv-marker-from-untranslated-term
              (untranslate (drop-unused-formals term) iff-flg wrld))))
    (case-match ans
      (('let 'nil body)
       body)
      (& ans))))

(defun make-let-smart-bindings (bindings vars)
  (cond ((endp bindings) nil)
        ((member-eq (caar bindings) vars)
         (cons (car bindings)
               (make-let-smart-bindings (cdr bindings) vars)))
        (t
         (make-let-smart-bindings (cdr bindings) vars))))

(defun make-let-smart (bindings body vars)

; Body is an untranslation of a term whose free vars are vars.  We form a let
; term where we delete each variable bound in bindings that is not in vars.

  (let ((new-bindings (make-let-smart-bindings bindings vars)))
    (cond ((null new-bindings) body)
          (t (make-let new-bindings body)))))

(mutual-recursion

(defun all-vars-for-real1-lambda (formals actuals body-vars ans)
  (cond ((endp formals) ans)
        ((member-eq (car formals) body-vars)
         (all-vars-for-real1-lambda (cdr formals) (cdr actuals) body-vars
                                    (all-vars-for-real1 (car actuals) ans)))
        (t (all-vars-for-real1-lambda (cdr formals) (cdr actuals) body-vars
                                      ans))))

(defun all-vars-for-real1 (term ans)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp ans))
                  :mode :program))
  (cond ((variablep term)
         (add-to-set-eq term ans))
        ((fquotep term) ans)
        ((flambda-applicationp term)
         (all-vars-for-real1-lambda (lambda-formals (ffn-symb term))
                                    (fargs term)
                                    (all-vars-for-real1
                                     (lambda-body (ffn-symb term)) nil)
                                    ans))
        (t (all-vars-for-real1-lst (fargs term) ans))))

(defun all-vars-for-real1-lst (lst ans)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (symbol-listp ans))
                  :mode :program))
  (cond ((endp lst) ans)
        (t (all-vars-for-real1-lst (cdr lst)
                                   (all-vars-for-real1 (car lst) ans)))))

)

(defun all-vars-for-real (term)

; This variant of all-vars returns a subset V of what is returned by all-vars,
; sufficient so that V determines the value of term: If s1 and s2 are two
; substitutions that agree on V, then term/s1 = term/s2.

; Consider for example the case that term is:

;   ((LAMBDA (R C) (BINARY-APPEND (F1 C) C)) ALL-R C)

; Since R does not occur in the body, ALL-R is not in the beta-reduction of
; this term.  So we do not include ALL-R in the result -- its value is
; irrelevant to the value of term.

  (all-vars-for-real1 term nil))

(defun uterm-values-len (x wrld)

; X is an untranslated term.  We return 1 if we cannot make a reasonable guess
; about the stobjs-out of x.

; Note that we currently assume that x does not include lambda applications.
; If x was produced by any reasonable untranslation routine, that seems to be a
; reasonable assumption.  We can probably add handling of lambdas if necessary.

  (declare (xargs :guard (plist-worldp wrld)
                  :ruler-extenders (if)))
  (or (and (consp x)
           (not (eq (car x) 'quote))
           (true-listp x)
           (cond ((eq (car x) 'mv)
                  (length (cdr x)))
                 ((eq (car x) 'let)
                  (uterm-values-len (car (last x)) wrld))

; Keep the following code in sync with stobjs-out.

                 ((or (not (symbolp (car x)))
                      (member-eq (car x) *stobjs-out-invalid*))
                  1)
                 (t (len (getpropc (car x) 'stobjs-out '(nil) wrld)))))
      1))

(defun du-nthp (n xn x)

; Xn and x are untranslated terms.  It is permissible (and desirable) to return
; t if xn is provably equal to (nth n x).  Otherwise, return nil.

; We could improve this function by returning t in more cases, for example:
; (nthp 1 '(cadr x) x).

  (declare (xargs :guard (natp n)))
  (cond ((and (true-listp xn) ; case (DU-NTHP n ([MV-]NTH n MV) MV)
              (member-eq (car xn) '(nth mv-nth))
              (eql (cadr xn) n)
              (equal (caddr xn) x))
         t)
        ((and (true-listp xn) ; case (DU-NTHP n ([MV-]NTH n (MV-LIST _ MV)) MV)
              (member-eq (car xn) '(nth mv-nth))
              (eql (cadr xn) n)
              (let ((tmp (caddr xn)))
                (case-match tmp
                  (('mv-list & !x) t)
                  (& nil))))
         t)
        ((and (consp xn)
              (consp (cdr xn))
              (eq (car xn) 'hide))
         (du-nthp n (cadr xn) x))
        ((zp n) ; xn is (car x)
         (and (consp xn)
              (consp (cdr xn))
              (eq (car xn) 'car)
              (equal (cadr xn) x)))
        (t nil)))

(defun du-nth-index (xn x)

; Xn and x are untranslated terms.  It is permissible (and desirable) to return
; the natural number n if xn is provably equal to (nth n x).  Otherwise, return
; nil.

; We could improve this function by returning non-nil in more cases, for
; example: (du-nth '(cadr x) x) could equal 1.

  (declare (xargs :guard (symbolp x)))
  (cond
   ((and (true-listp xn) ; case (DU-NTH-INDEX ([MV-]NTH n MV) MV)
         (member-eq (car xn) '(nth mv-nth))
         (natp (cadr xn))
         (eq (caddr xn) x))
    (cadr xn))
   ((and (true-listp xn) ; case (DU-NTH-INDEX ([MV-]NTH n (MV-LIST _ MV)) MV)
         (member-eq (car xn) '(nth mv-nth))
         (natp (cadr xn))
         (let ((tmp (caddr xn)))
           (case-match tmp
             (('mv-list & !x) t)
             (& nil))))
    (cadr xn))
   ((and (consp xn)
         (consp (cdr xn))
         (eq (car xn) 'hide))
    (du-nth-index (cadr xn) x))
   ((and ; xn is (car x)
     (consp xn)
     (consp (cdr xn))
     (eq (car xn) 'car)
     (eq (cadr xn) x))
    0)
   (t nil)))

(defun du-make-mv-let-aux (bindings formals mv-var n acc-vars ignore-vars)

; See du-make-mv-let.  Here we check that bindings are as expected for
; untranslation of the translation of an mv-let.

  (declare (xargs :guard (and (doublet-listp bindings)
                              (symbol-listp formals)
                              (natp n)
                              (symbolp mv-var)
                              (true-listp acc-vars)
                              (true-listp ignore-vars))))
  (cond ((endp formals) (mv t (reverse acc-vars) (reverse ignore-vars)))
        ((endp bindings)
         (mv t (revappend acc-vars formals) (revappend ignore-vars formals)))
        (t (let* ((b (car bindings))
                  (xn (cadr b))
                  (index (du-nth-index xn mv-var)))
             (cond ((eql index n)
                    (du-make-mv-let-aux (cdr bindings)
                                        (cdr formals)
                                        mv-var
                                        (1+ n)
                                        (cons (car b) acc-vars)
                                        ignore-vars))
                   ((and (natp index) ; equivalently, index is non-nil
                         (< n index)

; We check that the newly-ignored formal is not among the bound variables.  It
; might be very difficult to find an example that fails this check!

                         (not (member-eq (car formals) acc-vars))
                         (not (assoc-eq (car formals) bindings)))
                    (du-make-mv-let-aux bindings
                                        (cdr formals)
                                        mv-var
                                        (1+ n)
                                        (cons (car formals) acc-vars)
                                        (cons (car formals) ignore-vars)))
                   (t (mv nil nil nil)))))))

(defun make-mv-args (uterm k)

; Uterm is an untranslated term.  Return a list of untranslated terms of length
; k such that the application of mv to that list is provably equal to uterm, or
; else return nil.  The intended use is for when directed-untranslate is
; applied to a first argument of the form (mv-let ...)  to produce:

; ('LET ((mv-var mv-let-body)) ('LET & &))

; We want to call du-make-mv-let to reconstruct a form (mv-let & body &), but
; the problem is that body, having been produced by directed-untranslate, might
; not have suitable stobjs-out -- for example, it might be (cons & &), which is
; a single value.  Such a call of cons might, for example, be generated because
; the sterm given to directed-untranslate comes from function
; adjust-sterm-for-tterm, which may call make-true-list-cons-nest to produce a
; call of cons.

; If mv-let-body is already suitable as body, or if we don't see how to put
; mv-let-body into suitable form, we return nil here.  Otherwise we return a
; list (u1 ... uk) so that we can replace mv-let-body by (mv u1 ... uk).

  (declare (xargs :guard (posp k)))
  (cond ((atom uterm) nil)
        (t (case-match uterm
             (('quote evg)
              (and (true-listp evg)
                   (equal (length evg) k)
                   (maybe-kwote-lst evg)))
             (('mv . &) ; no need to convert
              nil)
             (('list . y)
              (and (true-listp y) ; always true?
                   (equal (length y) k)
                   y))
             (('cons x y)
              (cond ((= k 1)
                     (and (member-equal y '(nil 'nil))
                          (list x)))
                    (t (let ((args (make-mv-args y (1- k))))
                         (and args (cons x args))))))
             (('list* ('quote x))
              (cond ((= k 1)
                     (and (consp x)
                          (null (cdr x))
                          (list (maybe-kwote (car x)))))
                    (t (and (consp x)
                            (let ((args (make-mv-args `(list* (quote ,(cdr x)))
                                                      (1- k))))
                              (and args
                                   (cons (maybe-kwote (car x)) args)))))))
             (('list* x . y)
              (cond ((= k 1)
                     (and (equal y '(nil))
                          (list x)))
                    (t (let ((args (make-mv-args (cons 'list* y) (1- k))))
                         (and args (cons x args))))))
             (& nil)))))

(defun du-make-mv-let (formals x wrld state-vars)

; This function returns an untranslated term that is provably equal to the
; input untranslated term, x.  Formals is used heuristically; in practice, x is
; derived from a call of directed-untranslate-rec whose uterm is (mv-let
; formals ...).

; The following simple evaluation helped to guide us in writing this code.

;   ACL2 !>:trans (mv-let (x y) (mv x y) (declare (ignore y)) (append x x))
;
;   ((LAMBDA (MV)
;            ((LAMBDA (X Y) (BINARY-APPEND X X))
;             (MV-NTH '0 MV)
;             (HIDE (MV-NTH '1 MV))))
;    (CONS X (CONS Y 'NIL)))
;
;   => *
;
;   ACL2 !>(untranslate '((LAMBDA (MV)
;                                 ((LAMBDA (X Y) (BINARY-APPEND X X))
;                                  (MV-NTH '0 MV)
;                                  (HIDE (MV-NTH '1 MV))))
;                         (CONS X (CONS Y 'NIL)))
;                        nil (w state))
;   (LET ((MV (LIST X Y)))
;        (LET ((X (MV-NTH 0 MV))
;              (Y (HIDE (MV-NTH 1 MV))))
;             (APPEND X X)))
;   ACL2 !>

; Here is evidence that we got the guards right.

;   (verify-termination du-nth-index)
;   (verify-termination du-make-mv-let-aux)
;   (verify-termination uterm-values-len)
;
;   (defthm doublet-listp-forward-to-alistp
;     (implies (doublet-listp x)
;              (alistp x))
;     :rule-classes :forward-chaining)
;
;   (defthm doublet-listp-implies-all->=-len
;     (implies (doublet-listp x)
;              (all->=-len x 2))
;     :hints (("Goal" :expand ((LEN (CAR X))))))
;
;   ; Now redefine du-make-mv-let by removing the call of program-mode function
;   ; translate-cmp and adding (declare (ignore state-vars)).
;
;   (verify-termination du-make-mv-let)

  (declare (xargs :guard (and (symbol-listp formals)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))))
  (or (case-match x
        (('LET ((mv-var mv-let-body))
               ('LET bindings main-body))

; In the example above, directed-untranslate would already have replaced (LIST
; X Y) by (MV X Y).  So we can expect mv-let-body to be a cons whose car is
; either MV or else an untranslated term whose list of returned values is of
; the same length as bindings.

         (and (symbolp mv-var)         ; always true?
              (doublet-listp bindings) ; always true?
              (let* ((mv-let-body (case-match mv-let-body
                                    (('mv-list & y)
                                     y)
                                    (& mv-let-body)))
                     (formals-len (length formals))
                     (mv-let-body-args (make-mv-args mv-let-body formals-len))
                     (mv-let-body (if mv-let-body-args
                                      (cons 'mv mv-let-body-args)
                                    mv-let-body))
                     (values-len (uterm-values-len mv-let-body wrld))
                     (bindings-len (length bindings)))
                (and (= values-len formals-len) ; always true?
                     (<= bindings-len values-len)
                     (mv-let (flg vars ignore-vars)
                       (du-make-mv-let-aux bindings formals mv-var 0 nil nil)
                       (and flg

; We check that the ignored variables are not free in main-body.  We need to
; translate main-body in order to do that check.

                            (or
                             (null ignore-vars)
                             (mv-let (erp tbody)
                               (translate-cmp main-body
                                              nil ; stobjs-out
                                              nil ; logic-modep (don't care)
                                              t   ; known-stobjs
                                              'du-make-mv-let ; ctx
                                              wrld
                                              state-vars)
                               (and (null erp)
                                    (not (intersectp-eq ignore-vars tbody)))))
                            `(mv-let ,vars
                               ,mv-let-body
                               ,@(and ignore-vars
                                      `((declare (ignore ,@ignore-vars))))
                               ,main-body)))))))
        (('LET bindings main-body)
         (and (doublet-listp bindings) ; always true?
              (consp (cdr bindings))
              `(mv-let ,(strip-cars bindings)
                 (mv ,@(strip-cadrs bindings))
                 ,main-body))))

; We failed to construct an mv-let term.  At least undo the damage from
; creating a LET-binding (let ((mv (mv ...))) ...).

      (case-match x
        (('let ((mv-var ('mv . a))) . b)
         `(let ((,mv-var (list ,@a))) ,@b))
        (& x))))

(defun expand-mv-let (uterm tterm)

; Uterm is an untranslated term (mv-let ...).  Tterm is the translation of
; uterm.  So we have for example:

; uterm
;   (mv-let (x y) (foo u v) (append x y))

; tterm
;   ((lambda (mv)
;      ((lambda (x y) (binary-append x y))
;       (mv-nth '0 mv)
;       (mv-nth '1 mv)))
;    (foo u v))

; We expand away the LET from uterm.  In the example above, we get:

;   ACL2 !>(let ((uterm '(mv-let (x y) (mv x y) (append x y)))
;                (tterm '((lambda (mv) ((lambda (x y) (binary-append x y))
;                                       (mv-nth '0 mv)
;                                       (mv-nth '1 mv)))
;                         (cons x (cons y 'nil)))))
;            (expand-mv-let uterm tterm))
;   (LET ((MV (MV X Y)))
;        (LET ((X (MV-NTH 0 MV)) (Y (MV-NTH 1 MV)))
;             (APPEND X Y)))
;   ACL2 !>

; A subtlety, noticed by Stephen Westfold and incorporated into
; directed-untranslate-tests.lisp, is that the free variables bound with mv in
; tterm might not appear in the same order as in the translation of the
; modified uterm, unless we are careful.  So, we are careful!

  (or (case-match uterm
        (('mv-let vars mv-let-body . rest)
         (case-match tterm
           ((('lambda (mv-var . other-vars)
               (('lambda lvars &) . &))
             & . other-vars)
            (and (equal vars (take (length vars) lvars))
                 `(let ((,mv-var ,mv-let-body)
                        ,@(pairlis$ other-vars
                                    (pairlis$ other-vars nil)))
                    (let ,(make-mv-nths vars mv-var 0)
                      ,@(butlast rest 1)
                      ,(car (last rest)))))))))
      (er hard? 'expand-mv-let
          "Implementation error: Unexpected uterm,~|~x0"
          uterm)))

(defun prog2$-to-progn$ (uterm)
  (case-match uterm
    (('prog2$ x y)
     (let ((y2 (prog2$-to-progn$ y)))
       (case-match y2
         (('progn$ . rest)
          (list* 'progn$ x rest))
         (& (list 'progn$ x y)))))
    (& uterm)))

(defun append-dcls (x y)

; Imagine we have (declare . x) and (declare . y).  We wish to combine these
; into a single declare form that is "pretty".

  (cond ((endp x) y)
        (t (let* ((y (append-dcls (cdr x) y))
                  (key (caar x))  ; ignore, ignorable, type ...
                  (vars (cdar x)) ; variables for ignore, ignorable, type ...
                  (d (assoc-eq key y)))
             (cond (d (put-assoc-eq key
                                    (union-eq vars (cdr d))
                                    y))
                   (t (cons (car x) y)))))))

(defun reconstruct-let* (bindings x)

; Return a term equivalent to x, but using bindings as a guide to try to create
; a let* term.  The intended use is where x is a simplification of some let*
; term with the indicated bindings, some of which may have disappeared in
; simplifying to x.

; Example:

;   ACL2 !>:trans1 (let* ((x 3) (y 5) (z 6)) (declare (ignore x y)) z)
;    (LET ((X 3))
;         (DECLARE (IGNORE X))
;         (LET ((Y 5))
;              (DECLARE (IGNORE Y))
;              (LET ((Z 6)) Z)))
;   ACL2 !>

; Then for that result, r, (reconstruct-let* '((x 3) (y 5) (z 6)) r)
; is the original let*.

  (cond ((endp bindings) x)
        (t (let ((var (caar bindings)))
             (case-match x
               (('let ((!var &)) y)
                (let ((x2 (reconstruct-let* (cdr bindings) y)))
                  (case-match x2
                    (('let* b2 . r2)
                     `(let* ,(append (cadr x) b2)
                        ,@r2))
                    (& `(let* ,(cadr x) ,x2)))))
               (('let ((!var &)) ('declare . d) y)
                (let ((x2 (reconstruct-let* (cdr bindings) y)))
                  (case-match x2
                    (('let* b . r)
                     `(let* ,(append (cadr x) b)
                        ,@(case-match r
                            ((('declare . d2) . r2)
                             `((declare ,@(append-dcls d d2)) ,@r2))
                            (& `((declare ,@d) ,@r)))))
                    (& `(let* ,(cadr x) ,x2)))))
               (&
; We proceed in the hope that (car bindings) was dropped during
; simplification.
                (reconstruct-let* (cdr bindings) x)))))))

(mutual-recursion

(defun directed-untranslate-rec (uterm tterm sterm iff-flg lflg exec-p wrld)

; Tterm is the translation of uterm (as may be checked by check-du-inv).  We
; return a form whose translation, with respect to iff-flg, is provably equal
; to sterm.  There may be many such untranslations, but we attempt to return
; one that is similar in structure to uterm.  See also directed-untranslate.

; When lflg is true, we allow ourselves to modify sterm to match the lambda
; applications in tterm.

; When exec-p is true we assume that sterm has already been made executable
; (with make-executable), and we try to produce an executable result.

  (check-du-inv
   uterm tterm wrld
   (cond

; The following case is sound, and very reasonable.  However, we anticipate
; applying this function in cases where uterm is not a nice untranslation.
; This may change in the future.

;   ((equal tterm sterm)
;    uterm)

    ((or (variablep tterm)
         (fquotep tterm)
         (atom uterm))
     (du-untranslate sterm iff-flg wrld))
    ((ffn-symb-p sterm 'mv-marker)
     (let* ((ans (directed-untranslate-rec uterm tterm
                                           (fargn sterm 2)
                                           iff-flg lflg exec-p wrld))
            (n (du-untranslate (fargn sterm 1) nil wrld))
            (args (mv-marker-args n ans)))
       (cond (args (cons 'mv args))
             (t ans))))
    ((ffn-symb-p sterm 'mv-list)
     (let ((ans (directed-untranslate-rec uterm tterm
                                          (fargn sterm 2)
                                          iff-flg lflg exec-p wrld))
           (n (du-untranslate (fargn sterm 1) nil wrld)))
       (list 'mv-list n ans)))
    ((case-match uterm
       (('progn$ & & . &) t))
     (let ((ans (directed-untranslate-rec
                 `(prog2$ ,(cadr uterm)
                          (progn$ ,@(cddr uterm)))
                 tterm sterm iff-flg lflg exec-p wrld)))
       (prog2$-to-progn$ ans)))
    ((and (consp uterm)
          (eq (car uterm) 'progn$)) ; (progn$ &)
     (assert$ (null (cddr uterm))
              (directed-untranslate-rec
               (cadr uterm)
               tterm sterm iff-flg lflg exec-p wrld)))
    ((and (consp uterm)
          (eq (car uterm) 'mv-let))
     (assert$
      (and (consp (cdr uterm))
           (symbol-listp (cadr uterm)))
      (du-make-mv-let (cadr uterm)
                      (directed-untranslate-rec (expand-mv-let uterm tterm)
                                                tterm sterm iff-flg lflg
                                                exec-p wrld)
                      wrld
                      (default-state-vars nil))))
    ((and (consp uterm) (eq (car uterm) 'let*))

; Warning: If you change this, consider changing the handling of b*
; in directed-untranslate-b*.

     (case-match uterm
       (('let* () . &)
        (directed-untranslate-rec
         (car (last uterm))
         tterm sterm iff-flg lflg exec-p wrld))
       (('let* ((& &)) . &)
        (let ((x (directed-untranslate-rec
                  (cons 'let (cdr uterm))
                  tterm sterm iff-flg lflg exec-p wrld)))
          (case-match x
            (('let ((& &)) . &)
             (cons 'let* (cdr x)))
            (& x))))
       (('let* bindings . &)

; At one time we avoided calling macroexpand1-cmp below, instead doing the
; expansion ourselves.  But we threw away declarations, and that caused a
; violation of check-du-inv-fn because an ignore declaration was needed to
; match a HIDE in tterm.

        (mv-let (erp let-term)
          (macroexpand1-cmp uterm 'directed-untranslate-rec wrld
                            (default-state-vars nil))
          (and (not erp) ; always true?
               (let ((x (directed-untranslate-rec
                         let-term
                         tterm sterm iff-flg lflg exec-p wrld)))
                 (reconstruct-let* bindings x)))))
       (& ; impossible
        (er hard 'directed-untranslate-rec
            "Implementation error: unexpected uterm, ~x0."
            uterm))))
    ((and (consp uterm)
          (eq (car uterm) 'b*)

; Warning: If you change this, consider changing the case for let* in
; directed-untranslate-rec.

          (directed-untranslate-b* uterm tterm sterm iff-flg lflg exec-p
                                   wrld)))
    ((and (lambda-applicationp tterm)
          (lambda-applicationp sterm)
          (consp uterm)
          (eq (car uterm) 'let) ; would be nice to handle b* as well
          (let* ((tformals (lambda-formals (ffn-symb tterm)))
                 (len-tformals (length tformals))
                 (sformals (lambda-formals (ffn-symb sterm))))
            (and (<= len-tformals (length sformals))

; The following condition occurs when the extra sformals are bound to
; themselves.  Perhaps it is too restrictive, but it may be common and it is
; easiest to consider just this case, where we basically ignore those extra
; sformals.

                 (equal (nthcdr len-tformals sformals) ; extra sformals
                        (nthcdr len-tformals (fargs sterm))))))

; See the Essay on Handling of Lambda Applications by Directed-untranslate.

; We expect the problem to look like this:

;   uterm = (let (pairlis$ uformals uactuals) ubody)
;   tterm = ((lambda tformals tbody) tactuals)
;   sterm = ((lambda sformals sbody) sactuals)

     (let ((uterm (extend-let uterm tterm))) ; bind missing formals at the end
       (or
        (case-match uterm
          (('let let-bindings . let-rest)
           (and (symbol-doublet-listp let-bindings)  ; always true?
                (let* ((ubody (car (last let-rest))) ; ignore declarationsa
                       (tbody (remove-declare-effects
; Throw away the effects of type declarations.
                               (lambda-body (ffn-symb tterm))))
                       (sbody (lambda-body (ffn-symb sterm)))
                       (uformals (strip-cars let-bindings))
                       (sformals-all (lambda-formals (ffn-symb sterm)))
                       (tformals (lambda-formals (ffn-symb tterm)))
                       (len-tformals (length tformals))
                       (sformals-main (take len-tformals sformals-all))
                       (sargs-main (take len-tformals (fargs sterm)))
                       (uactuals (strip-cadrs let-bindings))
                       (tactuals (collect-by-position uformals
                                                      tformals
                                                      (fargs tterm)))
                       (sactuals (collect-by-position uformals
                                                      tformals
                                                      sargs-main))
                       (args (directed-untranslate-lst
                              uactuals
                              tactuals
                              (if exec-p
                                  (remake-executable-lst sactuals wrld)
                                sactuals)
                              nil lflg exec-p wrld))
                       (body (directed-untranslate-rec
                              ubody tbody sbody iff-flg lflg exec-p wrld))
                       (bindings (collect-non-trivial-bindings
                                  sformals-main
                                  args)))
                  (if bindings
                      (make-let-smart bindings body (all-vars-for-real sbody))
                    body)))))
        (du-untranslate sterm iff-flg wrld))))
    ((or (variablep sterm)
         (fquotep sterm))
     (du-untranslate sterm iff-flg wrld))
    ((and (eq (ffn-symb sterm) 'return-last)
          (directed-untranslate-return-last uterm tterm sterm iff-flg lflg
                                            exec-p wrld)))
    ((and (consp uterm)
          (member-eq (car uterm) '(er cw))
          (true-listp (cdr uterm)) ; always true?
          (cond ((eq (car uterm) 'er)
                 (and (member-eq (cadr uterm) '(hard hard?))
                      (member-eq (ffn-symb tterm) '(illegal hard-error))
                      (member-eq (ffn-symb sterm) '(illegal hard-error))))
                (t ; (eq (car uterm) 'cw)
                 (and (eq (ffn-symb tterm) 'fmt-to-comment-window)
                      (eq (ffn-symb sterm) 'fmt-to-comment-window)
                      (equal (fargn sterm 3) *0*)
                      (equal (fargn sterm 4) *nil*)
                      (equal (fargn sterm 5) *nil*))))
          (let ((uargs (if (eq (car uterm) 'cw)
                           (cddr uterm)
                         (cddddr uterm)))
                (targs (unmake-formal-pairlis2
                        (if (eq (car uterm) 'cw)
                            (fargn tterm 2)
                          (fargn tterm 3))
                        '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))
                (sargs (unmake-formal-pairlis2
                        (if (eq (car uterm) 'cw)
                            (fargn sterm 2)
                          (fargn sterm 3))
                        '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))))
            (and (not (eq targs :fail))
                 (not (eq sargs :fail))
                 (= (length uargs) (length sargs))
                 (= (length targs) (length sargs))
                 (let ((string-arg ; overkill to call directed-untranslate-rec
                        (du-untranslate (if (eq (car uterm) 'cw)
                                            (fargn sterm 1)
                                          (fargn sterm 2))
                                        nil wrld))
                       (rest-args
                        (directed-untranslate-lst
                         uargs targs sargs
                         (make-list (length uargs) :initial-element iff-flg)
                         lflg exec-p wrld)))
                   (cond ((eq (car uterm) 'cw)
                          `(cw ,string-arg ,@rest-args))
                         (t
                          `(er ,(if (eq (ffn-symb sterm) 'illegal)
                                    'hard
                                  'hard?)
                               ,(du-untranslate (fargn sterm 1) nil wrld)
                               ,string-arg
                               ,@rest-args))))))))
    ((and (lambda-applicationp tterm)
          (not (lambda-applicationp sterm))
          lflg)
     (let ((new-sterm (lambdafy tterm sterm exec-p wrld)))
       (assert$
        new-sterm ; lambdafy should do something in this case
        (directed-untranslate-rec uterm tterm new-sterm iff-flg
                                  nil ; lflg transitions from t to nil
                                  exec-p wrld))))
    (t
     (let ((sterm? (adjust-sterm-for-tterm tterm sterm)))
       (cond
        (sterm?
         (directed-untranslate-rec uterm tterm sterm? iff-flg lflg exec-p wrld))
        (t
         (mv-let (uterm1 tterm1)
           (directed-untranslate-drop-conjuncts uterm tterm sterm)
           (cond
            (tterm1 (directed-untranslate-rec uterm1 tterm1 sterm iff-flg lflg
                                              exec-p wrld))
            (t
             (mv-let (uterm1 tterm1)
               (directed-untranslate-drop-disjuncts uterm tterm sterm iff-flg
                                                    wrld)
               (cond
                (tterm1 (directed-untranslate-rec uterm1 tterm1 sterm iff-flg lflg
                                                  exec-p wrld))

;;; (TODO) Warning: The following comment is probably fine, but there is a
;;; small chance that it is obsolete.  Consider re-reading it carefully.
; At one time, we replaced sterm by (if (not tst) fbr tbr) when tterm is (if
; (not &) & &) and sterm is (if tst tbr fbr) where tst is not a call of NOT.
; However, that seems to be covered now by the case in adjust-sterm-for-tterm
; where we swap the true and false branches of sterm when one of those is the
; false or true branch (resp.) of tterm.

                ((eq (car uterm) 'cond)

; Deal here specially with the case that uterm is a COND.

                 (let ((clauses (directed-untranslate-into-cond-clauses
                                 (cdr uterm) tterm sterm iff-flg lflg exec-p wrld)))
                   (case-match clauses
                     ((('t x))
                      x)
                     (& (cons 'cond clauses)))))

; The next case applies when uterm represents a disjunction or conjunction.

                ((and (eq (ffn-symb sterm) 'if) ; optimization
                      (case-match sterm ; following similar handling in untranslate1

; We could also require more; for example, in the OR case, (eq (ffn-symb tterm)
; 'if) and (equal (fargn tterm 1) (fargn tterm 2)).  But any such requirements
; are probably always true, and even if not, we are happy to try to recover an
; OR or AND directly from sterm as follows.

                        (('if & *nil* *t*) ; generate a NOT, not an AND or OR
                         nil)
                        (('if x1 x2 *nil*)
                         (and (eq (car uterm) 'and)
                              (cond
                               ((cddr uterm) ; tterm is (if x1' x2' nil)
                                (untranslate-and
                                 (directed-untranslate-rec (cadr uterm)
                                                           (fargn tterm 1)
                                                           x1 t lflg exec-p wrld)
                                 (directed-untranslate-rec (if (cdddr uterm)
                                                               (cons 'and
                                                                     (cddr uterm))
                                                             (caddr uterm))
                                                           (fargn tterm 2)
                                                           x2 iff-flg lflg
                                                           exec-p wrld)
                                 iff-flg))
                               ((cdr uterm) ; uterm is (and x)
                                (directed-untranslate-rec (cadr uterm)
                                                          tterm sterm t lflg
                                                          exec-p wrld))
                               (t ; uterm is (and)
                                (directed-untranslate-rec t tterm sterm t lflg
                                                          exec-p wrld)))))
                        (('if x1 *nil* x2)
                         (and (eq (car uterm) 'and) ; tterm is (if x1' x3' *nil*)
                              (directed-untranslate-rec uterm
                                                        tterm
                                                        (fcons-term* 'if
                                                                     (dumb-negate-lit x1)
                                                                     x2
                                                                     *nil*)
                                                        iff-flg lflg exec-p wrld)))
                        (('if x1 x1-alt x2)
                         (and (eq (car uterm) 'or) ; tterm is (if x1' & x2')
                              (cond
                               ((and (or (equal x1-alt x1)
                                         (and iff-flg
                                              (equal x1-alt *t*)))
                                     (cddr uterm)) ; tterm is (if x1' & x2')
                                (untranslate-or
                                 (directed-untranslate-rec (cadr uterm)
                                                           (fargn tterm 1)
                                                           x1 t lflg exec-p wrld)
                                 (directed-untranslate-rec (cons 'or
                                                                 (cddr uterm))
                                                           (fargn tterm 3)
                                                           x2 iff-flg lflg
                                                           exec-p wrld)))
                               ((cddr uterm) ; uterm is (or x y ...)
                                (directed-untranslate-rec (or-macro (cdr uterm))
                                                          tterm sterm iff-flg lflg
                                                          exec-p wrld))
                               ((cdr uterm) ; uterm is (or x)
                                (directed-untranslate-rec (cadr uterm)
                                                          tterm sterm iff-flg lflg
                                                          exec-p wrld))
                               (t ; uterm is (or)
                                (directed-untranslate-rec t tterm sterm iff-flg lflg
                                                          exec-p wrld)))))
                        (('if x1 x2 *t*)
                         (and (eq (car uterm) 'or)
                              (directed-untranslate-rec uterm
                                                        tterm
                                                        (fcons-term* 'if
                                                                     (dumb-negate-lit x1)
                                                                     *t*
                                                                     x2)
                                                        iff-flg lflg exec-p wrld)))
                        (& nil))))
                ((and (eq (car uterm) '>)  ; (> x0 y0)
                      (ffn-symb-p sterm '<)  ; (< y1 x1)
                      (ffn-symb-p tterm '<)) ; (< y2 y1)

; Replace < in sterm by >.

                 (list '>
                       (directed-untranslate-rec
                        (cadr uterm)
                        (fargn tterm 2) (fargn sterm 2) nil lflg exec-p wrld)
                       (directed-untranslate-rec
                        (caddr uterm)
                        (fargn tterm 1) (fargn sterm 1) nil lflg exec-p wrld)))
                ((eq (car uterm) '<=) ; (<= x0 y0), translates as (not (< y1 x1))

; If uterm, tterm, and sterm all represent a <= call, then call <= in the
; result.

                 (or (case-match tterm
                       (('not ('< y1 x1)) ; should always match
                        (case-match sterm
                          (('not ('< y2 x2))
                           (cons '<= (directed-untranslate-lst
                                      (cdr uterm)  ; (x0 y0)
                                      (list x1 y1) ; from tterm
                                      (list x2 y2) ; from sterm
                                      nil lflg exec-p wrld)))
                          (& nil)))
                       (& nil))
                     (du-untranslate sterm iff-flg wrld)))
                ((eq (car uterm) '>=) ; (>= x0 y0), translates as (not (< x1 y1))

; If uterm, tterm, and sterm all represent a >= call, then call >= in the
; result.

                 (or (case-match tterm
                       (('not ('< x1 y1))
                        (case-match sterm
                          (('not ('< x2 y2))
                           (cons '>= (directed-untranslate-lst
                                      (cdr uterm)  ; (x0 y0)
                                      (list x1 y1) ; from tterm
                                      (list x2 y2) ; from sterm
                                      nil lflg exec-p wrld)))
                          (& nil)))
                       (& nil))
                     (du-untranslate sterm iff-flg wrld)))
                (t
                 (or

; Attempt to do something nice with cases where uterm is a call of list or
; list*.

                  (case-match uterm
                    (('mv . x)
                     (let ((list-version
                            (directed-untranslate-rec
                             (cons 'list x)
                             tterm sterm iff-flg lflg exec-p wrld)))
                       (cond ((eq (car list-version) 'list)
                              (cons 'mv (cdr list-version)))
                             (t list-version))))
                    (('list x) ; tterm is (cons x' nil)
                     (case-match sterm
                       (('cons a *nil*)
                        (list 'list
                              (directed-untranslate-rec x (fargn tterm 1) a nil
                                                        lflg exec-p wrld)))
                       (& nil)))
                    (('list x . y) ; same translation as for (cons x (list . y))
                     (case-match sterm
                       (('cons a b)
                        (let ((tmp1 (directed-untranslate-rec x
                                                              (fargn tterm 1)
                                                              a nil lflg exec-p
                                                              wrld))
                              (tmp2 (directed-untranslate-rec `(list ,@y)
                                                              (fargn tterm 2)
                                                              b nil lflg exec-p
                                                              wrld)))
                          (if (and (consp tmp2) (eq (car tmp2) 'list))
                              `(list ,tmp1 ,@(cdr tmp2))
                            `(cons ,tmp1 ,tmp2))))
                       (& nil)))
                    (('list* x) ; same transation as for x
                     (list 'list*
                           (directed-untranslate-rec x tterm sterm nil lflg
                                                     exec-p wrld)))
                    (('list* x . y) ; same translation as for (cons x (list* . y))
                     (case-match sterm
                       (('cons a b)
                        (let ((tmp1 (directed-untranslate-rec x
                                                              (fargn tterm 1)
                                                              a nil lflg exec-p
                                                              wrld))
                              (tmp2 (directed-untranslate-rec `(list* ,@y)
                                                              (fargn tterm 2)
                                                              b nil lflg exec-p
                                                              wrld)))
                          (if (and (consp tmp2) (eq (car tmp2) 'list*))
                              `(list* ,tmp1 ,@(cdr tmp2))
                            `(list* ,tmp1 ,tmp2))))
                       (& nil)))
                    (& nil))

; Attempt to preserve macros like cadr.

                  (and (member-eq (ffn-symb tterm) '(car cdr))
                       (directed-untranslate-car-cdr-nest uterm tterm sterm lflg
                                                          exec-p wrld))

; Final cases:

                  (and (eql (length (fargs sterm))
                            (length (fargs tterm)))
                       (let* ((pair (cdr (assoc-eq (ffn-symb sterm)
                                                   (untrans-table wrld))))
                              (op ; the fn-symb of sterm, or a corresponding macro
                               (if pair
                                   (car pair)
                                 (or (cdr (assoc-eq (ffn-symb sterm)
                                                    (table-alist
                                                     'std::define-macro-fns
                                                     wrld)))
                                     (ffn-symb sterm)))))
                         (cond
                          ((symbolp (ffn-symb sterm))
                           (cond ((and (cdr pair) ; hence pair, and we might right-associate
                                       (case-match uterm
                                         ((!op & & & . &) t) ; we want to flatten
                                         (& nil))) ; (op x (op y ...))

; Uterm is (op & & & . &) where op is a macro with &rest args corresponding to
; the function symbol of sterm.  Untranslate to a suitably flattened op call.

                                  (let ((arg1 (directed-untranslate-rec
                                               (cadr uterm)
                                               (fargn tterm 1) (fargn sterm 1)
                                               nil lflg exec-p wrld))
                                        (arg2 (directed-untranslate-rec
                                               (cons op (cddr uterm))
                                               (fargn tterm 2) (fargn sterm 2)
                                               nil lflg exec-p wrld)))
                                    (cond ((and (consp arg2)
                                                (equal (car arg2) op))
                                           (list* op arg1 (cdr arg2)))
                                          (t (list op arg1 arg2)))))
                                 ((or (equal (car uterm) op)
                                      (equal (car uterm) (ffn-symb tterm))
                                      (equal (macro-abbrev-p op wrld) (ffn-symb tterm)))

; If op is a suitable function (or macro) call for the result, then apply it to
; the result of recursively untranslating (directedly) the args.

                                  (cons op (directed-untranslate-lst
                                            (cdr uterm) (fargs tterm) (fargs sterm)
                                            (case (ffn-symb sterm)
                                              (if (list t iff-flg iff-flg))
                                              (not '(t))
                                              (otherwise nil))
                                            lflg exec-p wrld)))
                                 ((equal sterm tterm)

; It's probably better to use the macro at hand than to untranslate.

                                  uterm)
                                 (t nil)))
                          (t nil))))
                  (du-untranslate sterm iff-flg wrld)))))))))))))))

(defun directed-untranslate-return-last (uterm tterm sterm iff-flg lflg exec-p
                                               wrld)

; This is just code for handling the case of directed-untranslate-rec, that
; sterm is a call of return-last directed-untranslate-rec.  Initially we give
; special treatment only to cases corresponding to prog2$ and mbe.  Other cases
; may be added later.

; This function returns nil for cases not yet handled.

  (declare (xargs :guard ; a partial guard to record some input assumptions
                  (and (nvariablep tterm)
                       (not (fquotep tterm)))))
  (cond
   ((not (and (eq (ffn-symb sterm) 'return-last)
              (true-listp uterm) ; impossible?
              (ffn-symb-p tterm 'return-last)
              (equal (fargn tterm 1)
                     (fargn sterm 1))))
    nil)
   ((and (eq (car uterm) 'prog2$)
         (equal (fargn sterm 1) ''progn))
    (list 'prog2$
          (directed-untranslate-rec (cadr uterm)
                                    (fargn tterm 2)
                                    (fargn sterm 2)
                                    nil lflg exec-p wrld)
          (directed-untranslate-rec (caddr uterm)
                                    (fargn tterm 3)
                                    (fargn sterm 3)
                                    iff-flg lflg exec-p wrld)))
   ((and (eq (car uterm) 'mbe)
         (equal (fargn sterm 1) ''mbe1-raw))
    (list 'mbe
          :logic
          (directed-untranslate-rec (cadr (assoc-keyword :logic (cdr uterm)))
                                    (fargn tterm 3)
                                    (fargn sterm 3)
                                    iff-flg lflg nil wrld)
          :exec
          (directed-untranslate-rec (cadr (assoc-keyword :exec (cdr uterm)))
                                    (fargn tterm 2)
                                    (fargn sterm 2)
                                    iff-flg lflg exec-p wrld)))

; Other cases for return-last can be added here.

   (t nil)))

(defun directed-untranslate-b* (uterm tterm sterm iff-flg lflg exec-p wrld)

; Warning: If you change this, consider changing the case for let* in
; directed-untranslate-rec.

; This is just code for handling b* that was originally in
; directed-untranslate-rec, but has been moved into this separate function, for
; clarity.  This function may return nil.

; Note: It's technically wrong to untranslate to b*, since someone may have
; defined b* differently from how it's defined in std/util/bstar.lisp.  But we
; view directed-untranslate as essentially heuristic, so we can live with that
; technical "unsoundness" that, in fact, is very likely ever to be relevant.

  (case-match uterm
    (('b* bindings form1 form2 . rest)
     (let ((x (directed-untranslate-b*
               (list 'b* bindings (list* 'progn$ form1 form2 rest))
               tterm sterm iff-flg lflg exec-p wrld)))
       (case-match x
         (('b* bindings (progn$-or-prog2$ . forms))
          (if (member-eq progn$-or-prog2$ '(prog2$ progn$))
              `(b* ,bindings ,@forms)
            x))
         (& x))))
    (('b* () rest)
     (directed-untranslate-rec
      rest tterm sterm iff-flg lflg exec-p wrld))
    (('b* ((('if tst) . vals) . bindings) . rest)
     (let ((x (directed-untranslate-rec
               `(b* (((when ,tst) ,@vals) ,@bindings) ,@rest)
               tterm sterm iff-flg lflg exec-p wrld)))
       (case-match x
         (('b* ((('when tst2) . vals2) . bindings2) . rest2)
          `(b* (((if ,tst2) ,@vals2) ,@bindings2) ,@rest2))
         (& x))))
    (('b* ((('when u-tst) . vals) . bindings) rest)
; Keep this in sync with the 'unless case.
     (case-match tterm
       (('if t-tst t-tbr t-fbr) ; should always match
        (case-match sterm
          (('if s-tst s-tbr s-fbr)
           (let* ((r-tst ; "r-" for "result-"
                   (directed-untranslate-rec
                    u-tst t-tst s-tst t lflg exec-p wrld))
                  (u-tbr (if vals
                             `(progn$ ,@vals)
                           u-tst))
                  (r-tbr
                   (directed-untranslate-rec
                    u-tbr t-tbr s-tbr iff-flg lflg exec-p wrld))
                  (r-fbr
                   (directed-untranslate-rec
                    `(b* ,bindings ,rest)
                    t-fbr s-fbr iff-flg lflg exec-p wrld))
                  (new-binding `((when ,r-tst)
                                 ,@(cond
                                    ((and (null vals)
                                          (equal r-tst r-tbr))
                                     nil)
                                    ((eq (car r-tbr) 'progn$)
                                     (cdr r-tbr))
                                    (t (list r-tbr))))))
             (case-match r-fbr
               (('b* bindings2 . rest2)
                `(b* (,new-binding
                      ,@bindings2)
                   ,@rest2))
               (& `(b* (,new-binding)
                     ,r-fbr)))))
          (& ; test presumably simplified to true or false; don't know which
           (du-untranslate sterm iff-flg wrld))))
       (& ; probably an impossible case
        (du-untranslate sterm iff-flg wrld))))
    (('b* ((('unless u-tst) . vals) . bindings) rest)
; Keep this in sync with the 'when case.
     (case-match tterm
       (('if t-tst t-tbr t-fbr) ; should always match
        (case-match sterm
          (('if s-tst s-tbr s-fbr)
           (let* ((r-tst ; "r-" for "result-"
                   (directed-untranslate-rec
                    u-tst t-tst s-tst t lflg exec-p wrld))
                  (u-fbr `(progn$ ,@vals))
                  (r-tbr
                   (directed-untranslate-rec
                    `(b* ,bindings ,rest)
                    t-tbr s-tbr iff-flg lflg exec-p wrld))
                  (r-fbr
                   (directed-untranslate-rec
                    u-fbr t-fbr s-fbr iff-flg lflg exec-p wrld))
                  (new-binding `((unless ,r-tst)
                                 ,@(cond
                                    ((null vals)
                                     nil)
                                    ((and (consp r-fbr)
                                          (eq (car r-fbr) 'progn$))
                                     (cdr r-fbr))
                                    (t (list r-fbr))))))
             (case-match r-tbr
               (('b* bindings2 . rest2)
                `(b* (,new-binding
                      ,@bindings2)
                   ,@rest2))
               (& `(b* (,new-binding)
                     ,r-tbr)))))
          (& ; test presumably simplified to true or false; don't know which
           (du-untranslate sterm iff-flg wrld))))
       (& ; probably an impossible case
        (du-untranslate sterm iff-flg wrld))))
    (('b* ((('mv . args) val) . bindings) rest)
     (and (symbol-listp args) ; otherwise, future work...
          (mv-let (vars binders ignores ignorables freshvars)

; The following call is a bit dodgy, since it takes advantage of the
; implementation of b*, which presumably could change.

            (var-ignore-list-for-patbind-mv args 0 nil nil nil nil nil)
            (declare (ignore binders freshvars))
            (let ((x (directed-untranslate-rec
                      `(mv-let ,vars
                         ,val
                         ,@(and ignores
                                `((declare (ignore ,@ignores))))
                         ,@(and ignorables
                                `((declare (ignorable ,@ignorables))))
                         (b* ,bindings ,rest))
                      tterm sterm iff-flg lflg exec-p wrld)))
              (or (case-match x
                    (('mv-let !vars val2 . last)
                     (and last
                          (let ((body (car (last last))))
                            (mv-let
                              (erp tbody)
                              (translate-cmp body
                                             nil ; stobjs-out
                                             nil ; logic-modep (don't care)
                                             t   ; known-stobjs
                                             'directed-untranslate-b* ; ctx
                                             wrld
                                             (default-state-vars nil))
                              (and (null erp)
                                   (not (intersectp-eq ignores
                                                       (all-vars tbody)))

; Originally we had
; (b* (((mv . args) val) ..) ...)
; and after calling directed-untranslate-rec, we have
; (b* (((mv . vars) val2) ..) ...)
; where vars results from replacing variables in args, for example, ?!v with v
; and - with ignore-3.  In this case we want to use the original args, provided
; the ignored variables don't occur free in the body of the resulting mv-let.

                                   (mv-let (bindings2 body2)
                                     (case-match body
                                       (('b* bindings2 . rest2) ; ignore declares
                                        (mv bindings2 (car (last rest2))))
                                       (& (mv nil body)))
                                     `(b* (((mv ,@args) ,val2)
                                           ,@bindings2)
                                        ,body2))))))))
                  x)))))
    (('b* ((var val) . bindings) rest)
     (cond
      ((eq var '-)
       (case-match tterm
         (('return-last '(quote progn) val2 rest2)
          (case-match sterm
            (('return-last '(quote progn) val3 rest3)
             (let ((val4 (directed-untranslate-rec
                          val val2 val3 nil lflg exec-p wrld))
                   (rest4 (directed-untranslate-rec
                           (list 'b* bindings rest)
                           rest2 rest3 iff-flg lflg exec-p wrld)))
               (case-match rest4
                 (('b* bindings5 rest5)
                  `(b* ((- ,val4) ,@bindings5) ,rest5))
                 (& `(b* ((- ,val4)) ,rest4)))))
            (& ; prog2$ was probably just blown away
             (directed-untranslate-rec
              (list 'b* bindings rest)
              rest2 sterm iff-flg lflg exec-p wrld))))
         (& (er hard 'directed-untranslate-b*
                "Implementation error: unexpected translation of ~x0:~|~x1."
                uterm tterm))))
      ((eq var '&)

; The binding of var (i.e., of &) is thrown away at translate time, so as with
; LET, we don't want to keep an unsimplified val -- we just throw the binding
; away.

       (directed-untranslate-rec
        (list 'b* bindings rest)
        tterm sterm iff-flg lflg exec-p wrld))
      ((symbolp var)
       (mv-let (sym ignorep)
         (decode-varname-for-patbind var)
         (if (eq ignorep 'ignore)
             (directed-untranslate-rec
              `(b* ,bindings ,rest) tterm sterm iff-flg lflg exec-p wrld)
           (let* ((uterm0
                   ;; Can we just refuse to bind a variable marked ignored?
                   `(let ((,sym ,val))
                      ,@(and ignorep `((declare (,ignorep ,sym))))
                      (b* ,bindings ,rest)))
                  (x (directed-untranslate-rec
                      uterm0 tterm sterm iff-flg lflg exec-p wrld)))
             (or (case-match x
                   (('let ((!sym val2)) . last)
                    (and last
                         (let ((body (car (last last)))) ; ignore declares
                           (mv-let (bindings2 body2)
                             (case-match body
                               (('b* bindings2 . rest2) ; ignore declares
                                (mv bindings2 (car (last rest2))))
                               (& (mv nil body)))
                             `(b* ((,var ,val2) ,@bindings2)
                                ,body2))))))
                 x)))))
      (t ; Binders besides mv are not yet handled.
       nil)))
    (& nil)))

(defun directed-untranslate-lst (uargs targs sargs iff-flg-lst lflg exec-p
                                       wrld)
  (cond ((endp sargs) nil)
        ((or (endp uargs) (endp targs))
         (untranslate-lst sargs nil wrld))
        (t (cons (directed-untranslate-rec (car uargs)
                                           (car targs)
                                           (car sargs)
                                           (car iff-flg-lst)
                                           lflg exec-p wrld)
                 (directed-untranslate-lst (cdr uargs)
                                           (cdr targs)
                                           (cdr sargs)
                                           (cdr iff-flg-lst)
                                           lflg exec-p wrld)))))

(defun directed-untranslate-into-cond-clauses (cond-clauses tterm sterm iff-flg
                                                            lflg exec-p wrld)

; This is based on ACL2 source function untranslate-into-cond-clauses.  It
; returns new cond-clauses C (with luck, similar in structure to the input
; cond-clauses) such that (cond . C) translates to sterm.  See
; directed-untranslate.

  (cond
   ((not (and (nvariablep sterm)
;             (not (fquotep sterm))
              (eq (ffn-symb sterm) 'if)

; We expect the following always to be true, because tterm gave rise to
; cond-clauses; but we check, to be sure.

              (nvariablep tterm)
;             (not (fquotep tterm))
              (eq (ffn-symb tterm) 'if)))
    (list (list t
                (du-untranslate sterm iff-flg wrld))))
   ((endp (cdr cond-clauses))
    (cond
     ((eq (caar cond-clauses) t)
      (directed-untranslate-rec (cadar cond-clauses)
                                tterm sterm iff-flg lflg exec-p wrld))
     ((equal (fargn sterm 3) *nil*)
      (list (list (directed-untranslate-rec (caar cond-clauses)
                                            (fargn tterm 1)
                                            (fargn sterm 1)
                                            t lflg exec-p wrld)
                  (directed-untranslate-rec (cadar cond-clauses)
                                            (fargn tterm 2)
                                            (fargn sterm 2)
                                            iff-flg lflg exec-p wrld))))
     (t (list (list t
                    (du-untranslate sterm iff-flg wrld))))))
   ((and (endp (cddr cond-clauses))
         (eq (car (cadr cond-clauses)) t))

; Consider the following call.

;   (directed-untranslate-into-cond-clauses
;    '(((<= len j) yyy)
;      (t xxx))
;    '(if (not (< j len)) yyy xxx)
;    '(if (< j len) xxx yyy)
;    nil nil
;    (w state))

; If we don't give special consideration to this (endp (cddr cond-clauses))
; case, then the result will be as follows, which doesn't respect the structure
; of the given COND clauses.

;   (((< J LEN) XXX)
;    (T YYY))

; So instead, we transform the given COND clause into an IF call, and let our
; usual IF processing do the work for us.

    (let* ((cl1 (car cond-clauses))
           (tst (car cl1))
           (tbr (cadr cl1))
           (cl2 (cadr cond-clauses))
           (fbr (cadr cl2))
           (ans (directed-untranslate-rec `(if ,tst ,tbr ,fbr)
                                          tterm sterm iff-flg lflg exec-p wrld)))
      (case-match ans
        (('if x y z)
         `((,x ,y) (t ,z)))
        (t `(,t ,ans)))))
   (t
    (cons (list (directed-untranslate-rec (caar cond-clauses)
                                          (fargn tterm 1)
                                          (fargn sterm 1)
                                          t lflg exec-p wrld)
                (directed-untranslate-rec (cadar cond-clauses)
                                          (fargn tterm 2)
                                          (fargn sterm 2)
                                          iff-flg lflg exec-p wrld))
          (directed-untranslate-into-cond-clauses
           (cdr cond-clauses)
           (fargn tterm 3)
           (fargn sterm 3)
           iff-flg lflg exec-p wrld)))))

(defun directed-untranslate-car-cdr-nest (uterm tterm sterm lflg exec-p wrld)

; Tterm is a call of car or cdr.  Uterm may be a call of a name in
; *ca<d^n>r-alist*, such as CADDR.  We return nil or else a suitable result for
; (directed-untranslate-rec uterm tterm sterm ...).

  (and (eq (ffn-symb tterm) (ffn-symb sterm))
       (let ((triple (assoc-eq (car uterm) *car-cdr-macro-alist*)))
         (and triple
              (let* ((op1 (cadr triple))
                     (op2 (caddr triple)))
                (and (eq op1 (ffn-symb tterm))
                     (let ((x (directed-untranslate-rec
                               (list op2 (cadr uterm))
                               (fargn tterm 1)
                               (fargn sterm 1)
                               nil lflg exec-p wrld)))
                       (and (consp x)
                            (eq (car x) op2)
                            (list (car uterm) (cadr x))))))))))
)

(defun set-ignore-ok-world (val wrld)

; We return a world in which let-bound variables can be ignored, by extending
; the world with an updated acl2-defaults-table if necessary.

  (let* ((acl2-defaults-table (table-alist 'acl2-defaults-table wrld))
         (old-val (cdr (assoc-eq :ignore-ok acl2-defaults-table))))
    (cond
     ((eq old-val val) wrld)
     (t (putprop 'acl2-defaults-table
                 'table-alist
                 (acons :ignore-ok
                        val
                        acl2-defaults-table)
                 wrld)))))

(defun directed-untranslate (uterm tterm sterm iff-flg stobjs-out wrld)

; Uterm is an untranslated form that we expect to translate to the term, tterm
; (otherwise we just untranslate sterm).  Sterm is a term, which may largely
; agree with tterm.  The result is an untranslated form whose translation is
; provably equal to sterm, with the goal that the sharing of structure between
; tterm and sterm is reflected in similar sharing between uterm and that
; result.

; If stobjs-out is non-nil, then we attempt to make the resulting term have
; that as its stobjs-out.

; Warning: check-du-inv-fn, called in directed-untranslate-rec, requires that
; uterm translates to tterm.  We ensure with set-ignore-ok-world below that
; such failures are not merely due to ignored formals.

  (let* ((wrld (set-ignore-ok-world t wrld))
         (exec-p (and stobjs-out t))
         (sterm (if exec-p
                    (make-executable sterm stobjs-out wrld)
                  sterm)))
    (if (check-du-inv-fn uterm tterm wrld)
        (directed-untranslate-rec uterm tterm sterm iff-flg t exec-p wrld)
      (untranslate sterm iff-flg wrld))))

(defun directed-untranslate-no-lets (uterm tterm sterm iff-flg stobjs-out wrld)

; See directed-untranslate.  Here we refuse to introduce lambdas into sterm.

  (let* ((wrld (set-ignore-ok-world t wrld))
         (exec-p (and stobjs-out t))
         (sterm (if exec-p
                    (make-executable sterm stobjs-out wrld)
                  sterm)))
    (if (check-du-inv-fn uterm tterm wrld)
        (directed-untranslate-rec uterm tterm sterm iff-flg nil exec-p wrld)
      (untranslate sterm iff-flg wrld))))

; Essay on Handling of Lambda Applications by Directed-untranslate

; This essay assumes basic familiarity with the functionality of
; directed-untranslate.  Here we explain how the algorithm deals with lambda
; applications, including LET and LET* untranslated sterm inputs.

; It may be helpful to skip to the examples in directed-untranslate-tests.lisp,
; before reading the text that is immediately below.

; In order to handle the case that tterm is a lambda application but sterm is
; not, directed-untranslate calls an auxiliary routine, lambdafy, to replace
; sterm by an equivalent lambda application.  Lambdafy, in turn, calls
; weak-one-way-unify to create suitable bindings that can be used to abstract
; sterm to a lambda application that matches tterm.  Unlike one-way-unify, the
; returned substitution need not provide a perfect match, but is intended to
; provide bindings so that the abstracted sterm "matches" tterm in a heuristic
; sense.

; A flag in directed-untranslate, lflg, says whether or not it is legal to
; invoke lambdafy.  Lflg is initially t, but after lambdafy has been run, we
; try directed-untranslate again with lflg = nil.

; Note: We focus on the case that sterm has no lambda applications, because
; that is the case in our intended application.  But the algorithm should be
; correct regardless, and may sometimes work decently when sterm does have
; lambda applications.

; See directed-untranslate-tests.lisp.
