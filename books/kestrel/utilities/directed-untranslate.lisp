; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; TODO:

; - Handle more built-in macros, such as mv-let and case.

; - Handle b*.  A possible strategy is to use macroexpand1* to translate away
;   all b* calls, then try to reconstruct b* from the result and the given
;   uterm.

; - Perhaps improve lambdafy-rec to deal with dropped conjuncts and disjuncts;
;   see adjust-sterm-for-tterm.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc directed-untranslate
  :parents (kestrel-utilities system-utilities)
  :short "Create a user-level form that reflects a given user-level form's
 structure."
  :long "<p>See @(see term) for relevant background about user-level ``terms''
 and actual ``translated'' terms.</p>

 @({
 Example Form:
 (directed-untranslate
  '(and a (if b c nil))         ; uterm
  '(if a (if b c 'nil) 'nil)    ; tterm
  '(if a2 (if b2 c2 'nil) 'nil) ; sterm, a form to be untranslated
  nil
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
 always produce the result you want.</li>

 <li>Thus, @('directed-untranslate') may be improved over time; hence its
 untranslation of a given term may change over time as the tool uses
 increasingly sophisticated heuristics.</li>

 <li>The heuristics may work best in the case that sterm is a simplification of
 tterm.</li>

 <li>The heuristics are also optimized for an intended use case in which
 @('sterm') has no @(tsee lambda) applications.  An attempt is made to insert
 suitable @('LET') and/or @('LET*') bindings into the result.  The utility
 @('directed-untranslate-no-lets') is similar but does not make such an
 attempt.</li>

 <li>Here are some features that are not yet implemented but might be in the
 future.

 <ul>

 <li>A better untranslation might be obtainable when the simplified
 term (@('sterm')) has similar structure to a proper subterm of the original
 term @('tterm').  As it stands now, the original untranslated term @('uterm')
 is probably useless in that case.</li>

 <li>Macros including @(tsee mv-let), @(tsee b*), @(tsee case), and quite
 possibly others could probably be reasonably handled, but aren't yet.</li>

 </ul></li>

 </ol>

 <p>End of Remarks.</p>

 @({
 General Form:
 (directed-untranslate uterm tterm sterm iff-flg wrld)
 })

 <p>where:</p>

 <ul>

 <li>@('uterm') is an untranslated form that translates to the term,
 @('tterm');</li>

 <li>@('sterm') is a term, which might share a lot of structure with
 @('tterm') (intuitively, we may think of @('sterm') as a simplified version
 of @('tterm'));</li>

 <li>@('iff-flg') is a Boolean; and</li>

 <li>@('wrld') is a logical @('world'), typically @('(w state)').</li>

 </ul>

 <p>The returned form is an untranslated form whose translation is provably
 equal to @('sterm'), except that if @('iff-flg') is true then these need only
 be Boolean equivalent rather than equal.  The goal is that the shared
 structure between @('tterm') and @('sterm') is reflected in similar sharing
 between @('uterm') and the returned form.</p>")

(program)

(defun check-du-inv-fn (uterm tterm wrld)
  (mv-let (erp val)
    (translate-cmp uterm t nil t 'check-du-inv-fn wrld
                   (default-state-vars nil))
    (and (not erp)
         (equal val tterm))))

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
     (cond ((equal tterm-1 (fargn sterm 1))
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
; 'nil).  Sterm is of the form (if a b *nil*).  If sterm is the translation for
; some k of (and xk . rest), even if subsequent conjuncts differ, then return
; (mv uterm' tterm'), where uterm' and tterm' represent (and xk ... xn).  (xk
; ... xn) and the corresponding subterm of tterm; else return (mv nil nil).
; Note: return (mv nil nil if there is an immediate match.

  (directed-untranslate-drop-conjuncts-rec uterm tterm sterm t))

(defconst *boolean-primitives*

; These are function symbols from (strip-cars *primitive-formals-and-guards*)
; that always return a Boolean.

  '(acl2-numberp bad-atom<= < characterp complex-rationalp consp equal integerp
                 rationalp stringp symbolp))

(defun boolean-fnp (fn wrld)
  (if (member-eq fn *boolean-primitives*)
      t
    (let ((tp (cert-data-tp-from-runic-type-prescription fn wrld)))
      (and tp
           (null (access type-prescription tp :vars))
           (assert$ (null (access type-prescription tp :hyps))
                    (ts-subsetp
                     (access type-prescription tp :basic-ts)
                     *ts-boolean*))))))

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
       (cond ((equal tterm-1 (fargn sterm 1))
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

            (mv var (extend-gen-alist1 sterm var alist)))
           (t (mv (if (dumb-occur (car old) sterm)
                      (subst-expr var (car old) sterm)
                    nil)
                  alist))))))

(defun adjust-sterm-for-tterm (tterm sterm)

; This function can return a term logically equivalent to sterm that is a
; closer syntactic match to tterm.  (But it doesn't introduce lambdas into
; sterm; for that, see lambdafy-rec.)  Otherwise, it returns nil.

; Since (unlike directed-untranslate-rec) we don't have uterm as an input, we
; can't call directed-untranslate-drop-disjuncts or
; directed-untranslate-drop-conjuncts here.  We might consider adding such
; functionality here on behalf of the present function's call froman
; weak-one-way-unify.  But then maybe a flag should say whether we're calling
; this function on behalf of weak-one-way-unify, where we want to do such
; drops, or directed-untranslate, where we don't want the present function to
; do that (since directed-untranslate already invokes
; directed-untranslate-drop-disjuncts and directed-untranslate-drop-conjuncts).

  (mv-let
    (flg sterm)
    (case-match tterm
      (('if ('not (not-consp &)) & &)
       (cond
        ((member-eq not-consp '(endp atom))
         (case-match sterm
           (('if ('consp y) stbr sfbr)
            (mv t (fcons-term* 'if
                               (fcons-term* 'not (fcons-term* not-consp y))
                               stbr
                               sfbr)))
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
      (('return-last ''mbe1-raw *t* &) ; ('mbt &)
       (cond ((not (ffn-symb-p sterm 'return-last))
              (mv t (fcons-term* 'return-last
                                 ''mbe1-raw
                                 *t*
                                 sterm)))
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

; (Note that almost every example (i.e., call of local-test) in the "EXAMPLES"
; section near the end of this file will fail if we redefine lambdafy-restore
; to return (mv (make-lambda new-formals body) nil), thus leaving new-formals
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
        ((dumb-occur (car actuals) term)
         (mv-let (f1 a1)
           (lambda-subst (cdr formals) (cdr actuals) term)
           (cond ((eq f1 :fail)
                  (mv :fail nil))
                 (t (mv (cons (car formals) f1)
                        (cons (car actuals) a1))))))
        (t (mv :fail nil))))

(defun some-var-dumb-occur (lst1 term)
  (cond ((null lst1) nil)
        ((dumb-occur-var (car lst1) term) t)
        (t (some-var-dumb-occur (cdr lst1) term))))

(mutual-recursion

(defun weak-one-way-unify (tterm sterm new-formals old-formals)

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
      (weak-one-way-unify-rec tterm sterm alist)
      (let ((sterm (or sterm? sterm)))
        (mv sterm
            (bind-?-final alist (all-vars sterm) old-formals))))))

(defun weak-one-way-unify-rec (tterm sterm alist)

; This function is just as described in weak-one-way-unify, with two
; exceptions.  First, the present function makes no attempt to add pairs using
; bind-?-final (as in weak-one-way-unify).  Second, the first value returned is
; nil if sterm has not changed.

; Invariant: Every variable free in tterm should be bound in (a cdr of) alist.

  (cond
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
                 (lambdafy-rec tterm sterm)))
           (sterm (or lambdafied-sterm
                      (adjust-sterm-for-tterm tterm sterm)
                      sterm)))
      (mv-let
        (new-args new-alist)
        (weak-one-way-unify-lst (fargs tterm) (fargs sterm) alist)
        (let ((new-sterm?
               (and (or lambdafied-sterm new-args)
                    (fcons-term (ffn-symb sterm)
                                (or new-args
                                    (fargs sterm))))))
          (mv new-sterm? new-alist)))))))

(defun weak-one-way-unify-lst (tterm-lst sterm-lst alist)
  (cond ((equal (length tterm-lst)
                (length sterm-lst))
         (weak-one-way-unify-lst-rec tterm-lst sterm-lst alist))
        (t (mv nil alist))))

(defun weak-one-way-unify-lst-rec (tterm-lst sterm-lst alist)
  (cond ((endp sterm-lst) (mv nil alist))
        (t (mv-let (new-sterm alist)
             (weak-one-way-unify-rec (car tterm-lst)
                                     (car sterm-lst)
                                     alist)
             (mv-let (new-sterm-lst alist)
               (weak-one-way-unify-lst-rec (cdr tterm-lst)
                                           (cdr sterm-lst)
                                           alist)
               (mv (cond (new-sterm
                          (cons new-sterm
                                (or new-sterm-lst
                                    (cdr sterm-lst))))
                         (new-sterm-lst
                          (cons (car sterm-lst)
                                new-sterm-lst))
                         (t nil))
                   alist))))))

(defun lambdafy-rec (tterm sterm)

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
                          (lambdafy-rec body gen-sterm))
                         (extra-vars ; to create a proper lambda application
                          (set-difference-eq (all-vars lambdafied-sterm)
                                             formals)))
                    `((lambda ,(append? formals extra-vars)
                        ,lambdafied-sterm)
                      ,@(append? actuals extra-vars)))))))
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
                                  old-tformals)

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
                              (append? new-args new-extra-vars)))))))))))

(defun lambdafy (tterm sterm)
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
;     x (fix-true-listp lst))
;   '(member-equal x lst))

; Without the call of remove-guard-holders just below, the result is as
; follows.

;   ((LAMBDA (X L LST) (MEMBER-EQUAL X LST))
;    X L LST)

; Thus, we are making it easier to get a nice result from callers of lambdafy,
; in particular, directed-untranslate-rec.

         (remove-guard-holders tterm)))
    (lambdafy-rec tterm sterm)))
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

(defun du-untranslate (term iff-flg wrld)

; This version of untranslate removes empty let bindings.  At one time during
; development of directed-untranslate it made a difference to do so; even if
; that's no longer necessary, it seems harmless to redress that grievance in
; case this ever comes up.

  (let ((ans (untranslate term iff-flg wrld)))
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

(mutual-recursion

(defun directed-untranslate-rec (uterm tterm sterm iff-flg lflg wrld)

; Tterm is the translation of uterm (as may be checked by check-du-inv).  We
; return a form whose translation, with respect to iff-flg, is provably equal
; to sterm.  There may be many such untranslations, but we attempt to return
; one that is similar in structure to uterm.  See also directed-untranslate.

; When lflg is true, we allow ourselves to modify sterm to match the lambda
; applictions in tterm.

  (check-du-inv
   uterm tterm wrld
   (cond

; The following case is sound, and very reasonable.  However, we anticipate
; applying this function in cases where uterm is not a nice untranslation.
; This may change in the future.

;   ((equal tterm sterm)
;    uterm)

    ((or (variablep sterm)
         (fquotep sterm)
         (variablep tterm)
         (fquotep tterm)
         (atom uterm))
     (du-untranslate sterm iff-flg wrld))
    ((and (ffn-symb-p tterm 'return-last)
          (equal (fargn tterm 1) ''progn)
          (case-match uterm
            (('prog2$ & uterm2)
             (directed-untranslate-rec
              uterm2 (fargn tterm 3) sterm iff-flg lflg wrld)))))
    ((and (consp uterm) (eq (car uterm) 'let*))
     (case-match uterm
       (('let* () . &)
        (directed-untranslate-rec
         (car (last uterm))
         tterm sterm iff-flg lflg wrld))
       (('let* ((& &)) . &)
        (let ((x (directed-untranslate-rec
                  (cons 'let (cdr uterm))
                  tterm sterm iff-flg lflg wrld)))
          (case-match x
            (('let ((& &)) . &)
             (cons 'let* (cdr x)))
            (& x))))
       (('let* ((var val) . bindings) . rest)
        (let ((x (directed-untranslate-rec
                  `(let ((,var ,val))
                     (let* ,bindings ,@rest))
                  tterm sterm iff-flg lflg wrld)))
          (case-match x
            (('let ((var2 val2))
               ('let* bindings2 . rest2))
             `(let* ((,var2 ,val2) ,@bindings2)
                ,@rest2))
            (& x))))
       (& ; impossible
        (er hard 'directed-untranslate-rec
            "Implementation error: unexpected uterm, ~x0."
            uterm))))
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
                       (tbody (lambda-body (ffn-symb tterm)))
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
                              uactuals tactuals sactuals nil lflg wrld))
                       (body (directed-untranslate-rec
                              ubody tbody sbody iff-flg lflg wrld))
                       (bindings (collect-non-trivial-bindings sformals-main
                                                               args)))
                  (if bindings
                      (make-let-smart bindings body (all-vars-for-real sbody))
                    body)))))
        (du-untranslate sterm iff-flg wrld))))
    ((and (lambda-applicationp tterm)
          (not (lambda-applicationp sterm))
          lflg)
     (let ((new-sterm (lambdafy tterm sterm)))
       (assert$
        new-sterm ; lambdafy should do something in this case
        (directed-untranslate-rec uterm tterm new-sterm iff-flg
                                  nil ; lflg transitions from t to nil
                                  wrld))))
    (t
     (let ((sterm? (adjust-sterm-for-tterm tterm sterm)))
       (cond
        (sterm?
         (directed-untranslate-rec uterm tterm sterm? iff-flg lflg wrld))
        (t
         (mv-let (uterm1 tterm1)
           (directed-untranslate-drop-conjuncts uterm tterm sterm)
           (cond
            (tterm1 (directed-untranslate-rec uterm1 tterm1 sterm iff-flg lflg
                                              wrld))
            (t
             (mv-let (uterm1 tterm1)
               (directed-untranslate-drop-disjuncts uterm tterm sterm iff-flg wrld)
               (cond
                (tterm1 (directed-untranslate-rec uterm1 tterm1 sterm iff-flg lflg
                                                  wrld))
                (t
                 (or

; At one time, we replaced sterm by (if (not tst) fbr tbr when tterm is (if
; (not &) & &) and sterm is (if tst tbr fbr) where tst is not a call of NOT.
; However, that seems to be covered now by the case in adjust-sterm-for-tterm
; where we swap the true and false branches of sterm when one of those is the
; false or true branch (resp.) of tterm.

                  (cond
                   ((eq (car uterm) 'cond)

; Deal here specially with the case that uterm is a COND.

                    (let ((clauses (directed-untranslate-into-cond-clauses
                                    (cdr uterm) tterm sterm iff-flg lflg wrld)))
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
                                                              x1 t lflg wrld)
                                    (directed-untranslate-rec (if (cdddr uterm)
                                                                  (cons 'and
                                                                        (cddr uterm))
                                                                (caddr uterm))
                                                              (fargn tterm 2)
                                                              x2 iff-flg lflg wrld)
                                    iff-flg))
                                  ((cdr uterm) ; uterm is (and x)
                                   (directed-untranslate-rec (cadr uterm)
                                                             tterm sterm t lflg
                                                             wrld))
                                  (t ; uterm is (and)
                                   (directed-untranslate-rec t tterm sterm t lflg
                                                             wrld)))))
                           (('if x1 *nil* x2)
                            (and (eq (car uterm) 'and) ; tterm is (if x1' x3' *nil*)
                                 (directed-untranslate-rec uterm
                                                           tterm
                                                           (fcons-term* 'if
                                                                        (dumb-negate-lit x1)
                                                                        x2
                                                                        *nil*)
                                                           iff-flg lflg wrld)))
                           (('if x1 x1-alt x2)
                            (and (eq (car uterm) 'or) ; tterm is (if x1' & x2')
                                 (or (equal x1-alt x1)
                                     (equal x1-alt *t*))
                                 (cond
                                  ((cddr uterm) ; tterm is (if x1' & x2')
                                   (untranslate-or
                                    (directed-untranslate-rec (cadr uterm)
                                                              (fargn tterm 1)
                                                              x1 t lflg wrld)
                                    (directed-untranslate-rec (cons 'or
                                                                    (cddr uterm))
                                                              (fargn tterm 3)
                                                              x2 iff-flg lflg
                                                              wrld)))
                                  ((cdr uterm) ; uterm is (or x)
                                   (directed-untranslate-rec (cadr uterm)
                                                             tterm sterm t lflg
                                                             wrld))
                                  (t ; uterm is (or)
                                   (directed-untranslate-rec t tterm sterm t lflg
                                                             wrld)))))
                           (('if x1 x2 *t*)
                            (and (eq (car uterm) 'or)
                                 (directed-untranslate-rec uterm
                                                           tterm
                                                           (fcons-term* 'if
                                                                        (dumb-negate-lit x1)
                                                                        *t*
                                                                        x2)
                                                           iff-flg lflg wrld)))
                           (& nil))))
                   ((and (eq (car uterm) '>)  ; (> x0 y0)
                         (eq (car sterm) '<)  ; (< y1 x1)
                         (eq (car tterm) '<)) ; (< y2 y1)

; Replace < in sterm by >.

                    (list '>
                          (directed-untranslate-rec
                           (cadr uterm)
                           (fargn tterm 2) (fargn sterm 2) nil lflg wrld)
                          (directed-untranslate-rec
                           (caddr uterm)
                           (fargn tterm 1) (fargn sterm 1) nil lflg wrld)))
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
                                         nil lflg wrld)))
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
                                         nil lflg wrld)))
                             (& nil)))
                          (& nil))
                        (du-untranslate sterm iff-flg wrld)))
                   (t
                    (or

; Attempt to do something nice with cases where uterm is a call of list or
; list*.

                     (case-match uterm
                       (('list) uterm)
                       (('list x) ; tterm is (cons x' nil)
                        (case-match sterm
                          (('cons a *nil*)
                           (list 'list
                                 (directed-untranslate-rec x (fargn tterm 1) a nil
                                                           lflg wrld)))
                          (& nil)))
                       (('list x . y) ; same translation as for (cons x (list . y))
                        (case-match sterm
                          (('cons a b)
                           (let ((tmp1 (directed-untranslate-rec x
                                                                 (fargn tterm 1)
                                                                 a nil lflg wrld))
                                 (tmp2 (directed-untranslate-rec `(list ,@y)
                                                                 (fargn tterm 2)
                                                                 b nil lflg wrld)))
                             (if (and (consp tmp2) (eq (car tmp2) 'list))
                                 `(list ,tmp1 ,@(cdr tmp2))
                               `(cons ,tmp1 ,tmp2))))
                          (& nil)))
                       (('list* x) ; same transation as for x
                        (list 'list*
                              (directed-untranslate-rec x tterm sterm nil lflg
                                                        wrld)))
                       (('list* x . y) ; same translation as for (cons x (list* . y))
                        (case-match sterm
                          (('cons a b)
                           (let ((tmp1 (directed-untranslate-rec x
                                                                 (fargn tterm 1)
                                                                 a nil lflg wrld))
                                 (tmp2 (directed-untranslate-rec `(list* ,@y)
                                                                 (fargn tterm 2)
                                                                 b nil lflg wrld)))
                             (if (and (consp tmp2) (eq (car tmp2) 'list*))
                                 `(list* ,tmp1 ,@(cdr tmp2))
                               `(cons ,tmp1 ,tmp2))))
                          (& nil)))
                       (& nil))

; Attempt to preserve macros like cadr.

                     (and (member-eq (ffn-symb tterm) '(car cdr))
                          (directed-untranslate-car-cdr-nest uterm tterm sterm lflg
                                                             wrld))

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
                                                  nil lflg wrld))
                                           (arg2 (directed-untranslate-rec
                                                  (cons op (cddr uterm))
                                                  (fargn tterm 2) (fargn sterm 2)
                                                  nil lflg wrld)))
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
                                               lflg wrld)))
                                    ((equal sterm tterm)

; It's probably better to use the macro at hand than to untranslate.

                                     uterm)
                                    (t nil)))
                             (t nil))))
                     (du-untranslate sterm iff-flg wrld))))))))))))))))))

(defun directed-untranslate-lst (uargs targs sargs iff-flg-lst lflg wrld)
  (cond ((endp sargs) nil)
        ((or (endp uargs) (endp targs))
         (untranslate-lst sargs nil wrld))
        (t (cons (directed-untranslate-rec (car uargs)
                                           (car targs)
                                           (car sargs)
                                           (car iff-flg-lst)
                                           lflg wrld)
                 (directed-untranslate-lst (cdr uargs)
                                           (cdr targs)
                                           (cdr sargs)
                                           (cdr iff-flg-lst)
                                           lflg wrld)))))

(defun directed-untranslate-into-cond-clauses (cond-clauses tterm sterm iff-flg
                                                            lflg wrld)

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
                                tterm sterm iff-flg lflg wrld))
     ((equal (fargn sterm 3) *nil*)
      (list (list (directed-untranslate-rec (caar cond-clauses)
                                            (fargn tterm 1)
                                            (fargn sterm 1)
                                            t lflg wrld)
                  (directed-untranslate-rec (cadar cond-clauses)
                                            (fargn tterm 2)
                                            (fargn sterm 2)
                                            iff-flg lflg wrld))))
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
                                          tterm sterm iff-flg lflg wrld)))
      (case-match ans
        (('if x y z)
         `((,x ,y) (t ,z)))
        (t `(,t ,ans)))))
   (t
    (cons (list (directed-untranslate-rec (caar cond-clauses)
                                          (fargn tterm 1)
                                          (fargn sterm 1)
                                          t lflg wrld)
                (directed-untranslate-rec (cadar cond-clauses)
                                          (fargn tterm 2)
                                          (fargn sterm 2)
                                          iff-flg lflg wrld))
          (directed-untranslate-into-cond-clauses
           (cdr cond-clauses)
           (fargn tterm 3)
           (fargn sterm 3)
           iff-flg lflg wrld)))))

(defun directed-untranslate-car-cdr-nest (uterm tterm sterm lflg wrld)

; Tterm is a call of car or cdr.  Uterm may be a call of a name in
; *ca<d^n>r-alist*, such as CADDR.  We return nil or else a suitable result for
; (directed-untranslate uterm tterm sterm wrld).

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
                               nil lflg wrld)))
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

(defun directed-untranslate (uterm tterm sterm iff-flg wrld)

; Uterm is an untranslated form that we expect to translate to the term, tterm
; (otherwise we just untranslate sterm).  Sterm is a term, which may largely
; agree with tterm.  The result is an untranslated form whose translation is
; provably equal to sterm, with the goal that the sharing of structure between
; tterm and sterm is reflected in similar sharing between uterm and that
; result.

; Warning: check-du-inv-fn, called in directed-untranslate-rec, requires that
; uterm translates to tterm.  We ensure with set-ignore-ok-world below that
; such failures are not merely due to ignored formals.

  (let ((wrld (set-ignore-ok-world t wrld)))
    (if (check-du-inv-fn uterm tterm wrld)
        (directed-untranslate-rec uterm tterm sterm iff-flg t wrld)
      (untranslate sterm iff-flg wrld))))

(defun directed-untranslate-no-lets (uterm tterm sterm iff-flg wrld)

; See directed-untranslate.  Here we refuse to introduce lambdas into sterm.

  (let ((wrld (set-ignore-ok-world t wrld)))
    (if (check-du-inv-fn uterm tterm wrld)
        (directed-untranslate-rec uterm tterm sterm iff-flg nil wrld)
      (untranslate sterm iff-flg wrld))))

; Essay on Handling of Lambda Applications by Directed-untranslate

; This essay assumes basic familiarity with the functionality of
; directed-untranslate.  Here we explain how the algorithm deals with lambda
; applications, including LET and LET* untranslated sterm inputs.

; It may be helpful to skip down to the examples that are further below, before
; reading the text that is immediately below.

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

; Examples below includes annotated traces with DU for directed-untranslate, LF
; for lambdafy, and WO for weak-one-way-unify.  Note that all of these examples
; were developed to help guide code development; thus, all traces shown were
; created by hand.  Moreover, while the comments (including by-hand traces)
; below are perhaps useful, they have generally not been kept up-to-date.  If
; one of them looks wrong, consider tracing the relevant functions and perhaps
; fixing the corresponding trace below.

; ------------------------------
; EXAMPLES.
; ------------------------------

(logic)
(local (include-book "misc/assert" :dir :system))
(defmacro local-test (&rest args)
  `(local (encapsulate () (local (progn ,@args)))))

; ------------------------------

; Example 1:

(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (assert! ; check lambdafy
  (equal (let ((tterm '((LAMBDA (X Y) (< Y (FOO X)))
                        (CONS A (CONS B 'NIL))
                        Y))
               (sterm '(< Y (BAR (CONS A (CONS B 'NIL))))))
           (lambdafy tterm sterm))
         '((LAMBDA (X Y) (< Y (BAR X)))
           (CONS A (CONS B 'NIL))
           Y)))
 (assert! ; check directed-untranslate
  (equal (let ((uterm '(let ((x (cons a (list b))))
                         (> (foo x) y)))
               (tterm '((LAMBDA (X Y) (< Y (FOO X)))
                        (CONS A (CONS B 'NIL))
                        Y))
               (sterm '(< Y (BAR (CONS A (CONS B 'NIL)))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET ((X (CONS A (LIST B))))
               (> (BAR X) Y)))))

; Below we show a motivating hand trace.  Before adding support for
; lambda applications, the call above of directed-untranslate
; returned the simple untranslation of sterm, (< Y (BAR (LIST A B)))

; 0> DU
; uterm: (let ((x (cons a (list b))))
;          (> (foo x) y))
; tterm: ((LAMBDA (X Y) (< Y (FOO X)))
;         (CONS A (CONS B 'NIL))
;         Y)
; sterm: (< Y (BAR (CONS A (CONS B 'NIL))))
; lflg: t

; 1> LF
; uterm: (let ((x (cons a (list b))))
;          (> (foo x) y))
; tterm: ((LAMBDA (X Y) (< Y (FOO X)))
;         (CONS A (CONS B 'NIL))
;         Y)
; sterm: (< Y (BAR (CONS A (CONS B 'NIL))))

; 2> WO
; tterm: (< Y (FOO X))
; sterm: (< Y (BAR (CONS A (CONS B 'NIL))))
; vars:  (x y)

; <2 WO
; ((x . (CONS A (CONS B 'NIL)))
;  (y . y))

; <1 LF
; ((LAMBDA (X Y) (< Y (BAR X)))
;  (CONS A (CONS B 'NIL))
;  Y)

; 1> DU
; uterm: (let ((x (cons a (list b))))
;          (> (foo x) y))
; tterm: ((LAMBDA (X Y) (< Y (FOO X)))
;         (CONS A (CONS B 'NIL))
;         Y)
; sterm: ((LAMBDA (X Y) (< Y (BAR X)))
;         (CONS A (CONS B 'NIL))
;         Y)
; lflg: nil

; 2> DU [lambda body]
; uterm: (> (foo x) y)
; tterm: (< Y (FOO X))
; sterm: (< Y (BAR X))
; lflg: nil

; <2 DU
; (> (BAR X) Y)

; 2> DU [lambda actuals]
; uterm: (cons a (list b))
; tterm: (CONS A (CONS B 'NIL))
; sterm: (CONS A (CONS B 'NIL))
; lflg: nil

; <2 DU
; (CONS A (LIST B))

; <1 DU [flg=nil]
; (LET ((X (CONS A (LIST B))))
;      (> (BAR X) Y))

; <0 DU [flg=t]
; (LET ((X (CONS A (LIST B))))
;      (> (BAR X) Y))

; ------------------------------

; Example 2:

; Next let's try nested let and let* expressions.

(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (defun g (x) (car x))
 (defun h (x) (car x))
 (defthm g-is-h
   (equal (foo x) (bar x)))
 (in-theory (disable g h))
 (assert!
  (equal (let ((tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (CONS A (CONS B 'NIL))
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (BAR (CONS A (CONS B 'NIL))))))
           (lambdafy tterm sterm))
         '((LAMBDA (X D C)
                   ((LAMBDA (Y X) (< Y (BAR X)))
                    (H (CONS C (CONS D 'NIL)))
                    X))
           (CONS A (CONS B 'NIL))
           D C)))
 (assert!
  (equal (let ((uterm '(let ((x (cons a (list b))))
                         (let ((y (g (cons c (list d)))))
                           (> (foo x) y))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (CONS A (CONS B 'NIL))
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (BAR (CONS A (CONS B 'NIL)))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET ((X (CONS A (LIST B))))
               (LET ((Y (H (CONS C (LIST D)))))
                    (> (BAR X) Y))))))

; Note this variant involving let*.

(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (defun g (x) (car x))
 (defun h (x) (car x))
 (defthm g-is-h
   (equal (foo x) (bar x)))
 (in-theory (disable g h))
 (assert!
  (equal (let ((uterm '(let* ((x (cons a (list b)))
                              (y (g (cons c (list d)))))
                         (> (foo x) y)))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (CONS A (CONS B 'NIL))
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (BAR (CONS A (CONS B 'NIL)))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET* ((X (CONS A (LIST B)))
                 (Y (H (CONS C (LIST D)))))
                (> (BAR X) Y)))))

; Before handling lambda applications, directed-untranslate lost > and (cons a
; (list b)), instead returning: (< (H (LIST C D)) (BAR (LIST A B))).

; 0> DU
; uterm: (let ((x (cons a (list b))))
;          (let ((y (g (cons c (list d)))))
;            (> (foo x) y)))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (CONS A (CONS B 'NIL))
;         D C)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))
; lflg: t

; 1> LF
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (CONS A (CONS B 'NIL))
;         D C)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))

; 2> WO
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))
; vars:  (x d c)

; 3> LF
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))

; 4> WO
; tterm: (< Y (FOO X))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))
; vars: (y x)

; <4 WO
; ((y . (H (CONS C (CONS D 'NIL))))
;  (x . (CONS A (CONS B 'NIL))))

; <3 LF
; ((LAMBDA (Y X) (< Y (BAR X)))
;  (H (CONS C (CONS D 'NIL)))
;  (CONS A (CONS B 'NIL)))

; 3> WO [with lambda in sterm]
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X) (< Y (BAR X)))
;         (H (CONS C (CONS D 'NIL)))
;         (CONS A (CONS B 'NIL)))
; vars:  (x d c)

; <3 WO [lflg=nil]
; ((x . (CONS A (CONS B 'NIL)))
;  (d . d)
;  (c . c))

; <2 WO [lflg=t]
; ((x . (CONS A (CONS B 'NIL)))
;  (d . d)
;  (c . c))

; <1 LF
; ((LAMBDA (X D C)
;          ((LAMBDA (Y X) (< Y (BAR X)))
;           (H (CONS C (CONS D 'NIL)))
;           X))
;  (CONS A (CONS B 'NIL))
;  D C)

; 1> DU [lflg=nil]
; uterm: (let ((x (cons a (list b))))
;          (let ((y (g (cons c (list d)))))
;            (> (foo x) y)))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (CONS A (CONS B 'NIL))
;         D C)
; sterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (BAR X)))
;                  (H (CONS C (CONS D 'NIL)))
;                  X))
;         (CONS A (CONS B 'NIL))
;         D C)
; lflg: nil

; 2> DU [lambda body]
; uterm: (let ((y (g (cons c (list d)))))
;          (> (foo x) y))
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X) (< Y (BAR X)))
;         (H (CONS C (CONS D 'NIL)))
;         X)
; lflg: nil

; 3> DU [lambda body]
; uterm: (> (foo x) y)
; tterm: (< Y (FOO X))
; sterm: (< Y (BAR X))
; lflg: nil

; <3 DU
; (> (BAR X) Y)

; 3> DU [lambda actuals]
; uterm: (g (cons c (list d)))
; tterm: (G (CONS C (CONS D 'NIL)))
; sterm: (H (CONS C (CONS D 'NIL)))
; lflg: nil

; <3 DU
; (H (CONS C (LIST D)))

; <2 DU
; (LET ((Y (H (CONS C (LIST D)))))
;      (> (BAR X) Y))

; 2> DU [lambda actuals]
; uterm: (cons a (list b))
; tterm: (CONS A (CONS B 'NIL))
; sterm: (CONS A (CONS B 'NIL))
; lflg: nil

; <2 DU
; (CONS A (LIST B))

; <1 DU [lflg=nil]
; (LET ((X (CONS A (LIST B))))
;      (LET ((Y (H (CONS C (LIST D)))))
;           (> (BAR X) Y)))

; <0 DU [lflg=t]
; (LET ((X (CONS A (LIST B))))
;      (LET ((Y (H (CONS C (LIST D)))))
;           (> (BAR X) Y)))

; ------------------------------

; Example 3:

; This example shows how to handle the case that matching isn't as
; straightforward.  (The example below will make clear what that means.)

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))
 (assert!
  (equal (let ((tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A))))
           (lambdafy tterm sterm))
         '((LAMBDA (X D C)
                   ((LAMBDA (Y X) (< Y (MESS X)))
                    (H (CONS C (CONS D 'NIL)))
                    X))
           A D C)))
 (assert!
  (equal (let ((uterm '(let ((x (dup a)))
                         (let ((y (g (cons c (list d)))))
                           (> (foo x) y))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET ((X A))
               (LET ((Y (H (CONS C (LIST D)))))
                    (> (MESS X) Y))))))

; Note this variant involving let*.

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))
 (assert!
  (equal (let ((uterm '(let* ((x (dup a))
                              (y (g (cons c (list d)))))
                         (> (foo x) y)))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET* ((X A)
                 (Y (H (CONS C (LIST D)))))
                (> (MESS X) Y)))))

; Before directed-untranslate gave special handling for lambda applications,
; the call of directed-untranslate above returned (< (H (LIST C D)) (MESS A)).

; What result would we actually like?  Here are some reasonable choices.

; (a)
; (> (MESS A) (H (CONS C (LIST D))))

; (b)
; (LET ((Y (H (CONS C (LIST D)))))
;      (> (MESS A) Y))

; (c)
; (LET ((X (MESS A)))
;      (LET ((Y (H (CONS C (LIST D)))))
;           (> X Y)))

; Clearly (b) is better than (a).  Each of (b) and (c) has its advantages.  At
; first glance (c) is better, because it preserves the lambda-related structure
; of tterm.  But (c) is perhaps confusing, because x is bound to the
; simplification of (foo (dup a)), rather than (dup a) as in tterm.  A big
; advantage of (c) is that if there were many occurrences of (mess a), and if
; (mess a) were instead a large expression, then (b) could execute very slowly.
; Consider our real goal here: we want lambdafy to set things up so that
; directed-untranslate can produce a nice result.  In (b), (mess a) would be
; compared with (foo x).  In (c), (mess a) would be compared with (dup a).
; There isn't a clear winner as far as I can tell, though perhaps (c) is a bit
; more natural since both involve the variable, a.  So it is tempting go with
; (c) because of its better execution efficiency.

; However, if we look more closely at the original uterm, we see that if (mess
; a) occurs many times in sterm, then (foo x) could easily occur many times in
; uterm.  So we aren't necessarily losing execution efficiency.  See Example 4.

; In short: we always preserve the lambda structure in whatever way seems
; natural algorithmically.  If examples later suggest that this approach needs
; revising, they can provide guidance for how to proceed.

; 0> DU
; uterm: (let ((x (dup a)))
;          (let ((y (g (cons c (list d)))))
;            (> (foo x) y)))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; lflg: t

; 1> LF
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 2> WO
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars:  (x d c)

; 3> LF
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 4> WO
; tterm: (< Y (FOO X))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars: (y x)

; NOTE: Here is where trying to obtain a result of type (c) seems to break
; down.  The natural solution to this (weak-)one-way-unification problem is to
; bind x to a.

; <4 WO
; ((y . (H (CONS C (CONS D 'NIL))))
;  (x . A))

; <3 LF (matching y only, not x)
; ((LAMBDA (Y X) (< Y (MESS X)))
;  (H (CONS C (CONS D 'NIL)))
;  A)

; 3> WO [after lambdafying sterm]
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X) (< Y (MESS X)))
;         (H (CONS C (CONS D 'NIL)))
;         A)
; vars:  (x d c)

; <3 WO [after lambdafying sterm]
; ((x . a)
;  (d . d)
;  (c . c))

; <2 WO
; ((x . a)
;  (d . d)
;  (c . c))

; <1 LF
; ((LAMBDA (X D C)
;          ((LAMBDA (Y X) (< Y (MESS X)))
;           (H (CONS C (CONS D 'NIL)))
;           X))
;  A D C)

; 1> DU [lflg=nil]
; uterm: (let ((x (dup a)))
;          (let ((y (g (cons c (list d)))))
;            (> (foo x) y)))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (MESS X)))
;                  (H (CONS C (CONS D 'NIL)))
;                  X))
;         A D C)
; lflg: nil

; 2> DU [lambda body]
; uterm: (let ((y (g (cons c (list d)))))
;          (> (foo x) y))
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X) (< Y (MESS X)))
;         (H (CONS C (CONS D 'NIL)))
;         X)
; lflg: nil

; 3> DU [lambda body]
; uterm: (> (foo x) y)
; tterm: (< Y (FOO X))
; sterm: (< Y (MESS X))
; lflg: nil

; <3 DU
; (> (MESS X) Y)

; 3> DU [lambda actuals]
; uterm: (g (cons c (list d)))
; tterm: (G (CONS C (CONS D 'NIL)))
; sterm: (H (CONS C (CONS D 'NIL)))
; lflg: nil

; <3 DU
; (H (CONS C (LIST D)))

; <2 DU
; (LET ((Y (H (CONS C (LIST D)))))
;      (> (MESS X) Y))

; 2> DU [lambda actuals]
; uterm: (dup a)
; tterm: (DUP A)
; sterm: A
; lflg: nil

; <2 DU
; A

; <1 DU
; (LET ((X A))
;      (LET ((Y (H (CONS C (LIST D)))))
;           (> (MESS X) Y)))

; I suppose we could consider beta-reducing when the variable only occurs once,
; as above (though that would require some thought).  But it seems to make
; sense to preserve the structure when reasonably possible.

; ------------------------------

; Example 4:

; In Example 3 we discussed a concern about preserving sharing.  This example
; shows how that can work out OK.

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))

 (assert!
  (equal (let ((tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A))))
           (lambdafy tterm sterm))
         '((LAMBDA (X D C)
                   ((LAMBDA (Y X)
                            ((LAMBDA (Z Y) (< Y Z)) (MESS X) Y))
                    (H (CONS C (CONS D 'NIL)))
                    X))
           A D C)))
 (assert!
  (equal (let ((uterm '(let ((x (dup a)))
                         (let ((y (g (cons c (list d)))))
                           (let ((z (foo x)))
                             (> z y)))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET ((X A))
               (LET ((Y (H (CONS C (LIST D)))))
                    (LET ((Z (MESS X)))
                         (> Z Y)))))))

; Note these variants involving let*.

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))

 (assert!
  (equal (let ((uterm '(let* ((x (dup a))
                              (y (g (cons c (list d))))
                              (z (foo x)))
                         (> z y)))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET* ((X A)
                 (Y (H (CONS C (LIST D))))
                 (Z (MESS X)))
                (> Z Y)))))

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))

 (assert!
  (equal (let ((uterm '(let* ((x (dup a))
                              (y (g (cons c (list d)))))
                         (let ((z (foo x)))
                           (> z y))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET* ((X A)
                 (Y (H (CONS C (LIST D)))))
                (LET ((Z (MESS X)))
                     (> Z Y))))))

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))

 (assert!
  (equal (let ((uterm '(let ((x (dup a)))
                         (let* ((y (g (cons c (list d))))
                                (z (foo x)))
                           (> z y))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET ((X A))
               (let* ((Y (H (CONS C (LIST D))))
                      (Z (MESS X)))
                 (> Z Y))))))

; Without attention to lambdas, the result above was formerly
; (< (H (LIST C D)) (MESS A)).

; 0> DU
; uterm: (let ((x (dup a)))
;          (let ((y (g (cons c (list d)))))
;            (let ((z (foo x)))
;              (> z y))))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X)
;                          ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; lflg: t

; 1> LF
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X)
;                          ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 2> WO
; tterm: ((LAMBDA (Y X)
;                 ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars:  (x d c)
; lflg: t

; 3> LF
; tterm: ((LAMBDA (Y X)
;                 ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 4> WO
; tterm: ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars: (y x)

; 5> LF
; tterm: ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 6> WO
; tterm: (< Y Z)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars: (z y)

; <6 WO
; ((y . (H (CONS C (CONS D 'NIL))))
;  (z . (MESS A)))

; <5 LF
; ((LAMBDA (Z Y) (< Y Z))
;  (MESS A)
;  (H (CONS C (CONS D 'NIL))))

; 4> WO [after lambdafy]
; tterm: ((LAMBDA (Z Y) (< Y Z))
;         (FOO X)
;         Y)
; sterm: ((LAMBDA (Z Y) (< Y Z))
;         (MESS A)
;         (H (CONS C (CONS D 'NIL))))
; vars: (y x)

; <4 WO [after lambdafy]
; ((y . (H (CONS C (CONS D 'NIL))))
;  (x . a))

; <3 LF
; ((LAMBDA (Y X)
;          ((LAMBDA (Z Y) (< Y Z))
;           (MESS X)
;           Y))
;  (H (CONS C (CONS D 'NIL)))
;  A)

; 2> WO [after lambdafy]
; tterm: ((LAMBDA (Y X)
;                 ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X)
;                 ((LAMBDA (Z Y) (< Y Z)) (MESS X) Y))
;         (H (CONS C (CONS D 'NIL)))
;         A)
; vars:  (x d c)

; <2 WO
; ((x . a) (d . d) (c . c))

; <1 LF
; ((LAMBDA (X D C)
;          ((LAMBDA (Y X)
;                   ((LAMBDA (Z Y) (< Y Z)) (MESS X) Y))
;           (H (CONS C (CONS D 'NIL)))
;           X))
;  A D C)

; 1> DU [lflg=nil]
; uterm: (let ((x (dup a)))
;          (let ((y (g (cons c (list d)))))
;            (let ((z (foo x)))
;              (> z y))))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X)
;                          ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X)
;                          ((LAMBDA (Z Y) (< Y Z)) (MESS X) Y))
;                  (H (CONS C (CONS D 'NIL)))
;                  X))
;         A D C)
; lflg: nil

; <1 DU
; (let ((x a))
;   (let ((y (h (cons c (list d)))))
;     (let ((z (mess x)))
;       (> z y))))

; <0 DU
; (let ((x a))
;   (let ((y (h (cons c (list d)))))
;     (let ((z (mess x)))
;       (> z y))))

; ------------------------------

; Example 5: In this set of examples we deal with avoiding variable capture.

; Adapted from Example 2:
(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (defun g (x) (car x))
 (defun h (x) (car x))
 (defthm g-is-h
   (equal (foo x) (bar x)))
 (in-theory (disable g h))

 (assert!
  (equal (let ((tterm '((LAMBDA (X A)
                                ((LAMBDA (X A) (< A (FOO X))) (G X) A))
                        (CONS A (CONS B 'NIL))
                        A))
               (sterm '(< A (BAR (H (CONS A (CONS B 'NIL)))))))
           (lambdafy tterm sterm))
         '((LAMBDA (X A)
                   ((LAMBDA (X A) (< A (BAR X)))
                    (H X)
                    A))
           (CONS A (CONS B 'NIL))
           A)))
 (assert!
  (equal (let ((uterm '(let ((x (cons a (list b))))
                         (let ((x (g x)))
                           (> (foo x) a))))
               (tterm '((LAMBDA (X A)
                                ((LAMBDA (X A) (< A (FOO X))) (G X) A))
                        (CONS A (CONS B 'NIL))
                        A))
               (sterm '(< A (BAR (H (CONS A (CONS B 'NIL))))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET ((X (CONS A (LIST B))))
               (LET ((X (H X)))
                    (> (BAR X) A))))))

; Note this variant involving let*.

(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (defun g (x) (car x))
 (defun h (x) (car x))
 (defthm g-is-h
   (equal (foo x) (bar x)))
 (in-theory (disable g h))

 (assert!
  (equal (let ((uterm '(let* ((x (cons a (list b)))
                              (x (g x)))
                         (> (foo x) a)))
               (tterm '((LAMBDA (X A)
                                ((LAMBDA (X A) (< A (FOO X))) (G X) A))
                        (CONS A (CONS B 'NIL))
                        A))
               (sterm '(< A (BAR (H (CONS A (CONS B 'NIL))))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg wrld))
         '(LET* ((X (CONS A (LIST B)))
                 (X (H X)))
                (> (BAR X) A)))))

; Before handling lambdas specially, directed-untranslate returned
; (< A (BAR (H (LIST A B)))).

; 0> DU
; uterm: (let ((x (cons a (list b))))
;          (let ((x (g x)))
;            (> (foo x) a)))
; tterm: ((LAMBDA (X A)
;                 ((LAMBDA (X A) (< A (FOO X))) (G X) A))
;         (CONS A (CONS B 'NIL))
;         A)
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))
; lflg: t

; 1> LF
; tterm: ((LAMBDA (X A)
;                 ((LAMBDA (X A) (< A (FOO X))) (G X) A))
;         (CONS A (CONS B 'NIL))
;         A)
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))

; 2> WO
; tterm: ((LAMBDA (X A) (< A (FOO X))) (G X) A)
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))
; vars:  (x a)

; 3> LF
; tterm: ((LAMBDA (X A) (< A (FOO X))) (G X) A)
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))

; 4> WO
; tterm: (< A (FOO X))
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))
; vars: (x a)

; <4 WO
; ((A . A)
;  (X . (H (CONS A (CONS B 'NIL)))))

; <3 LF
; ((LAMBDA (X A) (< A (BAR X)))
;  (H (CONS A (CONS B 'NIL)))
;  A)

; 3> WO [after lambdafy]
; tterm: ((LAMBDA (X A) (< A (FOO X)))
;         (G X)
;         A)
; sterm: ((LAMBDA (X A) (< A (BAR X)))
;         (H (CONS A (CONS B 'NIL)))
;         A)
; vars:  (x a)

; <3 WO [after lambdafy]
; ((X . (CONS A (CONS B 'NIL)))
;  (A . A))

; <2 WO
; ((X . (CONS A (CONS B 'NIL)))
;  (A . A))

; <1 LF
; ((LAMBDA (X A)
;          ((LAMBDA (X A) (< A (BAR X)))
;           (H X)
;           A))
;  (CONS A (CONS B 'NIL))
;  A)

; 1> DU [lflg=nil]
; uterm: (let ((x (cons a (list b))))
;          (let ((x (g x)))
;            (> (foo x) a)))
; tterm: ((LAMBDA (X A)
;                 ((LAMBDA (X A) (< A (FOO X))) (G X) A))
;         (CONS A (CONS B 'NIL))
;         A)
; sterm: ((LAMBDA (X A)
;                 ((LAMBDA (X A) (< A (BAR X))) (H X) A))
;         (CONS A (CONS B 'NIL))
;         A)
; lflg: nil

; 2> DU [lambda body]
; uterm: (let ((x (g x)))
;          (> (foo x) a))
; tterm: ((LAMBDA (X A) (< A (FOO X))) (G X) A)
; sterm: ((LAMBDA (X A) (< A (BAR X))) (H X) A)
; lflg: nil

; 3> DU [lambda body]
; uterm: (> (foo x) a)
; tterm: (< A (FOO X))
; sterm: (< A (BAR X))
; lflg: nil

; <3 DU
; (> (BAR X) A)

; 3> DU [lambda actuals]
; uterm: (g x)
; tterm: (G X)
; sterm: (H X)
; lflg: nil

; <3 DU
; (H X)

; <2 DU
; (LET ((X (H X)))
;      (> (BAR X) A))

; 2> DU [lambda actuals]
; uterm: (cons a (list b))
; tterm: (CONS A (CONS B 'NIL))
; sterm: (CONS A (CONS B 'NIL))
; lflg: nil

; <2 DU
; (CONS A (LIST B))

; <1 DU [lflg=nil]
; (LET ((X (CONS A (LIST B))))
;      (LET ((X (H X)))
;           (> (BAR X) A)))

; <0 DU [lflg=t]
; (LET ((X (CONS A (LIST B))))
;      (LET ((X (H X)))
;           (> (BAR X) A)))

; ------------------------------

; Validate claims made in the documentation:

(local-test
 (assert!
  (let ((sterm '(if a2 (if b2 c2 'nil) 'nil)))
    (and (equal (directed-untranslate
                 '(and a (if b c nil))     ; uterm
                 '(if a (if b c 'nil) 'nil) ; tterm
                 sterm                      ; sterm, a form to be untranslated
                 nil
                 (w state))
                '(AND A2 (IF B2 C2 NIL)))
         (equal (untranslate sterm nil (w state))
                '(AND A2 B2 C2))))))

; Example: A challenge for avoiding capture.

(local-test

(defconst *uterm0*
  '(let ((y (cons x y))) (cons (cdr y) y)))

(defconst *tterm0*
  '((LAMBDA (Y) (CONS (CDR Y) Y))
    (CONS X Y)))

(defconst *sterm0*
  '(cons y (cons x y)))

; The following shows that uterm and tterm correspond:

(assert!
 (equal (untranslate '((LAMBDA (Y) (CONS (CDR Y) Y))
                       (CONS X Y))
                     nil
                     (w state))
        '(let ((y (cons x y))) (cons (cdr y) y))))

; Notice that uterm and sterm agree, though that's not really important here.

(must-succeed
 (thm (equal (let ((y (cons x y))) (cons (cdr y) y))
             (cons y (cons x y)))))


; Now let's apply directed-untranslate to get a version of *sterm0*, namely
; *sterm0-simp*, that is a LET (since *uterm0* is a LET).

(make-event
 `(defconst *sterm0-simp*
    ',(directed-untranslate *uterm0* *tterm0* *sterm0* nil (w state))))

; In our initial implementation, we had capture!
; Compare with *sterm0*: (CONS Y (CONS X Y))
; Fortunately, that capture no longer happens:

(assert! ; no longer have capture:
 (not (equal *sterm0-simp*
             '(LET ((Y (CONS X Y))) (CONS Y Y)))))

(assert! ; instead we get this:
 (equal *sterm0-simp*
        '(LET ((Y1 (CONS X Y))) (CONS Y Y1))))

; The prover validates this:

(make-event
 `(defthm s0-simp-test
    (equal ,*sterm0* ,*sterm0-simp*)
    :rule-classes nil))

; The real problem was with lambdafy.  Notice that this isn't a problem:

(assert!
 (equal
  (lambdafy '((LAMBDA (Y1) (CONS (CDR Y1) Y1))
              (CONS X Y))
            '(CONS Y (CONS X Y)))
  '((LAMBDA (Y1 Y) (CONS Y Y1))
    (CONS X Y)
    Y)))

; But when the lambda variable is y, there was capture.

(assert!
 (equal
  (lambdafy '((LAMBDA (Y) (CONS (CDR Y) Y))
              (CONS X Y))
            '(CONS Y (CONS X Y)))
; Formerly ((LAMBDA (Y) (CONS Y Y)) (CONS X Y))
  '((LAMBDA (Y1 Y) (CONS Y Y1))
    (CONS X Y)
    Y)))

; Notice that there needn't always be capture even when it looks like that
; might be possible.  Consider the following example, which succeeded even
; before we dealt with the capture problem, because weak-one-way-unify binds y
; to (cons x y) and there is no occurrence of the "outer" (global) y remaining
; after the abstraction.

(assert!
 (let ((tterm '((LAMBDA (Y) (CONS Y Y))
                (CONS X Y)))
       (sterm '(CONS (CONS X Y) (CONS X Y))))
   (equal (lambdafy tterm sterm)
          tterm)))

; But imagine that we alpha-convert tterm in this example, replacing y by y1.
; Then the result would contain y1.  But that's not so bad, as it eliminates some
; potential confusion; for example, the untranslated result would then be
; (LET ((Y1 (CONS X Y))) (CONS Y1 Y1)),
; which makes clear the distinction between the two "Y" variables.

(assert!
 (let ((tterm '((LAMBDA (Y1) (CONS Y1 Y1))
                (CONS X Y)))
       (sterm '(CONS (CONS X Y) (CONS X Y))))
   (equal (lambdafy tterm sterm)
          tterm)))

; So for purposes of lambdafy, we will initially rename top-level lambda
; formals in tterm that occur in sterm.  This may do more renaming than
; necessary, so we fix that; see lambdafy-restore and lambdafy-restore1.

)

; Example: A very thorny problem with capture.

(local-test

(defstub f1 (x1 x2) T)

(defun f2 (x1 x2 x3)
  (declare (ignore x2))
  (append x1 x3))

(defstub f3 (x1) t)

(defun f4 (x1 x2)
  (let* ((x3 (f3 x1))
	 (x4 (f2 x3 x1 x2)))
    (f1 x1 x4)))

; A preliminary attempt to deal with capture led to the following ugly (though
; correct) result.

#|
  (let ((x3 (f3 x1))
        (x2 x4)
        (x5 x2))
    (let* ((x4 (append x3 x5)))
      (f1 x1 x4)))
|#

; Now we get a nicer result.  See a long comment in weak-one-way-unify-rec
; about why an attempt to match and f2 call with a binary-append call fails
; (which leads to the dropping of the outer let* binding).

(assert!
 (equal
  (directed-untranslate '(let* ((x3 (f3 x1))
                                (x4 (f2 x3 x1 x2)))
                           (f1 x1 x4))
                        '((lambda (x3 x2 x1)
                            ((lambda (x4 x1) (f1 x1 x4))
                             (f2 x3 x1 x2)
                             x1))
                          (f3 x1)
                          x2
                          x1)
                        '(f1 x1 (binary-append (f3 x1) x2))
                        nil
                        (w state))
  '(LET* ((X3 (F3 X1))
          (X4 (APPEND X3 X2)))
         (F1 X1 X4))))

; Worse yet, the result could be not only ugly, but confusing.  Consider the
; following variant of f4.

(defun f5 (x y)
  (let* ((z (f3 x))
	 (y (f2 z x y)))
    (f1 x y)))

; We expect (f2 z x y) to simplify to (append z y), and happily, with the
; current version of directed-untranslate, it does:

(assert!
 (equal
  (directed-untranslate '(let* ((z (f3 x))
                                (y (f2 z x y)))
                           (f1 x y))
                        '((lambda (z y x)
                            ((lambda (y x) (f1 x y)) (f2 z x y) x))
                          (f3 x)
                          y
                          x)
                        '(f1 x (binary-append (f3 x) y))
                        nil
                        (w state))
  '(let* ((z (f3 x))
          (y (append z y)))
     (f1 x y))))

; A preliminary attempt to deal with capture produced the following, which is
; quite confusing (though correct) because the second argument to append is
; based on the symbol X rather than, as above, on the symbol Y.

#||
  (let ((z (f3 x))
        (y y1)
        (x1 y))
    (let* ((y (append z x1)))
      (f1 x y)))
||#

)

; The following once produced this bad result for directed-untranslate:
; (LET ((ALL-R R)) (APPEND (F1 C) C))

(local-test
 (defstub f1 (x) t)
 (defun app3 (r c ign)
   (declare (ignore ign))
   (append r c))
 (defun f2 (c)
   (f1 c))
 (defun g (c)
   (let* ((all-r (f2 c))
          (r all-r))
     (app3 r c 17)))
 (assert!
  (equal (directed-untranslate
          '(let* ((all-r (f2 c)) (r all-r))
             (app3 r c 17))
          '((lambda (all-r c)
              ((lambda (r c) (app3 r c '17)) all-r c))
            (f2 c)
            c)
          '(binary-append (f1 c) c)
          nil (w state))
         '(APPEND (F1 C) C))))
