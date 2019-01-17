; DEFINE-SK
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Jared Davis

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STD")
(include-book "std/util/define" :dir :system)
(include-book "acceptable-rewrite-rule-p")
(set-state-ok t)
(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc define-sk
  :parents (std/util defun-sk acl2::kestrel-utilities)
  :short "A very fine alternative to @(tsee defun-sk)."
  :long "<h3>Introduction</h3>

<p>@('define-sk') is an extension of @(see defun-sk) with many @(see
define)-like features and other enhancements:</p>

<ul>

<li>Support for @('define')-style syntax including: extended formals with
embedded guards/docs and @('&key')/@('&optional') arguments via macro aliases,
@(see xdoc) integration and automatic function signatures, @(':prepwork') and
@('///') sections, @(':returns') specifiers, etc.</li>

<li>Better support for @(see guard) verification which avoids theory problems
and provides smarter handling of @('implies') forms; see @(see
define-sk-implies-handling).</li>

<li>It automatically infers when using @(':rewrite :direct') is possible, which
generally gives you a better theorem for universally quantified functions.</li>

</ul>

<h5>Example</h5>

@({
     (define-sk distances-bounded-p ((bound   rationalp \"Maximum length to allow.\")
                                     (cluster setp      \"All nodes to consider.\"))
        :short \"Do all nodes in a cluster lie within some certain bound?\"
        (forall ((weaker   \"Lesser of the two nodes to consider.\")
                 (stronger \"Greater of the two nodes to consider.\"))
           (implies (and (in lesser cluster)
                         (in greater cluster)
                         (weaker-p weaker stronger))
                    (<= (distance lesser greater) bound)))
        ///
        (defthm sensible-when-sensible-bound-p
          (implies (and (distances-bounded-p bound cluster)
                        (sensible-bound-p bound))
                   (sensible-cluster-p cluster))))
})

<h3>Syntax</h3>

@({
     (define-sk name formals
       (quantifier extended-vars body)
       [/// other-events])              ;; optional, starts with the symbol ///
})

<p>Where:</p>

<ul>

<li>The name is just the name of the new quantified function to be defined, as
in @(see defun-sk).</li>

<li>The @('formals') are a list of @(see std::extended-formals).  This could be
as simple as a list of variables, but can also specify guards and documentation
fragments as in @(see define).  The special @('&key')/@('&optional') arguments
are allowed.  No extra keyword arguments are accepted on individual
formals.</li>

<li>The @('quantifier') should be either @('forall') or @('exists').</li>

<li>The @('extended-vars') are a list of @(see std::extended-formals) that are
being quantified over.  Like the @('formals'), these can have documentation
fragments.  Special restrictions: guards are not allowed here and neither are
@('&key')/@('&optional') arguments.  No additional keyword arguments are
accepted for individual extended vars.</li>

<li>The @('body') is as in @(see defun-sk).</li>

<li>The @('other-events') are as in @(see define); this is just a grouping
mechanism that allows you to put related theorems and events here.</li>

</ul>

<p>Additionally, optional @(':keyword value') arguments may be interspersed
anywhere between @('name') and @('///').</p>



<h3>Guard Related Features</h3>

<p>A common problem when trying to use guard verification with @(see
defun-sk) is that @(see implies) isn't lazy, so you won't be able to assume
that your hypotheses hold in your conclusion.  @('define-sk') tries to help
with this by smartly handling @('implies') forms in your function body.  See
@(see define-sk-implies-handling) for a detailed explanation of the
problem.</p>

<h5>Guard Options</h5>

<dl>

<dt>:verify-guards val</dt>

<dd>Like @(see define), we try to verify guards by default, but you can avoid
this by setting @(':verify-guards nil').</dd>

<dt>:guard guard</dt>

<dd>Usually it's most convenient to embed your guards within the @(see
extended-formals), but the @(':guard') option is sometimes useful for giving
additional guards.</dd>

<dt>:guard-hints hints</dt>
<dt>:guard-debug bool</dt>

<dd>These are passed to the guard verification attempt as you would
expect.</dd>

<dt>:implies mode</dt>

<dd>By default we use @(':implies :smart'), which means that uses of
@('implies') are automatically converted into @('if') terms in the body.  To
avoid this, use @(':implies :dumb').</dd>

</dl>


<h3>Other Keyword Options</h3>

<dl>

<dt>:enabled val</dt>

<dd>By default the quantified function <b>and its @('necc/suff') theorem</b>
will both be disabled after the @('///') events are finished.  You can control
this with @(':enabled'):

<ul>
<li>@(':enabled :all') -- enable the function and the theorem</li>
<li>@(':enable :thm') -- disable the function but enable the theorem</li>
<li>@(':enable :fn') -- enable the function but disable the theorem</li>
<li>@(':enable nil') -- disable the function and theorem (default)</li>
</ul></dd>

<dt>:rewrite val</dt>

<dd>This is similar to the same option for @(see defun-sk), except that by
default we look at your function's body to infer whether @(':rewrite :direct')
can be used.  If for whatever reason you don't like the rewrite rule that gets
generated, you can customize it by adding @(':rewrite <custom-term>').</dd>


<dt>:returns spec</dt>

<dd>By default we try to prove that your quantified function returns a @(see
booleanp).  However, note that it is possible to define ``weird'' quantifiers
that return non-boolean or multiple values.  For instance, here is a quantified
function that logically just always returns 0:</dd>

@({
     (set-ignore-ok t)
     (defun-sk weird-quantifier (x) (forall elem 0))
     (thm (equal (weird-quantifier x) 0))
})

<dd>Similarly, here is an quantified function that actually returns multiple
values:</dd>

@({
     (defun-sk weirder-quantifier (x) (forall elem (mv x x)))
     (thm (equal (weirder-quantifier x) (mv x x)))
})

<dd>If you try to introduce such a function with @('define-sk'), or if your
predicate just happens to not return a proper @('t') or @('nil') boolean, then
you may need to provide a custom @(':returns') form; see @(see
returns-specifiers) for details.</dd>


<dt>:strengthen val</dt>

<dd>Submits the underlying @(see defchoose) event with the @('strengthen')
option.</dd>


<dt>:ignore-ok val</dt>

<dd>Submits @('(set-ignore-ok val)') before the definition.  This option is
local to the @('define-sk') and does not affect the @('other-events').</dd>

<dt>:irrelevant-formals-ok val</dt>

<dd>Submits @('(set-irrelevant-formals-ok val)') before the definition.  This
option is local to the @('define-sk') and does not affect the
@('other-events').</dd>

<dt>:parents parents</dt>
<dt>:short string</dt>
<dt>:long string</dt>

<dd>These are @(see defxdoc)-style options for documenting the function.  They
are passed to a @(see defsection) for this definition.</dd>

<dt>:prepwork events</dt>

<dd>These are arbitrary events that you want to put before the definition
itself.  For instance, it might include any local lemmas.</dd>

<dt>:progn val</dt>

<dd>Normally a @('define-sk') expands to an @('(encapsulate nil ...)').  This
means for instance that you can use @(see local) in your @('prepwork'),
@('other-events'), to make changes that are local to the @('define-sk') form.
In certain special cases, you may want to avoid this use of @('encapsulate')
and instead submit the events using @('progn').</dd>

<dt>:verbosep val</dt>

<dd>By default some output is suppressed, but yu can set @(':verbosep t') to
avoid this.  This may be useful when debugging failed @('define-sk')
forms.</dd>

</dl>")

(defxdoc define-sk-implies-handling
  :parents (define-sk)
  :short "Explanation of the @(':implies :smart') option for @(see define-sk)."

  :long "<p>By default, the @(see define-sk) macro does handles calls of
@('implies') in its function's body in a ``smart'' way.  Below we explain what
problem this special handling is meant to help with and the way it works.</p>

<p>Note: you can disable this behavior via @(':implies :dumb').</p>


<h3>Sketch of the problem</h3>

<p>Consider a quantified function definition like:</p>

@({
    (defun-sk all-greaterp (min list)
      (forall (elem)
              (implies (member elem list)
                       (< min elem)))
      :witness-dcls ((declare (xargs :guard (and (integerp min)
                                                 (integer-listp list))
                                     :verify-guards nil))))
})

<p>Unfortunately, the above produces a lousy @('-necc') theorem that isn't
really the rule you usually want:</p>

@({
    (defthm all-greaterp-necc
      (implies (not (implies (member elem list)
                             (< min elem)))
               (not (all-greaterp min list))))
})

<p>We can get a better rule by adding the @(':rewrite :direct') option to the
@(see defun-sk).  After we do that, we get a better rule:</p>

@({
    (defthm all-greaterp-necc
      (implies (all-greaterp min list)
               (implies (member elem list)
                        (< min elem))))
})

<p>So that's great.  The problem comes in when we try to verify the guards of
@('all-greaterp').  For that, we need to know that @('elem') is a number when
we call @('(< min elem)').  This is obviously true since @('elem') is a member
of @('list'), an integer list&mdash;except wait, @(see implies) is a real
function, so when we call @('(< min elem)'), we haven't yet established that
@('elem') is in @('list').</p>

<p>To fix this, we might try to rewrite our function to get rid of the
@('implies').  For instance, we might write:</p>

@({
    (defun-sk all-greaterp (min list)
      (forall (elem)
              (if (member elem list)
                  (< min elem)
                t))
      :rewrite :direct
      :witness-dcls ((declare (xargs :guard (and (integerp min)
                                                 (integer-listp list))
                                     :verify-guards nil))))
})

<p>But now we run into a different problem: the @('-necc') theorem now ends up
looking like this:</p>

@({
    (defthm all-greaterp-necc
      (implies (all-greaterp min list)
               (if (member elem list)
                   (< min elem)
                 t)))
})

<p>But this isn't a valid <see topic='@(url acl2::rewrite)'>rewrite</see> rule
because of the @(see if) in the conclusion!</p>

<p>In short: for guard verification we generally want to use something like
@('if') or <see topic='@(url acl2::impliez)'>impliez</see> instead of
@('implies'), but to get good rewrite rules we need to use @('implies').</p>


<h3>Solution</h3>

<p>To try to help with this, @(see define-sk) does something special with
@('implies') forms inside the body.  In particular, when we submit:</p>

@({
    (define-sk all-greaterp ((min integerp) (list integer-listp))
      (forall (elem)
              (implies (member elem list)
                       (< min elem))))
})

<p>The @('implies') terms in the resulting @(see defun) for @('all-greaterp')
will automatically get expanded into @('if') terms.  That is, the real @(see
defun) that we submit will look something like this:</p>

@({
    (defun all-greaterp (min list)
      (declare ...)
      (let ((elem (all-greaterp-witness min list)))
         (if (member elem list)
             (< min elem)
           t)))
})

<p>This will generally help to make guard verification more straightforward
because you'll be able to assume the hyps hold during the conclusion.  But note
that this rewriting of @('implies') is done only in the function's body, not in
the @('-necc') theorem where it would ruin the <see topic='@(url
acl2::rewrite)'>rewrite</see> rule.</p>

<p>Is this safe?  There's of course no logical difference between @('implies')
and @('impliez'), but there certainly is a big difference in the execution, viz
evaluation order.  Fortunately, this difference will not matter for what we are
trying to do: we're only changing @('implies') to @('if') in code that follows
a call of the @('-witness') function.  This code can never be reached in real
execution, because calling the @('-witness') function will cause an error.  So:
logically we aren't changing anything, and this term is never executed anyway,
so execution differences don't matter.</p>")

; ----- Define-SK Table -------------------------------------------------------
;
; For meta-programming, information about each define-sk form is recorded in a
; define-sk table.  You generally shouldn't access this table directly, but
; instead should use FIND-DEFINE-SK-GUTS (see below).

(defconst *define-sk-keywords*
  ;; The keywords allowed by define-sk forms.
  ;; Note for very advanced users: if you're building macros on top of
  ;; define-sk, you can tell parse-define-sk to allow additional keywords
  ;; beyond those listed here.
  '(:parents
    :short
    :long
    :prepwork
    :progn
    :ignore-ok
    :irrelevant-formals-ok
    :verbosep
    :enabled
    :verify-guards
    :guard-hints
    :guard-debug
    :guard
    :implies
    :returns
    :rewrite
    :strengthen
    :quant-ok
    :skolem-name
    :thm-name
    :classicalp
    :non-executable
    ))

(def-primitive-aggregate define-sk-guts
  ;; A single entry in the Define-SK Table.
  ;; Note: if this doesn't have what you need, it is very easy to extend.
  ;; Just modify parse-define-sk to add the desired extra information.
  (name           ;; user-level name (could be the defun-sk name or a wrapper macro name)
   name-fn        ;; name of the actual defun-sk function (might be name or name-fn)
   raw-formals    ;; not parsed, includes any &optional/&key parts
   formals        ;; parsed formallist-p
   quantifier     ;; forall or exists
   bound-vars     ;; parsed formallist-p
   raw-body       ;; original body term, not macroexpanded or anything
   exec-body      ;; body modified with implies->if (for the function definition)
   main-def       ;; the full defun-sk event for the function
   macro          ;; macro wrapper (if necessary): nil or a defmacro event
   returnspecs    ;; returns specifiers, already parsed; default: (bool booleanp :rule-classes :type-prescription)
   kwd-alist      ;; keyword options passed to define-sk; see *define-sk-keywords*
   rest-events    ;; events in the /// part
   )
  :tag :define-sk-guts)

(table define-sk)
(table define-sk 'guts-alist)

(defun get-define-sk-guts-alist (world)
  (cdr (assoc 'guts-alist (table-alist 'define-sk world))))

(defun extend-define-sk-guts-alist (guts)
  `(table define-sk 'guts-alist
          (cons (cons ',(define-sk-guts->name guts) ',guts)
                (get-define-sk-guts-alist world))))

(define find-define-sk-guts ((name "This may be either the name of a define-sk
                                    function or a macro wrapper for a
                                    define-sk.")
                             world)
  :returns (maybe-guts "A Define-SK guts structure, if the function is found,
                        or NIL if this is not a known Define-SK.")
  (let ((name-fn
         ;; In the case of macro arguments like &key, Define-SK may introduce a
         ;; wrapper macro.  For instance, (define-sk foo (&optional ...) ...)
         ;; will create a macro named FOO and the core defun-sk will be named
         ;; FOO-FN.  To make this as transparent as possible, first resolve FOO
         ;; to FOO-FN if it happens to be a macro.
         (or (cdr (assoc name (table-alist 'define-macro-fns world)))
             name)))
    (cdr (assoc name-fn (get-define-sk-guts-alist world)))))


; ---- Smartly Expanding Implies ----------------------------------------------
;
; We "just" want to expand implies into ifs, but macros mean nothing is easy.
; Our approach won't work for everything, but it should be (1) safe and (2)
; hopefully good enough for most anything we'd encounter in practice.  The
; basic idea:
;
;    1. Translate the original raw body and expand implies within it to get
;       the "target term."
;
;    2. Dumbly expand implies in the raw-body, without understanding the macros
;       at all, to create a user-level, untranslated "candidate term".
;
;    3. Translate the candidate term and then expand implies within its
;       translation to get a "check term."  If the check term happens to be
;       equal to the target term, then it seems like everything is OK.
;
;    4. Else, something tricky is going on and we are too dumb to safely
;       replace implies with IFs.  Handle this in whatever way we decide to
;       handle it.

(mutual-recursion
 (defun expand-implies-in-pseudo-term (x)
   (b* (((when (atom x)) x)
        ((when (eq (car x) 'quote)) x)
        (args (expand-implies-in-pseudo-term-list (cdr x)))
        ((when (eq (car x) 'implies))
         (let ((p (first args))
               (q (second args)))
            (list 'if p (list 'if q ''t ''nil) ''t)))
        ((when (atom (car x)))
         (cons (car x) args))
        ((list lambda formals body) (car x)))
     (cons (list lambda formals (expand-implies-in-pseudo-term body)) args)))
 (defun expand-implies-in-pseudo-term-list (x)
   (if (atom x)
       x
     (cons (expand-implies-in-pseudo-term (car x))
           (expand-implies-in-pseudo-term-list (cdr x))))))

(defun dumb-expand-implies-in-untranslated-term (x)
  ;; Horribly stupid, doesn't understand macros, not to be trusted!
  (cond ((atom x) x)
        ((eq (car x) 'quote) x)
        ((and (eq (car x) 'implies)
              (true-listp x)
              (equal (len x) 3))
         (let ((p (dumb-expand-implies-in-untranslated-term (second x)))
               (q (dumb-expand-implies-in-untranslated-term (third x))))
           (list 'if p (list 'if q t nil) t)))
        (t
         (cons (dumb-expand-implies-in-untranslated-term (car x))
               (dumb-expand-implies-in-untranslated-term (cdr x))))))

(defun expand-implies-for-define-sk (raw-body ctx state)
  "Returns (MV OKP NEW-BODY STATE)"
  (acl2::state-global-let*   ;; hide any potential translation errors
   ((acl2::inhibit-output-lst acl2::*valid-output-names*))
   (b* ((stobjs-out t)
        (logic-modep t)
        (known-stobjs t)
        (wrld (w state))
        ((mv er pre-target-term state)
         (acl2::translate raw-body
                          stobjs-out logic-modep known-stobjs ctx wrld state))
        ((when (or er (not (pseudo-termp pre-target-term))))
         (mv nil raw-body state))
        (target-term (expand-implies-in-pseudo-term pre-target-term))
        (candidate   (dumb-expand-implies-in-untranslated-term raw-body))
        ((mv er candidate-trans state)
         (acl2::translate candidate
                          stobjs-out logic-modep known-stobjs ctx wrld state))
        ((when (or er (not (pseudo-termp candidate-trans))))
         (mv nil raw-body state))
        (check-term (expand-implies-in-pseudo-term candidate-trans))
        ((unless (equal check-term target-term))
         (mv nil raw-body state)))
     (mv t candidate state))))

(encapsulate ()
  (logic)

  ;; Quick sanity check of implies expansion

  (local (defmacro trick (x) (substitute 'and 'implies x)))
  (local (defthm example-of-trick
           (equal (trick (implies x y)) (and x y))
           :rule-classes nil))

  (local (make-event
          (b* ((ctx 'sanity-check)
               ((mv okp trans state)
                (expand-implies-for-define-sk '(let ((x 1)) (implies x y)) ctx state))
               ((unless (and okp
                             (equal trans '(let ((x 1)) (if x (if y t nil) t)))))
                (er soft ctx "Example 1 incorrect: got OKP=~x0, Trans=~x1." okp trans))
               ((mv okp trans state)
                (expand-implies-for-define-sk '(let ((x 1)) (trick x y)) ctx state))
               ((unless (not okp))
                (er soft ctx "Example 2 incorrect: got OKP=~x0, Trans=~x1." okp trans)))
            ;; Done with sanity checks
            (value '(value-triple :success))))))


(defun define-sk-infer-rewrite-mode (body state)
  ;; This should only be invoked for forall quantifiers with :rewrite nil.
  ;; Here's how the ordinary defun-sk handles :rewrite for the forall case:
  ;;
  ;;    :direct          -- use (implies (all-integerp x) body-guts)
  ;;    nil or :default  -- use (implies (not body-guts) (not (all-integerp x)))
  ;;    some custom term -- use the custom term
  ;;
  ;; We will try to be smarter:
  ;;
  ;;    nil              -- use :direct if it would work, :default otherwise
  ;;    :direct          -- use :direct
  ;;    :default         -- use :default
  ;;    some custom term -- use the custom term
  ;;
  ;; BODY is the raw body with no implies tampering.  We just translate it and
  ;; then see whether ACL2 thinks it'd be OK as a rewrite rule.  This isn't
  ;; quite the rewrite rule that we'll submit in the :direct case, because it's
  ;; missing the (all-integerp x) hyp or similar.  But that's fine and doesn't,
  ;; I think, affect whether it's a valid rewrite rule.  It also means that we
  ;; don't have to do anything special to make it so that the quantified
  ;; function is defined.  (This should be fine since quantified functions
  ;; can't recursively call themselves or the witness function.)
  "Returns (MV MODE STATE)"
  (declare (xargs :mode :program :stobjs state))
  (b* ((stobjs-out t)
       (logic-modep t)
       (known-stobjs t)
       ((mv er translated-body state)
        (acl2::state-global-let* ;; hide translation errors
         ((acl2::inhibit-output-lst acl2::*valid-output-names*))
         (acl2::translate body stobjs-out logic-modep known-stobjs 'define-sk (w state) state)))
       ((when er)
        ;; Some translation error -- it seems fine to ignore this and just not
        ;; infer :rewrite :direct.  If there's a problem translating the body
        ;; now, there'll be a problem when we submit the defchoose, and ACL2
        ;; can report about it then.
        (mv :default state))
       ;; Call ACL2's function that checks whether the rule is okay or not.
       (okp
        (acl2::acceptable-rewrite-rule-p translated-body
                                         (acl2::ens state)
                                         (acl2::w state)))
       ((when (not okp))
        ;; It's an error message, so there's some problem, don't use :direct.
        (mv :default state)))
    ;; Otherwise seems OK.
    (mv :direct state)))

(encapsulate ()
  (logic)

  ;; Quick sanity check of rewrite mode inference

  (local (make-event
          (b* (((mv mode1 state) (define-sk-infer-rewrite-mode '(implies (atom x) (equal (car x) nil)) state))
               ((unless (eq mode1 :direct))
                (er soft 'infer-rewrite-mode "sanity check 1 failed"))
               ((mv mode2 state) (define-sk-infer-rewrite-mode `(if x (integerp y) (consp z)) state))
               ((unless (eq mode2

; Matt K. mod, now that rewrite rules are permitted for IF-expressions
; (formerly :default).

                            :direct))
                (er soft 'infer-rewrite-mode "sanity check 2 failed"))
               ((mv mode3 state) (define-sk-infer-rewrite-mode ''t state))
               ((unless (eq mode3 :default))
                (er soft 'infer-rewrite-mode "sanity check 2 failed")))
            (value '(value-triple :success))))))



;; BOZO ugh, this is all so jumbled right now....

(define find-formal-with-non-t-guard (formals)
  (cond ((atom formals)
         nil)
        ((equal (formal->guard (car formals)) t)
         (find-formal-with-non-t-guard (cdr formals)))
        (t
         (car formals))))

(define parse-define-sk ((name "User-level name, e.g., FOO instead of FOO-FN.")
                         (args "Everything that comes after the name.")
                         (extra-keywords "Any additional keywords to allow; possibly
                                          useful for building tools on top of define-sk.")
                         state)
  :returns (mv guts state)
  (b* ((__function__ 'define-sk)
       (world (w state))
       ((unless (symbolp name))
        (mv (raise "Expected function name to be a symbol, found ~x0." name)
            state))
       ((mv main-stuff rest-events) (split-/// name args))
       ((mv kwd-alist non-keyword-stuff)
        (extract-keywords name
                          (append extra-keywords *define-sk-keywords*)
                          main-stuff nil))

       ;; Extract formals, quantifier, bound-vars, and body from the non-keyword-stuff
       ((unless (equal (len non-keyword-stuff) 2))
        (mv (raise "Error in ~x0: define-sk takes exactly two non-keyword ~
                    arguments (the formals and quantifier form), found ~x1."
                   name (len non-keyword-stuff))
            state))
       ((list raw-formals qvb-form) non-keyword-stuff)
       ((unless (and (consp qvb-form)
                     (or (eq (car qvb-form) 'acl2::forall)
                         (eq (car qvb-form) 'acl2::exists))))
        (mv (raise "Error in ~x0: expected (forall ...) or (exists ...) but ~
                    found ~x1" name qvb-form)
            state))
       ((unless (tuplep 3 qvb-form))
        (mv (raise "Error in ~x0: wrong number of arguments to ~x1: ~x2"
                   name (car qvb-form) qvb-form)
            state))
       ((list quantifier raw-bound-vars raw-body) qvb-form)

       ;; Special hack.  ACL2's defun-sk lets you write either, e.g.,
       ;;
       ;;      (forall x ...)    or    (forall (x) ...)
       ;;
       ;; This gets a little messy with extended formals.  We'll support any of:
       ;;
       ;;    (forall x ...)
       ;;    (forall (x "...") ...)
       ;;    (forall ((x "...")) ...)
       ;;
       ;; To do this, we'll explicitly look for the first two cases and convert
       ;; them into lists.
       (raw-bound-vars (cond ((symbolp raw-bound-vars)
                              ;; Single symbol, so listify it.
                              (list raw-bound-vars))
                             ((and (consp raw-bound-vars)
                                   (consp (cdr raw-bound-vars))
                                   (symbolp (first raw-bound-vars))
                                   (stringp (second raw-bound-vars)))
                              ;; (var "blah" ...) -- maybe a valid single extended
                              ;; formal, definitely not any other valid thing.
                              (list raw-bound-vars))
                             (t
                              raw-bound-vars)))

       ;; The formals (but not the bound vars) may have &key/&optional style
       ;; macro arguments.  If so, make a suitable wrapper macro.
       (need-macrop (has-macro-args raw-formals))
       (name-fn     (cond (need-macrop (intern-in-package-of-symbol
                                        (concatenate 'string (symbol-name name) "-FN")
                                        name))
                          (t name)))
       (macro       (and need-macrop
                         (make-wrapper-macro name name-fn raw-formals)))

       ;; The raw-formals and raw-bound-vars are user-level extended formals
       ;; syntax, so parse them into real formals.
       ;;
       ;;   - Note: the bound vars can't have macro arguments and are not
       ;;     allowed to have guards.
       ;;
       ;;   - Note also that define-like :type declarations aren't allowed
       ;;     anywhere, but we don't have do anything special to support this
       ;;     because that's just an extra keyword that define tells
       ;;     parse-formals it can use.
       (formals         (remove-macro-args name raw-formals nil))
       (formals         (parse-formals name formals nil world))
       (formal-names    (formallist->names formals))
       (formal-guards   (remove t (formallist->guards formals)))
       (stobj-names     (formallist->names (formallist-collect-stobjs formals world)))
       (bound-vars      (parse-formals name raw-bound-vars nil world))
       (bound-var-names (formallist->names bound-vars))
       (bad-bound-var (find-formal-with-non-t-guard bound-vars))
       ((when bad-bound-var)
        (mv (raise "Error in ~x0: bound variables can't have guards but ~x1 ~
                    has guard ~x2."
                   name (formal->name bad-bound-var) (formal->guard bad-bound-var))
            state))

       (prepwork (getarg :prepwork nil kwd-alist))
       ((unless (true-listp prepwork))
        (mv (raise "Error in ~x0: expected :prepwork to be a true-listp, but ~
                    found ~x1." name prepwork)
            state))

       (implies-mode (getarg :implies :smart kwd-alist))
       ((unless (member implies-mode '(:smart :dumb)))
        (mv (raise "Error in ~x0: unknown :implies mode ~x1 (expected :smart ~
                    or :dumb)." name implies-mode)
            state))
       (kwd-alist (put-assoc :implies implies-mode kwd-alist))
       ((mv ?okp exec-body state)
        (if (eq implies-mode :smart)
            (expand-implies-for-define-sk raw-body name state)
          (mv t raw-body state)))

       ;; I considered causing an error here.  However, at this point we
       ;; haven't yet sanity checked the body, so if there's anything wrong
       ;; with the body, such as a typo, then we'll error out and tell the user
       ;; that it's a problem expanding implies forms?  That's no good.
       ;; Causing an error might work if we move this down into the event
       ;; generation, e.g., we could definitely do this after we've submitted
       ;; the defchoose event.  Which would also be nice, because then maybe
       ;; parsing define-sk's wouldn't need to modify state...
       ;;
       ;; ((unless okp)
       ;;  (mv (raise "Error in ~x0: failed to expand implies forms.  You can ~
       ;;              avoid this error by adding :implies :dumb, but that may ~
       ;;              make guard verification harder; see :doc define-sk."
       ;;             name)
       ;;      state))

       (enabled (getarg :enabled nil kwd-alist))
       ((unless (member enabled '(nil :fn :thm :all)))
        (mv (raise "Error in ~x0: :enabled must be NIL, :FN, :THM, or :ALL, ~
                    but found ~x1." name enabled)
            state))

       (quant-ok     (getarg :quant-ok nil kwd-alist))

       ;; Skolem Name.  Do this here, instead of letting defun-sk name it,
       ;; because in the case of macros we may give defun-sk the name FOO-FN,
       ;; and it'd be nicer for the witness to be FOO-WITNESS instead of
       ;; FOO-FN-WITNESS.  (Also this lets us update the kwd-alist.)
       (skolem-name  (getarg :skolem-name nil kwd-alist))
       ((unless (symbolp skolem-name))
        (mv (raise "Error in ~x0: :skolem-name must be a symbol; found ~x1." name skolem-name)
            state))
       (skolem-name  (or skolem-name (acl2::add-suffix name "-WITNESS")))
       (kwd-alist    (put-assoc :skolem-name skolem-name kwd-alist))

       ;; Theorem Name.  Do this here, instead of letting defun-sk name it,
       ;; because in the case of macros we may give defun-sk the name FOO-FN,
       ;; and it'd be nicer for the witness to be FOO-WITNESS instead of
       ;; FOO-FN-WITNESS.  (Also this lets us update the kwd-alist.)
       (thm-name     (getarg :thm-name nil kwd-alist))
       ((unless (symbolp thm-name))
        (mv (raise "Error in ~x0: :thm-name must be a symbol;  found ~x1." name thm-name)
            state))
       (thm-name     (or thm-name
                         (acl2::add-suffix name (if (eq quantifier 'acl2::exists) "-SUFF" "-NECC"))))
       (kwd-alist    (put-assoc :thm-name thm-name kwd-alist))


       (parents     (if (assoc :parents kwd-alist)
                        (cdr (assoc :parents kwd-alist))
                      (xdoc::get-default-parents world)))
       (kwd-alist   (put-assoc :parents parents kwd-alist))

       ;; Since we're using defun-sk, tampering with the body is tricky because
       ;; we don't want to tamper with the -necc theorem.  The only time that this
       ;; will matter is if we're using :rewrite :direct, because then replacing
       ;; IMPLIES in the body with IF could screw up the rewrite rule.
       (rewrite     (getarg :rewrite nil kwd-alist))
       ((mv rewrite state)
        (if (and (not rewrite)
                 (not (eq quantifier 'acl2::exists)))
            (define-sk-infer-rewrite-mode raw-body state)
          (mv rewrite state)))
       (rewrite
        (if (and (not (eq quantifier 'acl2::exists))
                 (eq rewrite :direct))
            ;; This is the rule that they would have gotten from the plain
            ;; defun-sk without any implies tampering.  We need to supply it
            ;; ourselves, because if we just let the defun-sk do it, it'll
            ;; use the exec-body.
            `(implies (,name-fn ,@formal-names)
                      ,raw-body)
          ;; Otherwise, whatever they've supplied is fine for now.
          rewrite))

       (strengthen  (getarg :strengthen nil kwd-alist))

       (witness-dcls ;; trying to remove this (getarg :witness-dcls nil kwd-alist))
        nil)
       (guard          (getarg :guard t kwd-alist))

       ;; BOZO.  For now mark the function as non-executable by default if it
       ;; involves any stobjs.  Eventually avoid this by having defun-sk put a
       ;; non-exec around the call of the witness.
       (non-executable (getarg :non-executable (if stobj-names t nil) kwd-alist))
       (kwd-alist      (put-assoc :non-executable non-executable kwd-alist))

       (witness-dcls
        ;; The ordering here is somewhat subtle.
        (append
         ;; As in define, put stobj names first because they give us stobj-p
         ;; guards, which may be useful and probably can't depend on anything
         ;; else.
         (and stobj-names
              `((declare (xargs :stobjs ,stobj-names))))
         ;; Guards from the extended formals next.  These are likely to be
         ;; simple type guards, etc.  We sort them to put complex guards later
         ;; using the same strategy as in define.
         (cond ((atom formal-guards)
                nil)
               ((atom (cdr formal-guards))
                `((declare (xargs :guard ,(car formal-guards)))))
               (t
                (b* ((sorted-formal-guards (sort-formal-guards formal-guards world)))
                  `((declare (xargs :guard (and . ,sorted-formal-guards)))))))
         ;; Any explicit top-level :guard comes next.  This will typically be
         ;; for dependent typing kind of stuff between the formals, which
         ;; doesn't necessarily nicely fit into the extended formal mechanism.
         (and guard
              `((declare (xargs :guard ,guard))))
         ;; Finally, put in any :witness-dcls stuff.  Hopefully nobody will
         ;; ever really need to use this.
         (and non-executable
              `((declare (xargs :non-executable ,non-executable))))
         witness-dcls))

       ;; See the documentation for :verify-guards; we always submit the
       ;; definition with verify-guards nil, then explicitly try to verify its
       ;; guards afterward.
       (witness-dcls (cons '(declare (xargs :verify-guards nil)) witness-dcls))

       (bool-symbol (intern-in-package-of-symbol "BOOL" (pkg-witness (current-package state))))
       (returns     (getarg :returns `(,bool-symbol booleanp :rule-classes :type-prescription) kwd-alist))
       (returnspecs (parse-returnspecs name returns world))


       (main-def
        `(defun-sk ,name-fn ,formal-names
           (,quantifier ,bound-var-names ,exec-body)
           ,@(and rewrite      `(:rewrite ,rewrite))
           ,@(and witness-dcls `(:witness-dcls ,witness-dcls))
           ,@(and strengthen   `(:strengthen ,strengthen))
           ,@(and quant-ok     `(:quant-ok ,quant-ok))
           ,@(and skolem-name  `(:skolem-name ,skolem-name))
           ,@(and thm-name     `(:thm-name ,thm-name))
           #+non-standard-analysis
           ,@(and (assoc :classicalp kwd-alist)
                  `(:classicalp ,(cdr (assoc :classicalp kwd-alist))))))
       (guts (make-define-sk-guts :name name
                                  :name-fn name-fn
                                  :raw-formals raw-formals
                                  :formals formals
                                  :quantifier quantifier
                                  :bound-vars bound-vars
                                  :raw-body raw-body
                                  :exec-body exec-body
                                  :main-def main-def
                                  :macro macro
                                  :returnspecs returnspecs
                                  :kwd-alist kwd-alist
                                  :rest-events rest-events)))
    (mv guts state)))

(defun add-macro-aliases-from-define-sk-guts (guts)
  (b* (((define-sk-guts guts) guts))
    (and guts.macro
         `((add-macro-alias ,guts.name ,guts.name-fn)
           ;; This makes the alias known to the untranslate preprocessor for
           ;; define, which seems like a nice thing for prettier proof goals.
           (table define-macro-fns ',guts.name-fn ',guts.name)))))

(define add-define-sk-signature-from-guts (guts)
  (b* (((define-sk-guts guts)))
    ;; Now that the section has been submitted, we can compute its signature
    ;; block and prepend it to the topic (if any docs were generated)
    `(make-event
      (b* ((current-pkg (acl2::f-get-global 'acl2::current-package state))
           (base-pkg    (pkg-witness current-pkg))
           (name        ',guts.name)
           (all-topics  (xdoc::get-xdoc-table (w state)))
           (old-topic   (xdoc::find-topic name all-topics))
           ((unless old-topic)
            ;; Fine, it isn't documented.
            (value '(value-triple :invisible)))
           ((mv str state)
            (make-xdoc-top name ',guts.name-fn ',guts.formals
                           ',guts.returnspecs base-pkg state))
           (event (list 'xdoc::xdoc-prepend name str)))
        (value event)))))


(defun define-sk-events-from-guts (guts world)
  (b* (((define-sk-guts guts))
       (enabled       (getarg :enabled       nil guts.kwd-alist))
       (prepwork      (getarg :prepwork      nil guts.kwd-alist))
       (short         (getarg :short         nil guts.kwd-alist))
       (long          (getarg :long          nil guts.kwd-alist))
       (parents       (getarg :parents       nil guts.kwd-alist))
       (thm-name      (getarg :thm-name      nil guts.kwd-alist))
       (prognp        (getarg :progn         nil guts.kwd-alist))
       (verify-guards (getarg :verify-guards t   guts.kwd-alist))
       (guard-hints   (getarg :guard-hints   nil guts.kwd-alist))
       (guard-debug   (getarg :guard-debug   nil guts.kwd-alist))
       (set-ignores   (get-set-ignores-from-kwd-alist guts.kwd-alist))
       (start-max-absolute-event-number
        (acl2::max-absolute-event-number world)))
    `(,(if prognp 'defsection-progn 'defsection) ,guts.name
      ,@(and parents `(:parents ,parents))
      ,@(and short   `(:short ,short))
      ,@(and long    `(:long ,long))
      ,@(and prepwork
             `((with-output :stack :pop
                 (progn . ,prepwork))))

      ;; Macro, if necessary
      ,@(and guts.macro `((with-output :stack :pop ,guts.macro)))

      ;; Main definition
      ,@(if set-ignores
            `((encapsulate ()
                ,@set-ignores
                (with-output :stack :pop ,guts.main-def)))
          `((with-output :stack :pop ,guts.main-def)))

      ,@(add-macro-aliases-from-define-sk-guts guts)

      ;; Extend the define table right away, in case anything during
      ;; the rest-events needs to make use of it.
      ,(extend-define-sk-guts-alist guts)

      ;; BOZO maybe do something like set-define-current-function

      (local
       ;; Enable the function and thm for the :returns theorems and ///
       ;; events.  Even though it looks like these are already enabled since
       ;; we just defined them, we need to do this explicitly to ensure that
       ;; the /// section will be processed in a consistent way even in the
       ;; face of redundancy; see the comments in DEFINE for more info.
       (in-theory (enable ,guts.name ,thm-name)))

      (make-event
       (let* ((world (w state))
              (events (returnspec-thms ',guts.name ',guts.name-fn ',guts.returnspecs world)))
         (value (if events
                    `(with-output :stack :pop (progn . ,events))
                  '(value-triple :invisible)))))

      ,@(and verify-guards
             `((verify-guards ,guts.name-fn
                 ,@(and guard-hints `(:hints ,guard-hints))
                 ,@(and guard-debug `(:guard-debug ,guard-debug)))))

      ;; BOZO pe table?

      ,@(and guts.rest-events
             `((with-output :stack :pop
                 (progn
                   . ,guts.rest-events))))

      ,@(case enabled
          ;; Disable anything that should be disabled.  Doing it this way,
          ;; with disables only instead of any enables, avoids needing to
          ;; think hard about how :enable works with redundancy.
          (:all      nil)
          (:fn       `((in-theory (disable ,thm-name))))
          (:thm      `((in-theory (disable ,guts.name))))
          (otherwise `((in-theory (disable ,guts.name ,thm-name)))))

      ,(add-define-sk-signature-from-guts guts)

      (make-event (list 'value-triple
                        (if (eql ,start-max-absolute-event-number
                                 (acl2::max-absolute-event-number
                                  (acl2::w acl2::state)))
                            :redundant
                          (quote ',guts.name)))))))

(defun define-sk-fn (name args state)
  (declare (xargs :stobjs state))
  (b* (((mv guts state) (parse-define-sk name args nil state))
       (event (define-sk-events-from-guts guts (w state))))
    (value event)))

(defmacro define-sk (name &rest args)
  (let* ((verbose-tail (member :verbosep args))
         (verbosep (and verbose-tail (cadr verbose-tail))))
    `(with-output
       :stack :push
       ,@(and (not verbosep)
              '(:on (acl2::error) :off :all))
       (make-event
        (define-sk-fn ',name ',args state)))))

(defmacro acl2::define-sk (&rest args)
  `(define-sk . ,args))
