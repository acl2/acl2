; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "CUTIL")
(include-book "defaggregate")
(include-book "deflist")
(include-book "defprojection")
(include-book "xdoc-impl/fmt-to-str" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(set-state-ok t)

(defun interactive-p (state)
  (declare (xargs :mode :program))
  (not (f-get-global 'acl2::certify-book-info state)))

(make-event

; I originally wrote this file in logic mode.  You'll see theorems below, etc.
; But there is a problem:
;
;   - End-users (including me) would much rather have all this stuff in program
;     mode.  They don't care a lick about reasoning about cutil::formal-p and
;     that sort of thing, and we don't want theorems about the guts of define
;     messing with real proofs.
;
;   - Developers (including me) would much rather have all this stuff in logic
;     mode.  They want verified guards, assertions to be checked, etc.
;
; So, as a dumb hack: if we're aren't certifying a book, then do everything in
; logic mode to make sure the guards get checked.  If we're certifying the book,
; do it in program-mode so none of these theorems actually get exported.

 (if (interactive-p state)
     (value '(value-triple :invisible))
   (value '(program))))

(local (include-book "misc/assert" :dir :system))
(local (include-book "system/legal-variablep" :dir :system))

(defxdoc define
  :parents (cutil)
  :short "A very fine alternative to @(see defun)."

  :long "<h3>Introduction</h3>

<p>@('define') is an extension of @('defun')/@('defund') with:</p>

<ul>

<li>Richer @('formals') lists that permit keyword/optional arguments and
embedded guards and documentation, and which automatically infer @(see stobj)
declarations and <b>BOZO FUTURE WORK</b> some type declarations.</li>

<li>A more concise @(see xargs) syntax that also adds control over other
settings like @(see set-ignore-ok), @(see set-irrelevant-formals-ok), and
inlining.</li>

<li>A concise syntax for naming return values, documenting them, and proving
basic theorems (e.g., type-like theorems) about them.</li>

<li>Integration with @(see xdoc) with function signatures derived and a @(see
defsection)-like ability to associate related theorems with your function.</li>

<li>Automatic binding of @('__function__') to the name of the function, which
can be useful in error messages (see, e.g., @(see raise)) and, on CCL at least,
appears to produce identical compiled output when @('__function__') isn't used
in the body.</li>

</ul>

<p>The general form of @('define') is:</p>

@({
 (define name formals
   main-stuff
   [/// other-events])     ;; optional, starts with the symbol ///
})

<p>There's nothing special about the @('name'), it's just the name of the new
function to be defined, as in @(see defun).  The other parts all have their own
syntax and features to cover, and we address them in turn.</p>


<h3>The Formals</h3>

<p>The @('formals') syntax is a proper extension of the normal formals for a
@(see defun).  That is, you can still use a plain list of variable names.  In
this case, the only new feature of @('define') is that it automatically
determines which formals are @(see stobjs) and generates an appropriate
@('(declare (xargs :stobjs ...))') form.  But there are also some more
interesting extensions.</p>

<h4>Keyword and Optional Arguments</h4>

<p>You can also use @('&key') and @('&optional') as in @(see macro-args).
Other lambda-list keywords like @('&rest') aren't supported.</p>

<p>When @('define') sees these keywords, then instead of just producing a
@('defun') it will generate:</p>

<ul>
<li>A function, @('name-fn'),</li>
<li>A wrapper macro, @('name'),</li>
<li>A <see topic='@(url macro-aliases-table)'>macro alias</see> associating
@('name-fn') with @('name')</li>
</ul>

<h4>Embedded Guards and Documentation</h4>

<p>Beyond just naming the formals, you can specify simple guards for them and
document them right in the formals list.  Here is an example:</p>

@({
 (define split-up-string
   ((x stringp \"The string to split\")
    (separators (and (consp separators)
                     (character-listp separators))
     \"What letters to split on -- <b>dropped from the result!</b>\")
    &key
    (limit natp
     \"Where to stop, typically @('nil') which means @('(length x)')\"))
   ...)
})

<p>The general form for an extended formal is:</p>

@({
     (varname [guard] [xdoc])     i.e., both the guard and xdoc are optional
  OR (varname [xdoc] [guard])           and may be given in any order
})

<p>As a convenient shorthand, the @('guard') may be a single symbol, e.g.,
above the guard for @('x') is @('(stringp x)').  To be more precise:</p>

<ul>
 <li>@('t') and @('nil') are treated literally, and</li>
 <li>Any other symbol @('g') is treated as short for @('(g var)')</li>
</ul>

<p>Aside for future expansion: a nice side-effect of this treatment is that a
keyword like @(':foo') will produce the guard @('(:foo var)') which is invalid
and hence will be rejected.  So, if we eventually want to add keyword arguments
to our formals syntax, we'll be able to do that.</p>

<p>For more complex guards, you can also write down arbitrary terms, e.g.,
above @('separators') must be a non-empty character list.  We require that such
a guard be at least a cons to distinguish it from documentation and symbol
guards.  We also require that it is not simply a quoted constant.  This ensures
that guards can be distinguished from default values in macro arguments.  For
example, compare:</p>

@({
     &key (x 'atom)     ;; x has no guard, default value 'atom
 vs. &key (x atom)      ;; x has guard (atom x), default value nil
 vs. &key ((x atom) '3) ;; x has guard (atom x), default value 3
})

<p>BOZO this is not yet implemented.  Eventually I want it to be true: As a
special convenience, certain guards like @('stringp') and @('(unsigned-byte-p
32 x)'), are recognized as @(see type-spec)s and result in @(see type)
declarations for the Lisp compiler.  This may occasionally improve efficiency.
Note that this is a very limited mechanism and it can easily fail to add
declarations that are trivially implied by the guard.</p>

<p>The @('xdoc') is any string.  It will be embedded within the within @(see
xdoc) documentation, so you may make use of @(see xdoc::markup) and @(see
xdoc::preprocessor) directives.  Typically these descriptions should be short
and not include document-structuring tags like @('<p>'), @('<ul>'), @('<h3>'),
and so forth.  See the section on xdoc integration, below, for more
details.</p>


<h3>The Main Stuff</h3>

<p>After the formals we get to the main part of the definition.  This section
is a mixed list that may contain:</p>

<ul>
<li><i>Extended options</i> of the form @(':name value')</li>
<li>Declarations of the form @('(declare ...)')</li>
<li>Traditional documentation strings, i.e., @('\"...\"')</li>
<li>The function's body, a term</li>
</ul>

<p>Except for the extended options, this is just like @('defun').</p>

<p>Extended options can go <b>anywhere</b> between the formals and the special
separator @('///') (if any) or the end of the @('define').  Here is a contrived
example:</p>

@({
 (define parse-foo (channel n &optional (state 'state))

   :parents (parser) ;; extended option

   ;; declarations/docstrings must come before body, as in defun
   (declare (type integer n))
   (declare (ignorable channel))
   \"Traditional doc string.  Boo.\"
   (declare (xargs :normalize nil))

   :guard (< 17 n) ;; extended option

   (b* ((next (peek-char channel state))  ;; function's body
        ...)
      (mv result state))

   :measure (file-measure channel state)  ;; more extended opts.
   :hints ((\"Goal\" ...))
   :guard-debug t)
})

<p>How does this work, exactly?  Ordinarily, @('defun') distinguishes the
function's body from documentation strings and declarations using a simple
rule: the last item is the function's body, and everything before it must be a
declaration or documentation string.  For @('define'), we simply add a
preprocessing step:</p>

<ul>
<li>First, all of the extended options are extracted.</li>
<li>Then, the remaining parts are handled using the ordinary @('defun') rule.</li>
</ul>

<p>There is one special case where this approach is <b>incompatible</b> with
@('defun'): if your function's body is nothing more than a keyword symbol,
e.g.,</p>

@({
 (defun returns-foo (x)
   (declare (ignore x))
   :foo)
})

<p>then it cannot be converted into a @('define') since the body looks like
a (malformed) extended option.  I considered workarounds to avoid this, but
decided that it is better to just live with not being able to define these
kinds of functions.  They are very weird, anyway.</p>

<h4>Basic Extended Options</h4>

<p>All @(see xargs) are available as extended options.  In practice this just
makes things more concise and better looking, e.g., compare:</p>

@({
 (defun strpos-fast (x y n xl yl)
   (declare (xargs :guard (and ...)
                   :measure (nfix ...)))
   ...)
 vs.
 (define strpos-fast (x y n xl yl)
   :guard (and ...)
   :measure (nfix ...)
   ...)
})

<p>Some additional minor options include:</p>

<dl>

<dt>@(':enabled val')</dt>

<dd>By default the function will be disabled after the @('other-events') are
processed.  If @(':enabled t') is provided, we will leave it enabled,
instead.</dd>

<dt>@(':ignore-ok val')</dt>

<dd>Submits @('(set-ignore-ok val)') before the definition.  This option is
local to the @('define') only and does not affect the @('other-events').</dd>

<dt>@(':irrelevant-formals-ok val')</dt>

<dd>Submits @('(set-irrelevant-formals-ok val)') before the definition; local
to this @('define') only and not to any @('other-events').</dd>

<dt>@(':inline val')</dt>

<dd>Generates an inline function instead of an ordinary function, in a manner
similar to @(see defun-inline).</dd>

<dt>@(':parents parent-list')</dt>
<dt>@(':short str')</dt>
<dt>@(':long str')</dt>

<dd>These are @(see defxdoc)-style options for documenting the function.  They
are passed to a @('defsection') for this definition.</dd>

<dt>@(':prepwork events')</dt>

<dd>These are any arbitrary events you want to put before the definition
itself, for instance it might include @('-aux') functions or local lemmas
needed for termination.</dd>

</dl>

<h4>@('Returns') Specifications</h4>

<p>A more elaborate extended option is @(':returns').  This is a concise way to
name, document, and prove basic type-like theorems about the return values of
your functions.  The general form is:</p>

@({
    :returns return-spec       ;; for single-value functions
 or :returns (mv return-spec*) ;; for multiple-valued functions
})

<p>There should be exactly one @('return-spec') per return value.  Each
return-spec has the form:</p>

@({
     name               ;; just for naming return values
  or (name [option]*)   ;; for naming, documenting, and proving theorems
})

<p>where @('name') is a symbol and the options can come in any order.  To
distinguish between the two forms of @(':returns'), it is not legal to use
@('mv') as the name of a return value.  The options are:</p>

<dl>

<dt>@('<xdoc>'), any string literal</dt>

<dd>You can document each return value with a string literal.  The string may
make use of @(see xdoc::markup) and @(see xdoc::preprocessor) directives.
Typically these descriptions should be short and not include
document-structuring tags like @('<p>'), @('<ul>'), @('<h3>'), and so forth.
See the section on xdoc integration, below, for more details.</dd>

<dt>@('<return-type>'), a symbol or term</dt>

<dd>When provided, the return type is used to generate a basic type-like
theorems about the return values.</dd>

<dd><b>Important Note</b> in the multiple-valued case, this approach assumes
you are using the @('tools/mv-nth') book.  The theorems we prove target terms
like @('(mv-nth 0 (f ...))') and @('(mv-nth 1 (f ...))').  This will not work
well if @(see mv-nth) is enabled, especially about the 0th return value. For
your convenience, @('define') automatically includes the @('tools/mv-nth')
book.  You really should be using it, you know.</dd>

<dd>As a convenient shorthand, you can use a single symbol like @('evenp').
The theorem to be proven in this case might be, e.g., @('(evenp (f x))') for a
single-valued function, or @('(evenp (mv-nth 3 (f x)))') if this is the
fourth (because of zero-indexing) return value of a multiply-valued function.
The symbol @('t') is explicitly allowed and results in no theorem.  The symbol
@('nil') and keyword symbols are explicitly invalid as return types.</dd>

<dd>In certain cases, you may wish to prove a more complex theorem, e.g., say
we want to prove this return value is always greater than 5.  To support this,
you can write a return type like @('(< 5 ans)'), where @('ans') is the
@('name') of this return value.  You can also refer to the names of other
return values in this term.  To make it easy to distinguish return types from
other options, the return type term must be a cons and must not begin with
@('quote').</dd>

<dt>@(':hyp hyp-term')</dt>

<dd>This option only makes sense when there is a return-type term.  By default,
the return-type theorem is unconditional.  If the theorem needs a hypothesis,
you can put it here.</dd>

<dd>Frequently, the hypothesis you want for a type-like theorem is for the
guards of the function to be met.  As a convenient shorthand, @('hyp-term') may
be:

<ul>
<li>@(':guard') -- use the function's guard as the hypothesis</li>
<li>@(':fguard') -- like @(':guard'), but @(see force) the entire guard</li>
</ul>

If neither of these is what you want, you can provide an arbitrary
@('hyp-term').  Typically this term should mention only the formals of your
function.  The return values of the theorem will not be bound in scope of the
hyp, so trying to refer to them in a hypothesis is generally an error.</dd>

<dt>@(':hints hints-term')</dt>

<dd>This option only makes sense when there is a return-type term.  By default,
this is @('nil'), but when specified, the hints are passed to the proof attempt
for the associated return-type.</dd>

<dt>@(':rule-classes classes')</dt>

<dd>This option only makes sense when there is a return-type term.  By default,
the return-type theorem is added as a @(':rewrite') rule.  If you want to use
other @(see rule-classes), then you will want to override this default.</dd>

</dl>

<h4>@('Assert') Specification</h4>

<p>It can be convenient when testing code to check that the arguments of a
function meet certain criteria, and ACL2 implements that check with a @(see
guard).  In order to take this idea one step further, @('define') provides a
way to check the return value of the defined function at run-time, through the
@(':assert') keyword argument.</p>

<p>The @(':assert') keyword accepts either a symbol or a list of symbols.  In
the event that a symbol or a list containing exactly one symbol is provided, a
check will be added near the end of the defined function's body that checks
that the return value passes the predicate associated with that symbol.
Sometimes the defined function will return multiple-values.  In this case, the
argument given to @(':assert') should be a list of symbols, of length equal to
the number of return values.  @('Define') will then take each symbol and use
its associated function to check that the <i>i</i>'th return value passes the
<i>i</i>'th predicate symbol's test (where <i>i</i> ranges from 1 to the number
of values returned by the defined function).</p>

<p>In the long-term, we would like @('define') to only require a Boolean value
as the argument to @(':assert') and to infer the requirements of the return
values from the @(':returns') specifications.  If any user wishes to make this
change to @('define'), they should feel free to do so.</p>

<p>Another problem of the current implementation of @(':assert') is that if the
same predicate is used twice, the @('define') will break.  A workaround for
this is to define a second predicate that is simply a wrapper for the desired
predicate.  The user can then use that second predicate in the second place it
is needed.</p>

<p>BOZO assert is probably orthogonal to define and should just be turned into
some kind of tracing/advise mechanism.</p>


<h3>The Other Events</h3>

<p>The final part of a @('define') is an area for any arbitrary events to be
put.  These events will follow the function's definition, but will be submitted
<b>before</b> disabling the function.</p>

<p>Any event can be included here, but this space is generally intended for
theorems that are \"about\" the function that has just been defined.  The
events in this area will be included in the @(see xdoc), if applicable, as if
they were part of the same @(see defsection).</p>

<p>To distinguish the @('other-events') from the @('main-stuff'), we use the
special symbol @('///') to separate the two.</p>

<p>Why do we use this goofy symbol?  In Common Lisp, @('///') has a special
meaning and is used by the Lisp read-eval-print loop.  Because of that, ACL2
does not allow you to bind it in @(see let) statements or use it as a formal in
a definition.  Because of <i>that</i>, we can be sure that @('///') is not the
body of any function definition, so it can be reliably used to separate the
rest-events.  As bonus features, @('///') is already imported by any <see
topic='@(url defpkg)'>package</see> that imports
@('*common-lisp-symbols-from-main-lisp-package*'), and even sort of looks like
some kind of separator!</p>


")


; Preliminaries ---------------------------------------------------------------




; Trivial lemmas...

(local (defthm consp-of-assoc-equal
         (implies (alistp alist)
                  (equal (consp (assoc-equal key alist))
                         (if (assoc-equal key alist)
                             t
                           nil)))
         :hints(("Goal" :in-theory (enable assoc-equal)))))

(local (defthm alistp-of-delete-assoc
         (implies (alistp alist)
                  (alistp (delete-assoc key alist)))))

(local (defthm stringp-of-car-when-string-listp
         (implies (string-listp x)
                  (equal (stringp (car x))
                         (consp x)))))


; World Inspection ------------------------------------------------------------

(defsection var-is-stobj-p

  (defund var-is-stobj-p (var world)
    (declare (xargs :guard (and (symbolp var)
                                (plist-worldp world))))
    (consp (getprop var 'acl2::stobj nil 'current-acl2-world world)))

  (local
   (progn
     (assert! (not (var-is-stobj-p 'foo (w state))))
     (assert! (var-is-stobj-p 'state (w state)))
     (defstobj foo (field1 :initially 0))
     (assert! (var-is-stobj-p 'foo (w state))))))

(defsection look-up-formals

  (defund look-up-formals (fn world)
    (declare (xargs :guard (and (symbolp fn)
                                (plist-worldp world))))
    (b* ((look (getprop fn 'acl2::formals :bad 'acl2::current-acl2-world world))
         ((when (eq look :bad))
          (er hard? 'look-up-formals
              "Can't look up the formals for ~x0!" fn))
         ((unless (symbol-listp look))
          (er hard? 'look-up-formals
              "Expected a symbol-listp, but found ~x0!" look)))
      look))

  (local (in-theory (enable look-up-formals)))

  (defthm symbol-listp-of-look-up-formals
    (symbol-listp (look-up-formals fn world)))

  (local
   (progn
    (assert! (equal (look-up-formals 'look-up-formals (w state))
                    '(fn world))))))

(defsection look-up-guard

  (defund look-up-guard (fn world)
    (declare (xargs :guard (and (symbolp fn)
                                (plist-worldp world))))
    (b* ((?tmp
          ;; Silly... make sure the function exists, causing an error
          ;; otherwise.
          (look-up-formals fn world)))
      (getprop fn 'acl2::guard t 'acl2::current-acl2-world world)))

  (local
   (progn
   (defun f1 (x) x)
   (defun f2 (x) (declare (xargs :guard (natp x))) x)
   (defun f3 (x) (declare (xargs :guard (and (integerp x)
                                             (<= 3 x)
                                             (<= x 13))))
     x)
   (assert! (equal (look-up-guard 'f1 (w state)) 't))
   (assert! (equal (look-up-guard 'f2 (w state)) '(natp x)))
   (assert! (equal (look-up-guard 'f3 (w state))
                   '(IF (INTEGERP X)
                        (IF (NOT (< X '3)) (NOT (< '13 X)) 'NIL)
                        'NIL))))))

(defsection look-up-return-vals

  ;; Returns the stobjs-out property, a list that may have NILs and stobj names
  ;; with the same length as the number of return vals for FN.

  (defund look-up-return-vals (fn world)
    (declare (xargs :guard (and (symbolp fn)
                                (plist-worldp world))))
    (b* ((stobjs-out
          (getprop fn 'acl2::stobjs-out :bad 'acl2::current-acl2-world world))
         ((when (eq stobjs-out :bad))
          (er hard? 'look-up-return-vals
              "Can't look up stobjs-out for ~x0!" fn)
          '(NIL))
         ((unless (and (consp stobjs-out)
                       (symbol-listp stobjs-out)))
          (er hard? 'look-up-return-vals
              "Expected stobjs-out to be a non-empty symbol-list, but found ~x0."
              stobjs-out)
          '(NIL)))
      stobjs-out))

  (local (in-theory (enable look-up-return-vals)))

  (defthm symbol-listp-of-look-up-return-vals
    (symbol-listp (look-up-return-vals fn world)))

  (local
   (progn
     (defun f1 (x) x)
     (defun f2 (x) (mv x x))
     (defun f3 (x state) (declare (xargs :stobjs state)) (mv x state))
     (assert! (equal (look-up-return-vals 'f1 (w state)) '(nil)))
     (assert! (equal (look-up-return-vals 'f2 (w state)) '(nil nil)))
     (assert! (equal (look-up-return-vals 'f3 (w state)) '(nil state))))))


(defsection look-up-wrapper-args

; Like look-up-formals, except that wrapper can be a function or a macro.

  (defund look-up-wrapper-args (wrapper world)
    (declare (xargs :guard (and (symbolp wrapper)
                                (plist-worldp world))))
    (b* ((look (getprop wrapper 'acl2::formals :bad
                        'acl2::current-acl2-world world))
         ((unless (eq look :bad))
          look)
         (look (getprop wrapper 'acl2::macro-args :bad
                        'acl2::current-acl2-world world))
         ((unless (eq look :bad))
          look))
      (er hard? 'look-up-wrapper-args
          "Failed to find formals or macro-args for ~x0!" wrapper)))
  (local
   (progn
     (defun f1 (x) x)
     (defmacro f2 (x) x)
     (defmacro f3 (x y &key (c '5) (d '7)) (list x y c d))
     (assert! (equal (look-up-wrapper-args 'f1 (w state)) '(x)))
     (assert! (equal (look-up-wrapper-args 'f2 (w state)) '(x)))
     (assert! (equal (look-up-wrapper-args 'f3 (w state))
                     '(x y &key (c '5) (d '7)))))))



; -------------- Formals Stuff ------------------------------------------------

(defaggregate formal
  (name
   guard   ; always a term, t for formals with no guard
   doc     ; always a string, "" for formals with no documentation
   )
  :tag :formal
  :require ((legal-variablep-of-formal->name
             (legal-variablep name))
            (stringp-of-vl-formal->doc
             (stringp doc)
             :rule-classes :type-prescription)))

(deflist formallist-p (x)
  (formal-p x)
  :elementp-of-nil nil)

(defund parse-formal-name (fnname varname)
  (declare (xargs :guard t))
  (b* (((when (legal-variablep varname))
        varname)
       (fake-arglist (list varname))
       ((when (acl2::arglistp fake-arglist))
        (er hard? 'parse-formal-name
            "Error in ~x0: formal ~x1: mysterious problem that Jared thinks ~
             should be impossible, please tell him that he is wrong."
            fnname varname)
        'default-valid-legal-variablep)
       ((mv & reason)
        ;; BOZO should be able to get rid of this ec-call if someone can
        ;; verify the guards of find-first-bad-arg.
        (ec-call (acl2::find-first-bad-arg fake-arglist))))
    (er hard? 'parse-formal-name
        "Error in ~x0: formal ~x1 is invalid: ~s2." fnname varname reason)
    'default-valid-legal-variablep))

(defthm legal-variablep-of-parse-formal-name
  (legal-variablep (parse-formal-name fnname varname))
  :hints(("Goal" :in-theory (enable parse-formal-name))))

(defund parse-formal-item (fnname varname item guards docs)
  "Returns (mv guards docs)"
  (declare (xargs :guard (legal-variablep varname)))
  (cond ((booleanp item)
         (mv (cons item guards) docs))
        ((symbolp item)
         (mv (cons `(,item ,varname) guards) docs))
        ((and (consp item)
              (not (eq (car item) 'quote)))
         (mv (cons item guards) docs))
        ((stringp item)
         (mv guards (cons item docs)))
        (t
         (progn$
          (er hard? 'parse-formal-item
              "Error in ~x0, formal ~x1: expected guard specifiers or ~
               documentation strings, but found ~x2."
              fnname varname item)
          (mv guards docs)))))

(defthm string-listp-of-parse-formal-item-1
  (implies (string-listp docs)
           (b* (((mv ?guards docs)
                 (parse-formal-item fnname varname items guards docs)))
             (string-listp docs)))
  :hints(("Goal" :in-theory (enable parse-formal-item))))

(defund parse-formal-items (fnname varname items guards docs)
  "Returns (mv guards docs)"
  (declare (xargs :guard (legal-variablep varname)))
  (b* (((when (not items)) (mv guards docs))
       ((when (atom items))
        (er hard? 'parse-formal-items
            "Error in ~x0: expected formal-items to be nil-terminated, ~
             but found ~x1 as the final cdr." fnname items)
        (mv guards docs))
       ((mv guards docs)
        (parse-formal-item fnname varname (car items) guards docs)))
    (parse-formal-items fnname varname (cdr items) guards docs)))

(defthm string-listp-of-parse-formal-items-1
  (implies (string-listp docs)
           (b* (((mv ?guards docs)
                 (parse-formal-items fnname varname items guards docs)))
             (string-listp docs)))
  :hints(("Goal" :in-theory (enable parse-formal-items))))

(defund parse-formal (fnname formal)
  "Returns a formal-p"
  (declare (xargs :guard t))
  (b* (((when (atom formal))
        (b* ((varname (parse-formal-name fnname formal)))
          (make-formal :name varname
                       :guard t
                       :doc "")))
       (varname (parse-formal-name fnname (car formal)))
       (items   (cdr formal))
       ((mv guards docs) (parse-formal-items fnname varname items nil nil))
       (guard (cond ((atom guards) 't)
                    ((eql (len guards) 1) (car guards))
                    (t (er hard? 'parse-formal
                           "Error in ~x0, formal ~x1: expected a single guard ~
                            term, but found ~&2." fnname varname guards))))
       (doc   (cond ((atom docs) "")
                    ((eql (len docs) 1) (car docs))
                    (t (progn$
                        (er hard? 'parse-formal
                            "Error in ~x0, formal ~x1: expected a single xdoc ~
                             string, but found ~&2." fnname varname docs)
                        "")))))
    (make-formal :name varname
                 :guard guard
                 :doc doc)))

(defthm formal-p-of-parse-formal
  (formal-p (parse-formal fnname formal))
  :hints(("Goal" :in-theory (enable parse-formal))))

(defund parse-formals (fnname formals)
  ;; Assumes lambda-list keywords have already been removed from formals.
  (declare (xargs :guard t))
  (b* (((when (not formals))
        nil)
       ((when (atom formals))
        (er hard? 'parse-formals
            "Error in ~x0: expected formals to be nil-terminated, but found ~
             ~x1 as the final cdr." fnname formals)))
    (cons (parse-formal fnname (car formals))
          (parse-formals fnname (cdr formals)))))

(defthm formallist-p-of-parse-formals
  (formallist-p (parse-formals fnname formals))
  :hints(("Goal" :in-theory (enable parse-formals))))

(defprojection formallist->names (x)
  (formal->name x)
  :guard (formallist-p x)
  :nil-preservingp t
  :optimize nil)

(defprojection formallist->guards (x)
  (formal->guard x)
  :guard (formallist-p x)
  :nil-preservingp t
  :optimize nil)

(defund formallist-collect-stobjs (x world)
  (declare (xargs :guard (and (formallist-p x)
                              (plist-worldp world))))
  (cond ((atom x)
         nil)
        ((var-is-stobj-p (formal->name (car x)) world)
         (cons (car x) (formallist-collect-stobjs (cdr x) world)))
        (t
         (formallist-collect-stobjs (cdr x) world))))

(defthm formallist-p-of-formallist-collect-stobjs
  (implies (formallist-p x)
           (formallist-p (formallist-collect-stobjs x world)))
  :hints(("Goal" :in-theory (enable formallist-collect-stobjs))))




; -------------- Macro Formals Support ----------------------------------------

(defund has-macro-args (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (or (acl2::lambda-keywordp (car x))
        (has-macro-args (cdr x)))))

(defund remove-macro-args (fnname formals seenp)
  ;; Generates a new list of (unparsed) formals, with the macro arguments
  ;; removed.  This is going to be the list of formals for the -fn.  We are
  ;; going to remove "&key" and "&optional" from formals, and also fix up
  ;; any keyword/optional formals that have default values.
  ;;
  ;; When an argument has a default value it looks like
  ;;   (foo 'default).
  ;; The quote here distinguishes it from an extended formal that has a guard,
  ;; e.g., (foo 'atom) has a default value of 'atom and no guard, whereas
  ;; (foo atom) is just a plain extended formal with no default value (well, a
  ;; default value of nil) and a guard of (atom foo).
  ;;
  ;; Seenp says whether we've seen &key or &optional yet.  Until we've seen one
  ;; of these we don't change anything.
  (declare (xargs :guard t))
  (b* (((when (atom formals))
        formals)
       ((cons arg1 rest) formals)
       ((when (or (eq arg1 '&key)
                  (eq arg1 '&optional)))
        (remove-macro-args fnname rest t))
       ((when (acl2::lambda-keywordp arg1))
        (er hard? 'remove-macro-args
            "Error in ~x0: ~x1 only supports &key and &optional macro-style ~
             arguments, but found ~x2." fnname 'define arg1))
       ((unless seenp)
        ;; Haven't yet seen &key/&optional, so don't change any args yet.
        (cons arg1 (remove-macro-args fnname rest seenp)))

       ;; Saw &keyword/&optional already and this isn't another keyword.  So,
       ;; this is a real keyword/optional argument.  We need to remove any
       ;; default value.
       ((when (and (consp arg1)
                   (true-listp arg1)
                   (equal (len arg1) 2)
                   (consp (second arg1))
                   (eq (car (second arg1)) 'quote)))
        ;; Arg1 matches (foo 'value), so it has a default value to remove.
        ;; Change it to drop the default value.
        (cons (first arg1) (remove-macro-args fnname rest seenp))))

    ;; Else, it doesn't match (foo 'value), so leave it alone.
    (cons arg1 (remove-macro-args fnname rest seenp))))

(local
 (progn
   (assert! (equal (remove-macro-args 'f '(a b c) nil)
                   '(a b c)))
   (assert! (equal (remove-macro-args 'f '(a b c &key d e) nil)
                   '(a b c d e)))
   (assert! (equal (remove-macro-args 'f '(a b c &key d &optional e) nil)
                   '(a b c d e)))
   (assert! (equal (remove-macro-args 'f '(a b c &optional d e) nil)
                   '(a b c d e)))
   (assert! (equal (remove-macro-args 'f '(a b c &key (d true-listp) e) nil)
                   ;; true-listp is unquoted so it's a guard
                   '(a b c (d true-listp) e)))
   (assert! (equal (remove-macro-args 'f '(a b c &key (d 'true-listp) e) nil)
                   ;; 'true-listp is quoted so it's a default value
                   '(a b c d e)))
   (assert! (equal (remove-macro-args 'f '(a b c &key (d "foo") e) nil)
                   ;; "foo" is unquoted so it's an xdoc string
                   '(a b c (d "foo") e)))
   (assert! (equal (remove-macro-args 'f '(a b c &key (d '"foo") e) nil)
                   ;; '"foo" is quoted so it's a default value
                   '(a b c d e)))
   (assert! (equal (remove-macro-args 'f '(a b c &key ((d atom) '3) (e true-listp)) nil)
                   '(a b c (d atom) (e true-listp))))))


(defund formals-for-macro (fnname formals seenp)
  ;; Remove extended formal stuff (guards, documentation) and just get down to
  ;; a list of variable names and &key/&optional stuff.  This will be the
  ;; formals for the wrapper macro.
  (declare (xargs :guard t))
  (b* (((when (atom formals))
        formals)
       ((cons arg1 rest) formals)
       ((when (or (eq arg1 '&key)
                  (eq arg1 '&optional)))
        (cons arg1 (formals-for-macro fnname rest t)))
       ((when (acl2::lambda-keywordp arg1))
        (er hard? 'formals-for-macro
            "Error in ~x0: ~x1 only supports &key and &optional macro-style ~
             arguments, but found ~x2." fnname 'define arg1))

       ((unless seenp)
        ;; Haven't yet seen &key/&optional, so the only args should be ordinary
        ;; symbols and extended formals.  Keep just the name.  If it's a
        ;; extended formal then it has the form (name ...).
        (cons (if (atom arg1) arg1 (car arg1))
              (formals-for-macro fnname rest seenp)))

       ;; Saw &keyword/&optional already and this isn't another keyword.  So,
       ;; this is a real keyword/optional argument.  If there's a default value
       ;; we need to keep it.
       ((when (and (consp arg1)
                   (true-listp arg1)
                   (equal (len arg1) 2)
                   (consp (second arg1))
                   (eq (car (second arg1)) 'quote)))
        ;; Arg1 matches (extended-formal 'value).  We need to keep just
        ;; (name 'value)
        (let* ((eformal     (first arg1))
               (default-val (second arg1)) ;; already quoted
               (name        (if (atom eformal) eformal (car eformal))))
          (cons (list name default-val)
                (formals-for-macro fnname rest seenp)))))

    ;; Else, it doesn't match (foo 'value), so just do the name extraction like
    ;; normal.
    (cons (if (atom arg1) arg1 (car arg1))
          (formals-for-macro fnname rest seenp))))

(local
 (progn
   (assert! (equal (formals-for-macro 'f '(a b c) nil)
                   '(a b c)))
   (assert! (equal (formals-for-macro 'f '(a b c &key d e) nil)
                   '(a b c &key d e)))
   (assert! (equal (formals-for-macro 'f '(a b c &key d &optional e) nil)
                   '(a b c &key d &optional e)))
   (assert! (equal (formals-for-macro 'f '(a b c &optional d e) nil)
                   '(a b c &optional d e)))
   (assert! (equal (formals-for-macro 'f '(a b c &key (d true-listp) e) nil)
                   ;; true-listp is unquoted so it's a guard
                   '(a b c &key d e)))
   (assert! (equal (formals-for-macro 'f '(a b c &key (d 'true-listp) e) nil)
                   ;; 'true-listp is quoted so it's a default value
                   '(a b c &key (d 'true-listp) e)))
   (assert! (equal (formals-for-macro 'f '(a b c &key (d "foo") e) nil)
                   ;; "foo" is unquoted so it's an xdoc string
                   '(a b c &key d e)))
   (assert! (equal (formals-for-macro 'f '(a b c &key (d '"foo") e) nil)
                   ;; '"foo" is quoted so it's a default value
                   '(a b c &key (d '"foo") e)))
   (assert! (equal (formals-for-macro 'f '(a b c &key ((d atom) '3) (e true-listp)) nil)
                   '(a b c &key (d '3) e)))))

(defun make-wrapper-macro (fnname fnname-fn formals)
  (declare (xargs :guard (and (symbolp fnname)
                              (symbolp fnname-fn))))
  (b* ((fn-formals     (remove-macro-args fnname formals nil))
       (macro-formals  (formals-for-macro fnname formals nil))
       (parsed-formals (parse-formals fnname fn-formals))
       (fn-arg-names   (formallist->names parsed-formals)))
    `(defmacro ,fnname ,macro-formals
       (list ',fnname-fn . ,fn-arg-names))))

; -------------- Assertion Specifications -------------------------------------

(defun parse-assert-tests (assertion ctx)
  (declare (xargs :guard (symbol-listp assertion)))
  (cond ((atom assertion)
         nil)

; Predicate's symbol is also the local variable name.  It would be good to call
; gensym, along with a call of check-vars-not-free so that the same predicate
; could be used twice.  I'm not fixing this for now, because really we should
; be using the returns specifications, and doing so will obviate this issue.

        (t (cons `(if (,(car assertion) ,(car assertion)) 
                      t
                    (er hard? ',ctx
                        "Assertion failure.  The following was supposed to ~
                           be of type ~x0: ~x1"
                        ',(car assertion)
                        ,(car assertion)))
                 (parse-assert-tests (cdr assertion) ctx)))))

; -------------- Returns Specifications ---------------------------------------

(defaggregate returnspec
  (name
   doc           ; "" when omitted
   return-type   ; t when omitted
   hyp           ; t when omitted
   hints         ; nil when omitted
   rule-classes  ; :rewrite when omitted
   )
  :tag :return-spec
  :require ((symbolp-of-returnspec->name
             (symbolp name)
             :rule-classes :type-prescription)
            (stringp-of-returnspec->doc
             (stringp doc)
             :rule-classes :type-prescription)))

(deflist returnspeclist-p (x)
  (returnspec-p x)
  :elementp-of-nil nil)

(defconst *default-returnspec*
  (make-returnspec :name 'ret
                   :doc ""
                   :return-type t
                   :hyp t
                   :hints nil
                   :rule-classes :rewrite))

(defund extract-keywords (fnname legal-kwds args kwd-alist)
  "Returns (mv kwd-alist other-args)"
  (declare (xargs :guard (and (symbol-listp legal-kwds)
                              (no-duplicatesp legal-kwds)
                              (alistp kwd-alist))))
  (b* (((when (atom args))
        (mv kwd-alist args))
       (arg1 (first args))
       ((when (keywordp arg1))
        (b* (((unless (member arg1 legal-kwds))
              (er hard? 'extract-keyword-aux
                  "Error in ~x0: invalid keyword ~x1." fnname arg1)
              (mv nil nil))
             ((when (atom (rest args)))
              (er hard? 'extract-keywords
                  "Error in ~x0: expected keyword ~x1 to be followed by an ~
                   argument." fnname arg1)
              (mv nil nil))
             ((when (assoc arg1 kwd-alist))
              (er hard? 'extract-keywords
                  "Error in ~x0: found multiple occurrences of keyword ~x1."
                  fnname arg1)
              (mv nil nil))
             (value (second args))
             (kwd-alist (acons arg1 value kwd-alist)))
          (extract-keywords fnname legal-kwds (cddr args) kwd-alist)))
       ((mv kwd-alist other-args)
        (extract-keywords fnname legal-kwds (cdr args) kwd-alist)))
    (mv kwd-alist (cons arg1 other-args))))

(defthm true-listp-of-extract-keywords
  (implies (true-listp args)
           (true-listp
            (mv-nth 1 (extract-keywords fnname legal-kwds args kwd-alist))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable extract-keywords))))

(defthm alistp-of-extract-keywords
  (implies (force (alistp kwd-alist))
           (b* (((mv kwd-alist ?other-args)
                 (extract-keywords fnname legal-kwds args kwd-alist)))
             (alistp kwd-alist)))
  :hints(("Goal" :in-theory (enable extract-keywords))))

(defund parse-returnspec-item (fnname varname item terms docs)
  "Returns (mv terms docs)"
  (declare (xargs :guard t))
  (cond ((eq item t)
         ;; T is explicitly allowed as a return type
         (mv (cons item terms) docs))
        ((or (eq item nil)
             (keywordp item))
         (progn$
         ;; NIL/keywords are explicitly not allowed
          (er hard? 'parse-returnspec-item
              "Error in ~x0: return type for ~x1 is ~x2, which is ~
              not allowed." fnname varname item)
          (mv terms docs)))
        ((symbolp item)
         (mv (cons `(,item ,varname) terms) docs))
        ((and (consp item)
              (not (eq (car item) 'quote)))
         (mv (cons item terms) docs))
        ((stringp item)
         (mv terms (cons item docs)))
        (t
         (progn$
          (er hard? 'parse-returnspec-item
              "Error in ~x0, return type for ~x1: expected return ~
               type terms or documentation strings, but found ~x2."
              fnname varname item)
          (mv terms docs)))))

(defthm string-listp-of-parse-returnspec-item
  (implies (string-listp docs)
           (b* (((mv ?terms docs)
                 (parse-returnspec-item fnname varname items terms docs)))
             (string-listp docs)))
  :hints(("Goal" :in-theory (enable parse-returnspec-item))))

(defund parse-returnspec-items (fnname varname items terms docs)
  "Returns (mv terms docs)"
  (declare (xargs :guard t))
  (b* (((when (not items))
        (mv terms docs))
       ((when (atom items))
        (er hard? 'parse-returnspec-items
            "Error in ~x0: expected returnspec-items for ~x1 to be ~
             nil-terminated, but found ~x2 as the final cdr."
            fnname varname items)
        (mv terms docs))
       ((mv terms docs)
        (parse-returnspec-item fnname varname (car items) terms docs)))
    (parse-returnspec-items fnname varname (cdr items) terms docs)))

(defthm string-listp-of-parse-returnspec-items
  (implies (string-listp docs)
           (b* (((mv ?terms docs)
                 (parse-returnspec-items fnname varname items terms docs)))
             (string-listp docs)))
  :hints(("Goal" :in-theory (enable parse-returnspec-items))))

(defund parse-returnspec (fnname x world)
  (declare (xargs :guard (plist-worldp world)))
  (b* (((when (eq x 'mv))
        (er hard? 'parse-returnspec
            "Error in ~x0: return values may not be named MV."
            fnname)
        *default-returnspec*)
       ((when (symbolp x))
        ;; Fine, just a name, no docs/type
        ;; Someone once got very confused why :returns character-listp
        ;; wasn't proving that his function wasn't returning a character
        ;; list.  So, now, make sure this isn't a defined function.
        (b* ((look (getprop x 'acl2::formals :bad
                            'acl2::current-acl2-world world))
             ((unless (eq look :bad))
              (er hard? 'parse-returnspec
                  "Error in ~x0: you named a return value ~x1, which is ~
                   is the name of a defined function, but you don't have ~
                   any return type associated with this value.  There's a ~
                   good chance this you meant this to be the return value's ~
                   type instead of its name.~%~%~
                   If you really want to name this return value ~x1 and ~
                   not prove anything about it, you can use syntax like ~
                   ~x2.~%"
                  fnname x (list x t))
              *default-returnspec*))
          ;; Else, seems fine, just a name.
          (make-returnspec :name x
                           :doc ""
                           :return-type t
                           :rule-classes :rewrite
                           :hyp nil
                           :hints nil)))
       ((when (atom x))
        (er hard? 'parse-returnspec
            "Error in ~x0: return specifiers must be symbols or lists, but ~
             found: ~x1" fnname x)
        *default-returnspec*)
       ((cons varname options) x)
       ((unless (symbolp varname))
        (er hard? 'parse-returnspec
            "Error in ~x0: return specifiers must start with a symbol name, ~
             so this return specifier is not valid: ~x1" fnname x)
        *default-returnspec*)
       ((when (eq varname 'mv))
        (er hard? 'parse-returnspec
            "Error in ~x0: return values may not be named MV." fnname)
        *default-returnspec*)

       ((mv kwd-alist other-opts)
        ;; bozo better context for error message here would be good
        (extract-keywords fnname '(:hyp :hints :rule-classes) options nil))
       (hyp (if (assoc :hyp kwd-alist)
                (cdr (assoc :hyp kwd-alist))
              t))
       (hints (if (assoc :hints kwd-alist)
                (cdr (assoc :hints kwd-alist))
              nil))
       (rule-classes (if (assoc :rule-classes kwd-alist)
                         (cdr (assoc :rule-classes kwd-alist))
                       :rewrite))
       ((mv terms docs)
        (parse-returnspec-items fnname varname other-opts nil nil))
       (return-type
        (cond ((atom terms) ;; no return-type terms, fine, default is t
               t)
              ((atom (cdr terms))
               (car terms))
              (t
               (er hard? 'parse-returnspec
                   "Error in ~x0: return specifier ~x1 has multiple return ~
                    type terms, but at most one is allowed: ~&2"
                   fnname varname terms))))
       (xdoc
        (cond ((atom docs) ;; no documentation, go figure, default is ""
               "")
              ((atom (cdr docs))
               (car docs))
              (t
               (progn$
                (er hard? 'parse-returnspec
                    "Error in ~x0: return specifier ~x1 has multiple xdoc ~
                     strings, but at most one is allowed: ~x2."
                    fnname varname terms)
                "")))))
    (make-returnspec :name varname
                      :doc xdoc
                      :return-type return-type
                      :rule-classes rule-classes
                      :hyp hyp
                      :hints hints)))

(defthm returnspec-p-of-parse-returnspec
  (returnspec-p (parse-returnspec fnname x world))
  :hints(("Goal" :in-theory (enable parse-returnspec))))

(defund parse-returnspecs-aux (fnname x world)
  ;; Assumes they've already been normalized...
  (declare (xargs :guard (plist-worldp world)))
  (if (atom x)
      nil
    (cons (parse-returnspec fnname (car x) world)
          (parse-returnspecs-aux fnname (cdr x) world))))

(defthm returnspeclist-p-of-parse-returnspecs-aux
  (returnspeclist-p (parse-returnspecs-aux fnname x world))
  :hints(("Goal" :in-theory (enable parse-returnspecs-aux))))

(defund normalize-returnspecs (fnname x)
  ;; We support two forms of returns:
  ;;  :returns return-spec
  ;;  :returns (mv return-spec ... return-spec)
  ;; We require that names are never MV, so we can just check for MV to
  ;; tell thich kind of return spec we are dealing with.
  ;; This function just converts either form into a list of return specs
  ;; with no MV part.
  (declare (xargs :guard t))
  (cond ((not x)
         ;; Fine, no return spec
         nil)
        ((eq x 'mv)
         (er hard? 'normalize-returnspecs
             "Error in ~x0: :returns may not be just MV." fnname))
        ((symbolp x)
         ;; Fine
         (list x))
        ((atom x)
         (er hard? 'normalize-returnspecs
             "Error in ~x0: :returns may not be ~x1."
             fnname x))
        ((eq (car x) 'mv)
         (if (true-listp (cdr x))
             (cdr x)
           (er hard? 'normalize-returnspecs
               "Error in ~x0: :returns must be nil-terminated."
               fnname x)))
        (t
         (list x))))

(defund parse-returnspecs (fnname x world)
  (declare (xargs :guard (plist-worldp world)))
  (parse-returnspecs-aux fnname
                         (normalize-returnspecs fnname x)
                         world))

(defthm returnspeclist-p-of-parse-returnspecs
  (returnspeclist-p (parse-returnspecs fnname x world))
  :hints(("Goal" :in-theory (enable parse-returnspecs))))

(defsection untranslate-and

  (defund untranslate-and (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           ;; (and x) --> x
           (list x))
          ((and (consp x)
                (eq (first x) 'if)
                (equal (len x) 4)
                (equal (fourth x) ''nil))
           ;; (and x y ...) --> (if x (and y ...) nil)
           (cons (second x)
                 (untranslate-and (third x))))
          (t
           (list x))))

  (local
   (progn
     (assert! (equal (untranslate-and 'x) '(x)))
     (assert! (equal (untranslate-and 't) '(t)))
     (assert! (equal (untranslate-and '(if x y z)) '((if x y z))))
     (assert! (equal (untranslate-and '(if x y 'nil)) '(x y)))
     (assert! (equal (untranslate-and '(if x (if a b c) 'nil)) '(x (if a b c))))
     (assert! (equal (untranslate-and '(if x (if a b 'nil) 'nil)) '(x a b))))))

(defund force-each (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons `(force ,(car x))
          (force-each (cdr x)))))

(defund fancy-force-hyp (x)
  (declare (xargs :guard t))
  (b* ((hyp-list (untranslate-and x)))
    (cons 'and (force-each hyp-list))))

(defund fancy-hyp (x)
  (declare (xargs :guard t))
  (b* ((hyp-list (untranslate-and x)))
    (cons 'and hyp-list)))

(defund returnspec-single-thm (fnname x world)
  "Returns EVENTS"
  ;; Only valid to call AFTER the function has been submitted, because we look
  ;; up the guard/formals from the world.
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspec-p x)
                              (plist-worldp world))))
  (b* (((returnspec x) x)
       ((when (equal x.return-type t))
        nil)
       (formals (look-up-formals fnname world))
       (hyp     (cond ((eq x.hyp :guard)
                       (fancy-hyp (look-up-guard fnname world)))
                      ((eq x.hyp :fguard)
                       (fancy-force-hyp (look-up-guard fnname world)))
                      (t
                       x.hyp)))
       (hints x.hints)
       (concl   `(let ((,x.name (,fnname . ,formals)))
                   ,x.return-type))
       (formula (if (eq hyp t)
                    concl
                  `(implies ,hyp ,concl))))
    `((defthm ,(intern-in-package-of-symbol
                (concatenate 'string "RETURN-TYPE-OF-" (symbol-name fnname))
                fnname)
        ,formula
        :hints ,hints
        :rule-classes ,x.rule-classes))))

(defund returnspec-multi-thm (fnname binds x world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspec-p x)
                              (plist-worldp world))))
  (b* (((returnspec x) x)
       ((when (equal x.return-type t))
        nil)
       (hyp (cond
             ((eq x.hyp :guard) (fancy-hyp (look-up-guard fnname world)))
             ((eq x.hyp :fguard) (fancy-force-hyp (look-up-guard fnname world)))
             (t x.hyp)))

       (hints x.hints)
       (concl `(b* (,binds)
                 ,x.return-type))
       (formula (if (eq hyp t)
                    concl
                  `(implies ,hyp ,concl))))
    `((defthm ,(intern-in-package-of-symbol
                (concatenate 'string "RETURN-TYPE-OF-" (symbol-name fnname)
                             "." (symbol-name x.name))
                fnname)
        ,formula
        :hints ,hints
        :rule-classes ,x.rule-classes))))

(defund returnspec-multi-thms (fnname binds x world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspeclist-p x)
                              (plist-worldp world))))
  (if (atom x)
      nil
    (append (returnspec-multi-thm fnname binds (car x) world)
            (returnspec-multi-thms fnname binds (cdr x) world))))

(defprojection returnspeclist->names (x)
  (returnspec->name x)
  :guard (returnspeclist-p x)
  :result-type symbol-listp
  :optimize nil)

(defund make-symbol-ignorable (x)
  (declare (xargs :guard (symbolp x)))
  (intern-in-package-of-symbol
   (concatenate 'string "?" (symbol-name x))
   x))

(defprojection make-symbols-ignorable (x)
  (make-symbol-ignorable x)
  :guard (symbol-listp x)
  :optimize nil)

(defun returnspec-thms (fnname specs world)
  "Returns EVENTS"
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspeclist-p specs)
                              (plist-worldp world))))
  (b* (((unless specs)
        nil)
       ((when (equal (len specs) 1))
        (returnspec-single-thm fnname (car specs) world))
       (names   (returnspeclist->names specs))
       (ignorable-names (make-symbols-ignorable names))
       (formals (look-up-formals fnname world))
       (binds   `((mv . ,ignorable-names) (,fnname . ,formals))))
    (returnspec-multi-thms fnname binds specs world)))


; -------------- Main Stuff Parsing -------------------------------------------

(defund split-/// (fnname x)
  "Returns (mv main-stuff rest-events)"
  (declare (xargs :guard t))
  (b* (((when (not x))
        (mv nil nil))
       ((when (atom x))
        (er hard? 'split-///
            "Expected arguments to (~x0 ~x1 ...) to be nil-terminated, but ~
             found ~x2." 'define fnname x)
        (mv nil nil))
       ((when (eq (car x) '///))
        (mv nil (cdr x)))
       ((mv main-stuff rest-events)
        (split-/// fnname (cdr x))))
    (mv (cons (car x) main-stuff) rest-events)))

(defthm true-listp-of-split-///-0
  (true-listp (mv-nth 0 (split-/// fnname x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable split-///))))

(defthm true-listp-of-split-///-1
  (implies (true-listp x)
           (true-listp (mv-nth 1 (split-/// fnname x))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable split-///))))

(defund get-xargs-from-kwd-alist (kwd-alist)
  "Returns (mv xarg-stuff rest-of-kwd-alist)"
  (declare (xargs :guard (alistp kwd-alist)))
  (b* (((when (atom kwd-alist))
        (mv nil nil))
       ((cons (cons key1 val1) rest) kwd-alist)
       ((mv xarg-stuff kwd-alist)
        (get-xargs-from-kwd-alist rest))
       ((when (member key1 acl2::*xargs-keywords*))
        (mv (list* key1 val1 xarg-stuff) kwd-alist)))
    (mv xarg-stuff (acons key1 val1 kwd-alist))))

(defthm alistp-of-get-xargs-from-kwd-alist
  (implies (force (alistp kwd-alist))
           (b* (((mv ?xarg-stuff kwd-alist)
                 (get-xargs-from-kwd-alist kwd-alist)))
             (alistp kwd-alist)))
  :hints(("Goal" :in-theory (enable get-xargs-from-kwd-alist))))


(defund get-before-events-from-kwd-alist (kwd-alist)
  "Returns (mv events rest-of-kwd-alist)"
  (declare (xargs :guard (alistp kwd-alist)))
  (b* (((when (atom kwd-alist))
        (mv nil nil))
       ((cons (cons key1 val1) rest) kwd-alist)
       ((mv events kwd-alist)
        (get-before-events-from-kwd-alist rest))
       ((when (eq key1 :ignore-ok))
        (mv (cons `(set-ignore-ok ,val1) events) kwd-alist))
       ((when (eq key1 :irrelevant-formals-ok))
        (mv (cons `(set-irrelevant-formals-ok ,val1) events) kwd-alist)))
    (mv events (acons key1 val1 kwd-alist))))

(defthm true-listp-of-get-before-events-from-kwd-alist
  (true-listp (mv-nth 0 (get-before-events-from-kwd-alist kwd-alist)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable get-before-events-from-kwd-alist))))

(defthm alistp-of-get-before-events-from-kwd-alist
  (implies (force (alistp kwd-alist))
           (b* (((mv ?xarg-stuff kwd-alist)
                 (get-before-events-from-kwd-alist kwd-alist)))
             (alistp kwd-alist)))
  :hints(("Goal" :in-theory (enable get-before-events-from-kwd-alist))))


(defund get-xdoc-stuff (kwd-alist)
  "Returns (mv parents short long rest-of-kwd-alist)"
  (declare (xargs :guard (alistp kwd-alist)))
  (b* ((parents (cdr (assoc :parents kwd-alist)))
       (short   (cdr (assoc :short kwd-alist)))
       (long    (cdr (assoc :long kwd-alist)))
       (kwd-alist (delete-assoc :parents kwd-alist))
       (kwd-alist (delete-assoc :short kwd-alist))
       (kwd-alist (delete-assoc :long kwd-alist)))
    (mv parents short long kwd-alist)))

(defthm alistp-of-get-xdoc-stuff
  (implies (force (alistp kwd-alist))
           (b* (((mv ?parents ?short ?long kwd-alist)
                 (get-xdoc-stuff kwd-alist)))
             (alistp kwd-alist)))
  :hints(("Goal" :in-theory (enable get-xdoc-stuff))))

(defund get-defun-params (kwd-alist)
  "Returns (mv enabled-p inline-p prepwork rest-of-kwd-alist)"
  (declare (xargs :guard (alistp kwd-alist)))
  (b* ((enabled-p (cdr (assoc :enabled kwd-alist)))
       (inline-p  (cdr (assoc :inline kwd-alist)))
       (prepwork  (cdr (assoc :prepwork kwd-alist)))
       (kwd-alist (delete-assoc :enabled kwd-alist))
       (kwd-alist (delete-assoc :inline kwd-alist))
       (kwd-alist (delete-assoc :prepwork kwd-alist)))
    (mv enabled-p inline-p prepwork kwd-alist)))

(defthm alistp-of-get-defun-params
  (implies (force (alistp kwd-alist))
           (b* (((mv ?enabled-p ?inline-p ?prepwork kwd-alist)
                 (get-defun-params kwd-alist)))
             (alistp kwd-alist)))
  :hints(("Goal" :in-theory (enable get-defun-params))))

(defund get-assertion (kwd-alist)
  "Returns (mv assertion rest-of-kwd-alist)"
  (declare (xargs :guard (alistp kwd-alist)))
  (b* ((assertion (cdr (assoc :assert kwd-alist)))
       (assertion (if (and (atom assertion) (not (null assertion)))
                      (list assertion)
                    assertion))
       (kwd-alist (delete-assoc :assert kwd-alist)))
    (mv assertion kwd-alist)))

(defthm alistp-of-get-assertion
  (implies (force (alistp kwd-alist))
           (b* (((mv ?assertion kwd-alist)
                 (get-assertion kwd-alist)))
             (alistp kwd-alist)))
  :hints(("Goal" :in-theory (enable get-assertion))))

(defund get-returns (kwd-alist)
  "Returns (mv returns rest-of-kwd-alist)"
  (declare (xargs :guard (alistp kwd-alist)))
  (b* ((returns   (cdr (assoc :returns kwd-alist)))
       (kwd-alist (delete-assoc :returns kwd-alist)))
    (mv returns kwd-alist)))

(defthm alistp-of-get-returns
  (implies (force (alistp kwd-alist))
           (b* (((mv ?returns kwd-alist)
                 (get-returns kwd-alist)))
             (alistp kwd-alist)))
  :hints(("Goal" :in-theory (enable get-returns))))

(defconst *define-keywords*
  (append '(:ignore-ok
            :irrelevant-formals-ok
            :parents
            :short
            :long
            :inline
            :enabled
            :returns
            :assert
            :prepwork
            )
          acl2::*xargs-keywords*))



; -------------- XDOC Signatures ----------------------------------------------

; The idea here is to write out a signature that shows the names of the formals
; and return values, and then provides the documentation for any documented
; formals/returns.
;
; The formals always have names, but the return values will only have names if
; someone has named them with :returns.  If we don't have return-value names,
; we can at least look up the stobjs-out property and see how many return
; values there are, and if any of them are stobj names they'll have names.
; This will also let us double-check the return value arities.

(defund nils-to-stars (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((eq (car x) nil)
         (cons '* (nils-to-stars (cdr x))))
        (t
         (cons (car x) (nils-to-stars (cdr x))))))

(defthm symbol-listp-of-nils-to-stars
  (implies (symbol-listp x)
           (symbol-listp (nils-to-stars x)))
  :hints(("Goal" :in-theory (enable nils-to-stars))))

(defund return-value-names (fnname returnspecs world)
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspeclist-p returnspecs)
                              (plist-worldp world))))
  (b* ((stobjs-out (look-up-return-vals fnname world))
       ((when (atom returnspecs))
        ;; Fine, the user just didn't name/document the return values...
        (nils-to-stars stobjs-out))
       ((unless (equal (len stobjs-out) (len returnspecs)))
        (er hard? 'return-value-names
            "Error in ~x0: ACL2 thinks this function has ~x0 return ~
             values, but :returns has ~x1 entries!"
            (len stobjs-out)
            (len returnspecs))))
    ;; Else the user documented things, so everything has a name and we should
    ;; be just fine.
    (returnspeclist->names returnspecs)))

(defun make-xdoc-signature
  (wrapper            ; name of wrapper function, a symbol
   return-value-names ; names of return values, a symbol list
   base-pkg           ; base package for printing
   acc                ; accumulator for chars in reverse order
   state)
  "Returns (mv acc state)"
  (declare (xargs :mode :program))
  (b* ((args (look-up-wrapper-args wrapper (w state)))
       (call-sexpr (cons wrapper args))
       (ret-sexpr (cond ((atom return-value-names)
                         (er hard? 'make-xdoc-signature
                             "Expected at least one return value name."))
                        ((atom (cdr return-value-names))
                         ;; Just one return value, don't do any MV stuff.
                         (car return-value-names))
                        (t
                         (cons 'mv return-value-names))))

       ((mv call-str state) (xdoc::fmt-to-str call-sexpr base-pkg state))
       ((mv ret-str state)  (xdoc::fmt-to-str ret-sexpr base-pkg state))
       (call-len (length call-str)) ;; sensible since not yet encoded
       (ret-len  (length ret-str))  ;; sensible since not yet encoded
       (acc (str::revappend-chars "<box><p><b>Signature:</b>" acc))
       (acc (if (< (+ call-len ret-len) 60)
                ;; Short signature, so put it all on the same line.  I'm still
                ;; going to use <code> instead of <tt>, for consistency.
                (b* ((acc (str::revappend-chars "<code>" acc))
                     (acc (xdoc::simple-html-encode-str call-str 0 call-len acc))
                     (acc (str::revappend-chars " &rarr; " acc))
                     (acc (xdoc::simple-html-encode-str ret-str 0 ret-len acc))
                     (acc (str::revappend-chars "</code>" acc)))
                  acc)
              ;; Long signature, so split it across lines.  Using <code> here
              ;; means it's basically okay if there are line breaks in call-str
              ;; or ret-str.
              (b* ((acc (str::revappend-chars "<code>" acc))
                   (acc (xdoc::simple-html-encode-str call-str 0 call-len acc))
                   (acc (cons #\Newline acc))
                   (acc (str::revappend-chars "  &rarr;" acc))
                   (acc (cons #\Newline acc))
                   (acc (xdoc::simple-html-encode-str ret-str 0 ret-len acc))
                   (acc (str::revappend-chars "</code>" acc)))
                acc)))
       (acc (str::revappend-chars "</p></box>" acc)))
    (mv acc state)))

(defsection ends-with-period-p

  (defun ends-with-period-p (x)
    (let ((xl (length x)))
      (and (> xl 0)
           (eql (char x (- (length x) 1)) #\.))))

  (local
   (progn
    (assert! (not (ends-with-period-p "")))
    (assert! (not (ends-with-period-p "foo")))
    (assert! (ends-with-period-p "foo.")))))

(defund formal-can-generate-doc-p (x)
  (declare (xargs :guard (formal-p x)))
  (b* (((formal x) x))
    (or (not (equal x.doc ""))
        (not (eq x.guard t)))))

(defund formals-can-generate-doc-p (x)
  (declare (xargs :guard (formallist-p x)))
  (if (atom x)
      nil
    (or (formal-can-generate-doc-p (car x))
        (formals-can-generate-doc-p (cdr x)))))

(defun doc-from-formal (x acc base-pkg state)
  (declare (xargs :guard (formal-p x)
                  :mode :program))
  (b* (((formal x) x)

       ((unless (formal-can-generate-doc-p x))
        (mv acc state))

       (acc (str::revappend-chars "<dd>" acc))
       ((mv name-str state) (xdoc::fmt-to-str x.name base-pkg state))
       (acc (str::revappend-chars "<tt>" acc))
       (acc (xdoc::simple-html-encode-str name-str 0 (length name-str) acc))
       (acc (str::revappend-chars "</tt>" acc))

       (acc (if (equal x.doc "")
                acc
              (b* ((acc (str::revappend-chars " &mdash; " acc))
                   (acc (str::revappend-chars x.doc acc))
                   (acc (if (ends-with-period-p x.doc)
                            acc
                          (cons #\. acc))))
                acc)))

       ((when (eq x.guard t))
        (b* ((acc (str::revappend-chars "</dd>" acc)))
          (mv acc state)))

       ((mv guard-str state) (xdoc::fmt-to-str x.guard base-pkg state))
       ;; Using @('...') here isn't necessarily correct.  If the sexpr has
       ;; something in it that can lead to '), we are hosed.  BOZO eventually
       ;; check for this and make sure we use <code> tags instead, if it
       ;; happens.
       (acc (str::revappend-chars " Guard @('" acc))
       (acc (str::revappend-chars guard-str acc))
       (acc (str::revappend-chars "').</dd>" acc)))
    (mv acc state)))

(defun doc-from-formals-aux (x acc base-pkg state)
  (declare (xargs :guard (formallist-p x)
                  :mode :program))
  (b* (((when (atom x))
        (mv acc state))
       ((mv acc state)
        (doc-from-formal (car x) acc base-pkg state)))
    (doc-from-formals-aux (cdr x) acc base-pkg state)))

(defun doc-from-formals (x acc base-pkg state)
  (declare (xargs :guard (formallist-p x)
                  :mode :program))
  (b* (((unless (formals-can-generate-doc-p x))
        (mv acc state))
       (acc (str::revappend-chars "<dl><dt>Inputs</dt>" acc))
       ((mv acc state) (doc-from-formals-aux x acc base-pkg state))
       (acc (str::revappend-chars "</dl>" acc)))
    (mv acc state)))

(defun make-xdoc-top (wrapper fnname formals returnspecs base-pkg state)
  "Returns (mv str state)"
  (declare (xargs :mode :program))
  (b* ((world (w state))
       (acc nil)
       (return-value-names (return-value-names fnname returnspecs world))
       ((mv acc state)
        (make-xdoc-signature wrapper return-value-names base-pkg acc state))
       ((mv acc state)
        (doc-from-formals formals acc base-pkg state))
       (str (reverse (coerce acc 'string))))
    (mv str state)))



; -------------- Top-Level Macro ----------------------------------------------

(defund define-fn (fnname formals args world)
  (declare (xargs :guard (plist-worldp world)))
  (b* (((unless (symbolp fnname))
        (er hard? 'define-fn
            "Expected function names to be symbols, but found ~x0."
            fnname))

       ((mv main-stuff rest-events) (split-/// fnname args))
       ((mv kwd-alist normal-defun-stuff)
        (extract-keywords fnname *define-keywords* main-stuff nil))
       (traditional-decls/docs (butlast normal-defun-stuff 1))
       (body          (car (last normal-defun-stuff)))

;; I originally generated __function__ in a package based on the function name.
;; The goal was to make it easy to use __function__ in other packages without
;; having to remember to import it, etc.  But then, when I added raise, I
;; realized how inconvenient this is.  You can't write something like raise
;; unless you know which package __function__ will live in.  So, now, just
;; always target cutil::__function__ which is the same as acl2::__function__
;; and can be imported as desired.

       (extended-body `(let ((__function__ ',fnname))
                         ;; CCL's compiler seems to be smart enough to not
                         ;; generate code for this binding when it's not
                         ;; needed.
                         (declare (ignorable __function__))
                         ,body))

       ((mv xargs kwd-alist)              (get-xargs-from-kwd-alist kwd-alist))
       ((mv returns kwd-alist)            (get-returns kwd-alist))
       ((mv before-events kwd-alist)      (get-before-events-from-kwd-alist kwd-alist))
       ((mv parents short long kwd-alist) (get-xdoc-stuff kwd-alist))
       ((mv enabled-p inline-p prepwork kwd-alist)
        (get-defun-params kwd-alist))
       ((mv assertion kwd-alist)          (get-assertion kwd-alist))
       ((unless (symbol-listp assertion))
        (er hard? 'define-fn
            "Error in ~x0: expected :assert to be either a symbol or a ~
             symbol-listp, but found ~x1."
            fnname assertion)) 
       (ruler-extenders (if assertion :all nil))       

       ((unless (true-listp prepwork))
        (er hard? 'define-fn
            "Error in ~x0: expected :prepwork to be a true-listp, but found ~x1."
            fnname prepwork))

       ((when kwd-alist)
        (er hard? 'define-fn
            "Error in ~x0: expected all keywords to be accounted for, but ~
             still have ~x1 after extracting everything we know about."
            fnname (strip-cars kwd-alist)))

       (need-macrop   (or inline-p (has-macro-args formals)))
       (fnname-fn     (cond (inline-p
                             (intern-in-package-of-symbol
                              (concatenate 'string (symbol-name fnname) "$INLINE")
                              fnname))
                            (need-macrop
                             (intern-in-package-of-symbol
                              (concatenate 'string (symbol-name fnname) "-FN")
                              fnname))
                            (t
                             fnname)))

       (macro         (and need-macrop
                           (make-wrapper-macro fnname fnname-fn formals)))
       (formals       (remove-macro-args fnname formals nil))
       (formals       (parse-formals fnname formals))
       (formal-names  (formallist->names formals))
       (formal-guards (remove t (formallist->guards formals)))
       (stobj-names   (formallist->names (formallist-collect-stobjs formals world)))

       (assert-mv-let-bindings assertion)
       (assert-tests (parse-assert-tests assertion fnname-fn))

       (returnspecs   (parse-returnspecs fnname returns world))
       (defun-sym     (if enabled-p 'defun 'defund))

       (main-def
        `(,defun-sym ,fnname-fn ,formal-names
           ,@(cond ((atom formal-guards)
                    ;; Design decision: I prefer to put in a declaration here
                    ;; instead of leaving it out.  This makes define trigger
                    ;; guard verification even with eagerness 1.  I think I
                    ;; much more frequently have guards of T than want to not
                    ;; verify guards.
                    `((declare (xargs :guard t))))
                   ((atom (cdr formal-guards))
                    `((declare (xargs :guard ,(car formal-guards)))))
                   (t
                    `((declare (xargs :guard (and . ,formal-guards))))))
           ,@(and stobj-names `((declare (xargs :stobjs ,stobj-names))))
           ,@(and xargs       `((declare (xargs . ,xargs))))

;; Bozo (that only applies in the :assert case), we should merge the
;; ruler-extenders or figure out a way to do the assertions without them.

           ,@(and ruler-extenders `((declare (xargs :ruler-extenders
                                                    ,ruler-extenders))))
           ,@traditional-decls/docs
           ,(if assertion
                `(mv?-let ,assert-mv-let-bindings
                          ,extended-body
                          (prog2$ (and ,@assert-tests)
                                  (mv? ,@assert-mv-let-bindings)))
                extended-body))))

    `(progn
       (defsection ,fnname
         ,@(and parents `(:parents ,parents))
         ,@(and short   `(:short ,short))
         ,@(and long    `(:long ,long))

         ;; Define the macro first, so that it can be used in recursive calls,
         ;; e.g., to take advantage of nicer optional/keyword args.
         ,@(and need-macrop `(,macro))

         ,@prepwork

         ,@(if before-events
               `((encapsulate ()
                   ,@before-events
                   ,main-def))
             `(,main-def))

         ,@(and need-macrop `((add-macro-alias ,fnname ,fnname-fn)
                              (table define-macro-fns ',fnname-fn ',fnname)))

         (local (in-theory (enable ,fnname)))

         (make-event
          (let* ((world (w state))
                 (events (returnspec-thms ',fnname-fn ',returnspecs world)))
            (value `(progn . ,events))))

         . ,rest-events)

       ;; Now that the section has been submitted, its xdoc exists, so we can
       ;; do the doc generation and prepend it to the xdoc.
       ,(if (not (or parents long short))
            '(value-triple :invisible)
          `(make-event
            (b* ((current-pkg (acl2::f-get-global 'acl2::current-package state))
                 (base-pkg    (pkg-witness current-pkg))
                 (fnname      ',fnname)
                 ((mv str state)
                  (make-xdoc-top fnname ',fnname-fn
                                 ',formals ',returnspecs
                                 base-pkg state))
                 (event (list 'xdoc::xdoc-prepend fnname str)))
              (value event))))
       )))

(defmacro define (name formals &rest args)
  `(make-event (b* ((world (w state))
                    (event (define-fn ',name ',formals ',args world)))
                 (value event))))

#!ACL2
(progn
  ;; Returns (mv successp arglist).
  ;; If DEFINE has created a macro wrapper for a function, which may have
  ;; optional or keyword args, we'd terms involving the function to untranslate
  ;; to a correct call of the macro.  This tries to do that.  Args are the
  ;; arguments provided to the function, macro-args is the lambda-list of the
  ;; macro.
  (defun untrans-macro-args (args macro-args opt/key)
    (cond ((endp macro-args)
           (mv (endp args) nil))
          ((endp args) (mv nil nil))
          ((member-eq (car args) '(&whole &body &rest &allow-other-keys))
           ;; unsupported macro arg type
           (mv nil nil))
          ((member (car macro-args) '(&key &optional))
           (untrans-macro-args args (cdr macro-args) (car macro-args)))
          ((not opt/key)
           ;; just variables, no default
           (mv-let (ok rest)
             (untrans-macro-args (cdr args) (cdr macro-args) opt/key)
             (if ok
                 (mv t (cons (car args) rest))
               (mv nil nil))))
          (t (let* ((default (and (< 1 (len (car macro-args)))
                                  ;; unquote of the second element
                                  (cadr (cadr (car macro-args)))))
                    (key (and (eq opt/key '&key)
                              (cond ((symbolp (car macro-args))
                                     (intern (symbol-name (car macro-args)) "KEYWORD"))
                                    ((symbolp (caar macro-args))
                                     (intern (symbol-name (car macro-args)) "KEYWORD"))
                                    (t (caaar macro-args)))))
                    (presentp (< 2 (len (car macro-args)))))
               (if (and (not (equal (car args) default))
                        presentp
                        (not (cadr args)))
                   ;; Looks like presentp is nil but the value is not the
                   ;; default, so things must not be of the expected form.
                   (mv nil nil)
                 (mv-let (ok rest)
                   (untrans-macro-args
                    (if presentp (cddr args) (cdr args))
                    (cdr macro-args) opt/key)
                   (if (not ok)
                       (mv nil nil)
                     (let ((args-out
                            (cond ((and (or (eq opt/key '&key) (not rest))
                                        (equal default (car args))
                                        (or (not presentp)
                                            (not (cadr args))))
                                   ;; default value and not supposed to be present, leave out
                                   rest)
                                  (key (list* key (car args) rest))
                                  (t (cons (car args) rest)))))
                       (mv t args-out)))))))))


  (defun untranslate-preproc-for-define (term world)
    (and (consp term)
         (not (eq (car term) 'quote))
         (symbolp (car term))
         (let* ((macro (cdr (assoc (car term) (table-alist 'define-macro-fns world)))))
           (and macro
                (let ((macro-args
                       (getprop macro 'macro-args nil
                                'current-acl2-world world)))
                  (and macro-args
                       (mv-let (ok newargs)
                         (untrans-macro-args (cdr term) macro-args nil)
                         (and ok
                              (cons macro newargs)))))))))


  (table user-defined-functions-table
         'untranslate-preprocess
         'untranslate-preproc-for-define))


(defsection raise
  :parents (define)
  :short "Shorthand for causing hard errors, for use in @(see define)."

  :long "<p>@(call raise) is a macro that is equivalent to @('(er hard? ...)'),
but it automatically fills in the function name using @('__function__').  So,
rather than write something like:</p>

@({
 (er hard? __function__ \"bad input value ~x0~%\" x)
})

<p>You can just write:</p>

@({
 (raise \"bad input value ~x0~%\" x)
})

<p>Logically @('raise') just returns @('nil').</p>

@(def raise)"

  (defmacro raise (&rest args)
    `(er hard? __function__ . ,args)))

