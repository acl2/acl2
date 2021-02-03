; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
; Contributing author: Alessandro Coglio <coglio@kestrel.edu>
;
; Additional Copyright Notice.
;
; This file is adapted from the Milawa Theorem Prover, Copyright (C) 2005-2009
; Kookamara LLC, which is also available under an MIT/X11 style license.

(in-package "STD")
(include-book "define")
(include-book "maybe-defthm")
(include-book "std/lists/abstract" :dir :system)
(set-state-ok t)

(defxdoc deflist
  :parents (std/util)
  :short "Introduce a recognizer for a typed list."

  :long "<p>Deflist lets you to quickly introduce recognizers for typed lists
like @(see nat-listp).  It defines the new recognizer function, sets up a basic
theory with rules about @(see len), @(see append), @(see member), etc., and
generates basic, automatic @(see xdoc) documentation.</p>

<h4>General Form</h4>

@({
 (deflist name formals
   element
   [keyword options]
   [/// other events]
   )

 Options                  Defaults
   :negatedp                nil
   :true-listp              nil
   :elementp-of-nil         :unknown
   :guard                   t
   :verify-guards           t
   :guard-hints             nil
   :guard-debug             nil
   :non-emptyp              nil
   :mode                    current defun-mode
   :cheap                   nil
   :verbosep                nil
   :parents                 nil
   :short                   nil
   :long                    nil
   :prepwork                nil
})

<h4>Basic Examples</h4>

<p>The following introduces a new function, @('my-integer-listp'), which
recognizes lists whose every element satisfies @('integerp'), and also
introduces many theorems about this new function.</p>

@({
 (deflist my-integer-listp (x)
   (integerp x))
})

<p><b><color rgb='#ff0000'>Note</color></b>: @('x') is treated in a special
way.  It refers to the whole list in formals and guards, but refers to
individual elements of the list in the @('element') portion.  This is similar
to how other macros like @(see defalist), @(see defprojection), and @(see
defmapappend) handle @('x').</p>

<p>Here is a recognizer for lists with no natural numbers:</p>

@({
 (deflist nat-free-listp (x)
   (natp x)
   :negatedp t)
})

<p>Here is a recognizer for lists whose elements must exceed some minimum:</p>

@({
 (deflist all-greaterp (min x)
   (> x min)
   :guard (and (natp min)
               (nat-listp x)))
})

<h3>Usage and Optional Arguments</h3>

<p>Let @('pkg') be the package of @('name').  All functions, theorems, and
variables are created in this package.  One of the formals must be @('pkg::x'),
and this argument represents the list to check.  Otherwise, the only
restriction on the formals is that you may not use the names @('pkg::a'),
@('pkg::n'), or @('pkg::y'), because we use these variables in the theorems we
generate.</p>

<p>The optional @(':negatedp') keyword can be used to recognize a list whose
every element does not satisfy elementp.</p>

<p>The optional @(':true-listp') keyword can be used to require that the new
recognizer is \"strict\" and will only accept lists that are
@('nil')-terminated; by default the recognizer will be \"loose\" and will not
pay attention to the final @('cdr').  There are various reasons to prefer one
behavior or another; see @(see strict-list-recognizers) for details.</p>

<p>The optional @(':elementp-of-nil') keyword can be used when @('(elementp nil
...)') is always known to be @('t') or @('nil').  When it is provided,
@('deflist') can generate slightly better theorems.</p>

<p>The optional @(':guard'), @(':verify-guards'), @(':guard-debug'), and
@(':guard-hints') are options for the @(see defun) we introduce.  These are for
the guards of the new list recognizer, not the element recognizer.</p>

<p>The optional @(':mode') keyword can be set to @(':logic') or @(':program')
to introduce the recognizer in logic or program mode.  The default is whatever
the current default defun-mode is for ACL2, i.e., if you are already in program
mode, it will default to program mode, etc.</p>

<p>The optional @(':verbosep') flag can be set to @('t') if you want deflist to
print everything it's doing.  This may be useful if you run into any failures,
or if you are simply curious about what is being introduced.</p>

<p>The optional @(':cheap') flag can be set to @('t') to produce cheaper, less
effective rule-classes for some rules; this may be convenient when the element
type is a very common function such as @('consp'), in which case adding
stronger rules might significantly slow down proofs.</p>

<p>The optional @(':parents'), @(':short'), and @(':long') keywords are as in
@(see defxdoc).  Typically you only need to specify @(':parents'), perhaps
implicitly with @(see xdoc::set-default-parents), and suitable documentation
will be automatically generated for @(':short') and @(':long').  If you don't
like this documentation, you can supply your own @(':short') and/or @(':long')
to override it.</p>

<p>The optional @(':prepwork') may provide a list of event forms that are
submitted just before the generated events.  These are preparatory events,
e.g. local lemmas to help prove @(':elementp-of-nil').</p>

<h3>Pluggable Architecture</h3>

<p>Beginning in ACL2 6.5, deflist no longer hard-codes the set of theorems to
be produced about every list recognizer.  Instead, @('def-listp-rule') forms
pertaining to a generic list recognizer called @('element-list-p') are used as
templates and instantiated for each deflist invocation.  These forms may be
scattered throughout various libraries, so the set of books you have loaded
determines the set of rules produced by a deflist invocation.  See @(see
acl2::std/lists/abstract) for more information about these rules and how to
control what theorems are produced by deflist.</p>

<p>\"std/util/deflist.lisp\" includes books that compose a set of rules to
instantiate that should be more or less backward compatible with the theorems
produced by deflist in ACL2 6.4 and previous.  \"std/util/deflist-base.lisp\"
includes a much more basic set of rules.</p>

<h3>Support for Other Events</h3>

<p>Deflist implements the same @('///') syntax as other macros like @(see
define).  This allows you to put related events near the definition and have
them included in the automatic documentation.  As with define, the new
recognizer is enabled during the @('///') section.  Here is an example:</p>

@({
 (deflist even-integer-list-p (x)
   (even-integer-p x)
   :true-listp t
   ///
   (defthm integer-listp-when-even-integer-list-p
     (implies (even-integer-list-p x)
              (integer-listp x))))
})

<p>Deprecated.  The optional @(':rest') keyword was a precursor to @('///').
It is still implemented, but its use is now discouraged.  If both @(':rest')
and @('///') events are used, we arbitrarily put the @(':rest') events
first.</p>

<p>Deprecated.  The optional @(':already-definedp') keyword can be set if you
have already defined the function.  This was previously useful when you wanted
to generate the ordinary @('deflist') theorems without generating a @('defund')
event, e.g., because you are dealing with mutually recursive recognizers.  We
still accept this option for backwards compatibility but it is useless, because
@('deflist') is now smart enough to notice that the function is already
defined.</p>")

(defxdoc strict-list-recognizers
  :parents (deflist)
  :short "Should your list recognizers require @('nil')-terminated lists?"

  :long "<p>Here are two ways that you could write a list recognizer:</p>

<p>The \"strict\" way:</p>

@({
   (defun foo-listp (x)
     (if (atom x)
         (not x)
       (and (foop (car x))
            (foo-listp (cdr x)))))
})

<p>The \"loose\" way:</p>

@({
   (defun foo-listp (x)
     (if (atom x)
         t
       (and (foop (car x))
            (foo-listp (cdr x)))))
})

<p>The only difference is that in the base case, the strict recognizer requires
X to be NIL, whereas the loose recognizer allows X to be any atom.</p>

<p>By default, the recognizers introduced by @(see deflist) follow the loose
approach.  You can use the @(':true-listp') option to change this behavior, and
instead introduce a strict recognizer.</p>

<p>Why in the world would we use a loose recognizer?  Well, there are
advantages to either approach.</p>

<p>The strict approach is certainly more clear and less weird.  It is nice that
a strict recognizer always implies @(see true-listp).  And it makes EQUAL more
meaningful when applied to FOO-LISTP objects.</p>

<p>That is, when FOO-LISTP is strict, there is only one FOO-LISTP that has
length 3 and whose first three elements are (A B C).  However, when FOO-LISTP
is loose, there are infinitely many lists like this, and the only difference
between them is their final cdr.</p>

<p>This nicer equality behavior makes the strict approach especially appealing
when you are building new data types that include FOO-LISTP components, and
you'd like to just reuse EQUAL instead of having new equivalence relations for
each structure.</p>

<p>But the loose approach more nicely follows the @(see list-fix) convention:
\"a function that takes a list as an argument should coerce the final-cdr to
NIL, and produce the same result regardless of the final cdr.\" More formally,
you might say that F respects the list-fix convention when you can prove</p>

@({
   (defcong list-equiv equal (f ... x ...) n)
})

<p>Where list-equiv is equality up to the final cdr, e.g.,</p>

@({
   (list-equiv x y) = (equal (list-fix x) (list-fix y))
})

<p>Many functions follow this convention or something similar to it, and
because of this there are sometimes nicer theorems about loose list recognizers
than about strict list recognizers.  For instance, consider @(see append).  In
the loose style, we can prove:</p>

@({
   (equal (foo-listp (append x y))
          (and (foo-listp x)
               (foo-listp y)))
})

<p>In the strict style, we have to prove something uglier, e.g.,</p>

@({
   (equal (foo-listp (append x y))
          (and (foo-listp (list-fix x))
               (foo-listp y)))
})

<p>There are many other nice theorems, but just as a few examples, each of
these theorems are very nice in the loose style, and are uglier in the strict
style:</p>

@({
   (equal (foo-listp (list-fix x))
          (foo-listp x))

   (equal (foo-listp (rev x))
          (foo-listp x))

   (equal (foo-listp (mergesort x))
          (foo-listp x))

   (implies (and (subsetp-equal x y)
                 (foo-listp y))
            (foo-listp x))
})

<p>@(see deflist) originally came out of @(see acl2::milawa), where I
universally applied the loose approach, and in that context I think it is very
nice.  It's not entirely clear that loose recognizers are a good fit for ACL2.
Really one of the main objections to the loose style is: ACL2's built-in list
recognizers use the strict approach, and it can become irritating to keep track
of which recognizers require true-listp and which don't.</p>")





(defconst *deflist-valid-keywords*
  '(:negatedp
    :cheap
    :guard
    :verify-guards
    :guard-debug
    :guard-hints
    :already-definedp
    :elementp-of-nil
    :non-emptyp
    :mode
    :parents
    :short
    :long
    :true-listp
    :rest
    :verbosep
    :prepwork
    ;; Undocumented option for customizing the theory, mainly meant for
    ;; problematic cases, e.g., built-in functions where ACL2 "knows too much"
    :theory-hack))

(program)

(defun deflist-substitution (name formals element kwd-alist x)
  (b* ((negatedp (getarg :negatedp nil kwd-alist))
       (true-listp (getarg :true-listp nil kwd-alist))
       (non-emptyp (getarg :non-emptyp nil kwd-alist)))
    `((acl2::element-p ,(if negatedp
                            `(lambda (,x) (not ,element))
                          `(lambda (,x) ,element)))
      (acl2::non-element-p ,(if negatedp
                                `(lambda (,x) ,element)
                              `(lambda (,x) (not ,element))))
      (,(if non-emptyp
            'acl2::element-list-nonempty-p
          'acl2::element-list-p)
       (lambda (,x) (,name . ,formals)))
      (acl2::element-list-final-cdr-p ,(if true-listp
                                           'not
                                         '(lambda (x) t))))))



(defun atom/quote-listp (x)
  (if (atom x)
      (eq x nil)
    (and (or (atom (car x))
             (eq (caar x) 'quote))
         (atom/quote-listp (cdr x)))))

(defun simple-fncall-p-hack (x)
  ;; Recognizes a function call with variable/quote
  ;; arguments.  Maybe nested function calls could be
  ;; considered simple; anything containing an if shouldn't
  ;; be, though.
  (and (consp x)
       (symbolp (car x))
       (atom/quote-listp (cdr x))))

(defun deflist-requirement-alist (kwd-alist formals element)
  (b* ((negatedp (getarg :negatedp nil kwd-alist))
       (simple (simple-fncall-p-hack element))
       (true-listp (getarg :true-listp nil kwd-alist))
       (elementp-of-nil (getarg :elementp-of-nil :unknown kwd-alist))
       (single-var (eql (len formals) 1))
       (cheap      (getarg :cheap      nil kwd-alist)))
    `((acl2::element-p-of-nil . ,(eq elementp-of-nil (not negatedp)))
      (acl2::not-element-p-of-nil . ,(eq elementp-of-nil negatedp))
      (acl2::negatedp . ,negatedp)
      (acl2::true-listp . ,true-listp)
      (acl2::single-var . ,single-var)
      (acl2::cheap      . ,cheap)
      (acl2::simple     . ,simple))))

(mutual-recursion
 (defun deflist-thmbody-subst (body element name formals x negatedp)
   (if (atom body)
       body
     (case (car body)
       (acl2::element-p
        (let ((call (cons (car element) (subst (cadr body) x (cdr element)))))
          (if negatedp
              (list 'not call)
            call)))
       (acl2::non-element-p
        (let ((call (cons (car element) (subst (cadr body) x (cdr element)))))
          (if negatedp
              call
            (list 'not call))))
       (acl2::element-list-p
        (cons name (subst (cadr body) x formals)))
       (acl2::element-list-nonempty-p
        (cons name (subst (cadr body) x formals)))
       (t (if (symbolp (car body))
              (cons (car body)
                    (deflist-thmbody-list-subst (cdr body) element name formals x negatedp))
            (deflist-thmbody-list-subst body element name formals x negatedp))))))
 (defun deflist-thmbody-list-subst (body element name formals x negatedp)
   (if (atom body)
       body
     (cons (deflist-thmbody-subst (car body) element name formals x negatedp)
           (deflist-thmbody-list-subst (cdr body) element name formals x negatedp)))))


(defun deflist-thmname-subst (thmname listp-name elementp)
  (b* ((thmname (symbol-name thmname))
       (subst-list `(("ELEMENT-LIST-NONEMPTY-P" . ,(symbol-name listp-name))
                     ("ELEMENT-LIST-NONEMPTY" . ,(symbol-name listp-name))
                     ("ELEMENT-LIST-P" . ,(symbol-name listp-name))
                     ("ELEMENT-LIST" . ,(symbol-name listp-name))
                     ("ELEMENT-P" . ,(symbol-name elementp))
                     ("ELEMENT" . ,(symbol-name elementp)))))
    (intern-in-package-of-symbol
     (dumb-str-sublis subst-list thmname)
     listp-name)))


(defun deflist-ruleclasses-subst (rule-classes element name formals x negatedp)
  (b* (((when (atom rule-classes)) rule-classes)
       (class (car rule-classes))
       ((when (atom class))
        (cons class
              (deflist-ruleclasses-subst
                (cdr rule-classes) element name formals x negatedp)))
       (corollary-look (assoc-keyword :corollary class))
       ((unless corollary-look)
        (cons class
              (deflist-ruleclasses-subst
                (cdr rule-classes) element name formals x negatedp)))
       (prefix (take (- (len class) (len corollary-look)) class))
       (corollary-term (deflist-thmbody-subst
                         (cadr corollary-look)
                         element name formals x negatedp)))
    (cons (append prefix `(:corollary ,corollary-term . ,(cddr corollary-look)))
          (deflist-ruleclasses-subst
                (cdr rule-classes) element name formals x negatedp))))

(defun deflist-instantiate (table-entry element name formals kwd-alist x
                                        req-alist fn-subst world)
  (b* (((cons inst-thm alist) table-entry)
       ((when (not alist)) nil)
       (alist (and (not (eq alist t)) alist))
       (req-look (assoc :requirement alist))
       (req-ok (or (not req-look)
                   (generic-eval-requirement (cadr req-look) req-alist)))
       ((unless req-ok) nil)
       (thmname-base (let ((look (assoc :name alist)))
                       (if look (cadr look) inst-thm)))
       (thmname (deflist-thmname-subst thmname-base name (car element)))
       (body (let ((look (assoc :body alist)))
               (if look (cadr look) (fgetprop inst-thm 'acl2::untranslated-theorem nil world))))
       ((when (not body)) (er hard? 'deflist-instantiate
                              "Bad deflist table entry: ~x0~%" inst-thm))
       (rule-classes
        (b* ((cheap-look (and (getarg :cheap nil kwd-alist)
                              (assoc :cheap-rule-classes alist)))
             ((when cheap-look) (cadr cheap-look))
             (look (assoc :rule-classes alist)))
          (if look (cadr look) (fgetprop inst-thm 'acl2::classes nil world))))
       (negatedp (getarg :negatedp nil kwd-alist))
       (rule-classes (deflist-ruleclasses-subst rule-classes element name formals x negatedp)))
    `((defthm ,thmname
        ,(deflist-thmbody-subst body element name formals x negatedp)
        :hints (("goal" :use ((:functional-instance
                               ,inst-thm
                               . ,fn-subst))))
        :rule-classes ,rule-classes))))


(defun deflist-instantiate-table-thms-aux
  (table element name formals kwd-alist x
         req-alist fn-subst world)
  (if (atom table)
      nil
    (append (deflist-instantiate (car table) element name formals kwd-alist x
              req-alist fn-subst world)
            (deflist-instantiate-table-thms-aux (cdr table) element name
              formals kwd-alist x req-alist fn-subst world))))

(defun deflist-instantiate-table-thms (name formals element kwd-alist x world)
  (b* ((non-emptyp (getarg :non-emptyp nil kwd-alist))
       (table
        ;; [Jared] added this reverse because it's nice for documentation for
        ;; the simpler rules (atom, consp, etc.) to show up first.  Since new
        ;; rules just get consed onto the table, if we don't do this reverse
        ;; then the first things you see are rules about revappend, remove,
        ;; last, etc., which are kind of obscure.

        (reverse (table-alist (if non-emptyp 'acl2::nonempty-listp-rules 'acl2::listp-rules) world)))
       (fn-subst (deflist-substitution name formals element kwd-alist x))
       (req-alist (deflist-requirement-alist kwd-alist formals element)))
    (deflist-instantiate-table-thms-aux table element name formals kwd-alist x req-alist fn-subst world)))



(defun deflist-fn (name formals element kwd-alist other-events state)
  (declare (xargs :mode :program))
  (b* ((__function__ 'deflist)
       ; (mksym-package-symbol name)

       ;; Special variables that are reserved by deflist.
       (x (intern-in-package-of-symbol "X" name))
       (a (intern-in-package-of-symbol "A" name))
       (n (intern-in-package-of-symbol "N" name))
       (y (intern-in-package-of-symbol "Y" name))

       ((unless (and (symbol-listp formals)
                     (no-duplicatesp formals)))
        (raise "The formals must be a list of unique symbols, but are ~x0."
               formals))
       ((unless (member x formals))
        (raise "The formals must contain ~x0, but are ~x1.~%" x formals))
       ((unless (and (not (member a formals))
                     (not (member n formals))
                     (not (member y formals))))
        (raise "As a special restriction, formals may not mention ~x0, ~x1, ~
                or ~x2, but the formals are ~x3." a n y formals))
       ((unless (and (consp element)
                     (symbolp (car element))))
        (raise "The element recognizer must be a function applied to the ~
                formals, but is ~x0." element))

       (elementp     (car element))
       (elem-formals (cdr element))

       ;; We previously required the user to tell us if the function was
       ;; already defined.  Now we---you know---actually look to see.  Duh.
       (looks-already-defined-p
        (or (not (eq (getprop name 'acl2::formals :none 'acl2::current-acl2-world
                              (w state))
                     :none))
            (not (eq (getprop name 'acl2::macro-args :none 'acl2::current-acl2-world
                              (w state))
                     :none))))
       (already-definedp (getarg :already-definedp :unknown kwd-alist))
       ((unless (or (eq already-definedp :unknown)
                    (eq already-definedp looks-already-defined-p)))
        (raise "Found :already-definedp ~x0, but ~x1 is ~s2."
               already-definedp name
               (if looks-already-defined-p
                   "already defined."
                 "not defined.")))
       (already-definedp looks-already-defined-p)

       (negatedp         (getarg :negatedp         nil      kwd-alist))
       (true-listp       (getarg :true-listp       nil      kwd-alist))
       (verify-guards    (getarg :verify-guards    t        kwd-alist))
       (guard            (getarg :guard            t        kwd-alist))
       (guard-debug      (getarg :guard-debug      nil      kwd-alist))
       (guard-hints      (getarg :guard-hints      nil      kwd-alist))

       (elementp-of-nil  (getarg :elementp-of-nil  :unknown kwd-alist))
       (short            (getarg :short            nil      kwd-alist))
       (long             (getarg :long             nil      kwd-alist))
       (theory-hack      (getarg :theory-hack      nil      kwd-alist))
       (non-emptyp       (getarg :non-emptyp       nil      kwd-alist))

       (prepwork         (getarg :prepwork         nil      kwd-alist))

       (rest             (append
                          (getarg :rest nil kwd-alist)
                          other-events))

       (mode             (getarg :mode
                                 (default-defun-mode (w state))
                                 kwd-alist))

       (parents-p (assoc :parents kwd-alist))
       (parents   (cdr parents-p))
       (parents   (if parents-p
                      parents
                    (or (xdoc::get-default-parents (w state))
                        '(acl2::undocumented))))

       ((unless (booleanp negatedp))
        (raise ":negatedp must be a boolean, but is ~x0." negatedp))
       ((unless (booleanp true-listp))
        (raise ":true-listp must be a boolean, but is ~x0." true-listp))
       ((unless (booleanp verify-guards))
        (raise ":verify-guards must be a boolean, but is ~x0." verify-guards))
       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (raise ":mode must be one of :logic or :program, but is ~x0." mode))
       ((unless (or (eq mode :logic)
                    (not already-definedp)))
        (raise ":mode :program and already-definedp cannot be used together."))
       ((unless (member elementp-of-nil '(t nil :unknown)))
        (raise ":elementp-of-nil must be t, nil, or :unknown"))

       (short (or short
                  (and parents
                       (concatenate
                        'string "@(call " (xdoc::full-escape-symbol name)
                                 ") recognizes lists where every element "
                                 (if negatedp
                                     "is rejected by "
                                   "satisfies ")
                                 ;; bozo it'd be better to put the formals in
                                 ;; here, for multi-arity functions.
                                 "@(see? " (xdoc::full-escape-symbol elementp) ")."))))

       (long (or long
                 (and parents
                      (if true-listp
                          "<p>This is an ordinary @(see std::deflist).  It is
                           \"strict\" in that it requires @('x') to be a
                           \"properly\" nil-terminated list.</p>"
                        "<p>This is an ordinary @(see std::deflist).  It is
                         \"loose\" in that it does not care whether @('x') is
                         nil-terminated.</p>"))))

       (car-test (if negatedp
                     `(not (,elementp ,@(subst `(car ,x) x elem-formals)))
                   `(,elementp ,@(subst `(car ,x) x elem-formals))))
       (end-test (if true-listp
                     `(null ,x)
                   t))

       (def (if already-definedp
                ;; Stupid hack to allow adding boilerplate documentation to
                ;; already-defined functions.  This isn't quite as good as
                ;; having the documentation as part of the DEFINE because we
                ;; won't get an automatic signature.  But it's better than
                ;; nothing.
                (and
                 ;; If the user has already documented this function, there is
                 ;; no reason to override their docs with something new.  But
                 ;; using find-topic here doesn't fully work.  It works if the
                 ;; previously defined topic is in the certification world when
                 ;; the deflist is generated during certification, but not if
                 ;; it is in the world before the book is included!  So we use
                 ;; the :no-override flag to defxdoc instead.
                 ;; (not (xdoc::find-topic name (xdoc::get-xdoc-table (w state))))

                 ;; If we don't have any actual documentation to add, then
                 ;; leave it alone and don't do anything.
                 (or (and parents-p parents) short long)
                 ;; Otherwise it seems pretty OK to add some docs.
                 `((defxdoc ,name
                     ,@(and (or parents-p parents) `(:parents ,parents))
                     ,@(and short   `(:short ,short))
                     ,@(and long    `(:long ,long))
                     :no-override t)))

              `((define ,name (,@formals)
                  ,@(and (or parents-p parents) `(:parents ,parents))
                  ,@(and short   `(:short ,short))
                  ,@(and long    `(:long ,long))
                  :returns bool
                  :guard ,guard
                  ;; We tell ACL2 not to normalize because otherwise type
                  ;; reasoning can rewrite the definition, and ruin some of our
                  ;; theorems below, e.g., when ELEMENTP is known to always be
                  ;; true.
                  :normalize nil
                  ,@(and (eq mode :logic)
                         `(:verify-guards ,verify-guards
                           :guard-debug   ,guard-debug
                           :guard-hints   ,guard-hints))
                  ,(if non-emptyp
                       `(and (consp ,x)
                             ,car-test
                             (let ((,x (cdr ,x)))
                               (if (consp ,x)
                                   (,name ,@formals)
                                 ,end-test)))
                     `(if (consp ,x)
                          (and ,car-test
                               (,name ,@(subst `(cdr ,x) x formals)))
                        ,end-test))))))

       ((when (eq mode :program))
        `(encapsulate nil
           (program)
           ,@prepwork
           ,@def
           ,@rest))

       (want-doc-p (or short long parents))
       (thms (deflist-instantiate-table-thms name formals element kwd-alist x (w state)))
       (name-basics (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-BASICS")
                     name))
       (thms-section
        ;; Try to avoid introducing a foolist-p-basics section if we aren't generating
        ;; docs or if there's already such a topic defined.
        (if (or (not want-doc-p)
                (and already-definedp
                     (xdoc::find-topic name-basics (xdoc::get-xdoc-table (w state)))))
            `(progn . ,thms)
          `(defsection-progn ,name-basics
             :parents (,name)
             :short ,(concatenate 'string
                                  "Basic theorems about @(see "
                                  (xdoc::full-escape-symbol name)
                                  "), generated by @(see std::deflist).")
             . ,thms)))

       (events
        `((logic)
          ,@prepwork
          (set-inhibit-warnings ;; implicitly local
           "theory" "free" "non-rec" "double-rewrite" "subsume" "disable")

          (value-triple
           (cw "~|~%Deflist: attempting to show, using your current theory, ~
                that ~x0 is always Boolean valued.~%" ',element))

          (with-output
            :stack :pop
            :off (acl2::summary acl2::observation)
            (local (defthm deflist-local-booleanp-element-thm
                     (or (equal ,element t)
                         (equal ,element nil))
                     :rule-classes :type-prescription)))

          ,@(and (not (eq elementp-of-nil  :unknown))
                 `((value-triple
                    (cw "~|~%Deflist: attempting to justify, using your ~
                         current theory, :ELEMENTP-OF-NIL ~x0.~%"
                        ',elementp-of-nil))

                   (with-output
                     :stack :pop
                     :off (acl2::summary)
                     (local (maybe-defthm-as-rewrite
                             deflist-local-elementp-of-nil-thm
                             (equal (,elementp ,@(subst ''nil x elem-formals))
                                    ',elementp-of-nil))))))

          (value-triple
           (cw "~|~%Deflist: introducing ~x0 and proving deflist theorems.~%"
               ',name))

          ,@def

          (local (in-theory (theory 'minimal-theory)))
          (local (in-theory (enable ,name
                                    (:type-prescription ,name)
                                    deflist-local-booleanp-element-thm
                                    )))
          (local (enable-if-theorem deflist-local-elementp-of-nil-thm))
          ,@theory-hack
          ,thms-section)))

    `(progn
       (encapsulate ()
         ;; This encapsulate is necessary to keep all our deflist theory stuff
         ;; bottled up.  It would be nice not to need this since encapsulate is
         ;; slow, but it'd be hard to get it working.
         . ,events)
       ;; Now do the rest of the events with name enabled, so they get included
       ;; in the section
       . ,(and rest
               `((value-triple (cw "Deflist: submitting /// events.~%"))
                 (with-output
                   :stack :pop
                   (defsection user-events
                     ,@(and want-doc-p `(:extension ,name))
                     (local (in-theory (enable ,name)))
                     . ,rest)))))))


(defmacro deflist (name &rest args)
  (b* ((__function__ 'deflist)
       ((unless (symbolp name))
        (raise "Name must be a symbol."))
       (ctx (list 'deflist name))
       ((mv main-stuff other-events) (split-/// ctx args))
       ((mv kwd-alist formals-elem)
        (extract-keywords ctx *deflist-valid-keywords* main-stuff nil))
       ((unless (tuplep 2 formals-elem))
        (raise "Wrong number of arguments to deflist."))
       ((list formals element) formals-elem)
       (verbosep (getarg :verbosep nil kwd-alist)))
    `(with-output
       :stack :push
       ,@(if verbosep
             nil
           '(:gag-mode t :off (acl2::summary
                               acl2::observation
                               acl2::prove
                               acl2::proof-tree
                               acl2::event)))
       (make-event
        `(progn ,(deflist-fn ',name ',formals ',element ',kwd-alist
                   ',other-events state)
                (value-triple '(deflist ,',name)))))))
