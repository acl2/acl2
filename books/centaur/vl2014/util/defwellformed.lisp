; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "defs")
(include-book "warnings")
(include-book "tools/flag" :dir :system)


(defxdoc well-formedness
  :parents (vl2014)
  :short "Sanity checks for the well-formedness of Verilog modules.")

(defxdoc defwellformed
  :parents (well-formedness)

  :short "@('Defwellformed') is a macro for introducing well-formedness
checking functions."

  :long "<h3>Motivation</h3>

<p>Throughout VL, there are many functions that check to see whether some
module element is well-formed.  When we introduce these well-formedness checks,
we often want to have two versions of the check:</p>

<ol>

<li>A <b>vanilla</b> Boolean-valued predicate, @('foo-okp'), that causes no
side effects and is easy to reason about, and</li>

<li>A <b>debugging</b> function, @('foo-okp-warn') that generates useful @(see
warnings) that explain precisely why the object is malformed.  In particular,
@('foo-okp-warn') takes a warnings accumulator as an extra argument, and
returns @('(mv okp warnings')').</li>

</ol>

<p>The value of the debugging function is probably obvious: it allows us to
provide a better explanation for why some module is not being translated.  But
the debugging function is <i>not</i> well-suited for reasoning.  In particular,
in theorems we generally do not care about which warnings have been
accumulated; we only want to know whether some structure is well-formed.  If we
try to use the debugging function directly for this purpose, we might write
theorems such as:</p>

@({
 (implies (and (foo-p x)
               (car (foo-okp-warn x warnings)))
          (consequence x))
})

<p>The problem with such a theorem is that @('warnings') is a free variable,
which can cause problems for ACL2 when it tries to apply the rule.</p>

<p>So, our approach is to introduce <b>both</b> versions of the well-formedness
check, and then add a theorem that shows the first value returned by
@('foo-okp-warn') is exactly the value returned by @('foo-okp').  Accordingly,
we can run @('foo-okp-warn') in our code and get useful warning messages, but
we can always reason about the simpler function @('foo-okp').</p>

<p>Unfortunately, writing two versions of a function comes at its own cost; we
have to duplicate the code, keep both versions in sync, and write these
boilerplate theorems.  The macro @(srclink defwellformed) allows us to automate
this process.</p>

<h3>Using @('defwellformed')</h3>

<p>The @('defwellformed') macro is similar to @('defun').  The general form
is:</p>

@({
 (defwellformed foo-okp (x other-args ...)
   :guard (and (foop x) ...)
   :body [...]
   :extra-decls ((xargs ...))
   :parents ...
   :short ...
   :long ...)
})

<p>Here, @('foo-okp') is the name of the new vanilla function, and @('(x
other-args ...)') are the formals.  The @(':guard') and @(':body') are used in
the @('defun') form we generate, as are any @(':extra-decls') that you need.
Finally, the @('parents'), @('short'), and @('long') fields are as in @(see
defxdoc).</p>

<p>The debugging function is always named by appending @('-warn') to the name
of the vanilla function.  Having such a convention is necessary for our
implementation of @('(@wf-call ...)').</p>

<h5>Meta-macros</h5>

<p>The tricky part to using defwellformed is to write a @(':body') that serves
both as the vanilla definition and as the debugging definition.  To accomplish
this, we make use of certain \"meta-macros\", which can be identifier with the
prefix @('@wf-').</p>

<p>In particular, the bodies of our well-formedness checks generally look
something like this:</p>

@({
 (let ((bar ...)
       (baz ...))
   (@wf-progn
    (@wf-assert condition1 [type msg args])
    (@wf-assert condition2 [type msg args])
    (@wf-note condition type msg args)
    (@wf-call other-wf-check ...)
    ...))
})

<p>These @('@wf-') expressions are only valid in the body of the
@('defwellformed') command, and are given <b>different expansions</b> depending
upon whether we are in the vanilla or debugging version of the function.</p>

<p>In the vanilla function,</p>
<ul>
  <li>@('(@wf-progn ...)') becomes @('(and ...)')</li>
  <li>@('(@wf-and ...)') becomes @('(and ...)')</li>
  <li>@('(@wf-assert condition ...)') becomes @('(if condition t nil)')</li>
  <li>@('(@wf-note condition ...)') becomes @('t')</li>
  <li>@('(@wf-call other-wf-check ...)') becomes @('(other-wf-check ...)')</li>
</ul>

<p>But in the debugging function, a more complex expansion is used.</p>

<dl>
<dt>(@wf-progn ...)</dt>

<dd>This becomes an appropriate @('mv-let') strucutre to handle the return
values from @('@wf-assert') and @('@') commands.  Note that in the debugging
version <b>execution continues</b> after a violation is discovered so that we
uncover as many problems as possible.  This behavior can cause problems for
guard verification: you cannot rely upon the earlier assertions having
\"passed\" in the guards of your later assertions.  Hence the introduction of
@('@wf-and').</dd>

<dt>(@wf-and ...)</dt>

<dd>This becomes an @('mv-let') structure as in @('@wf-progn'), but
<b>execution stops</b> when any assertion is violated.</dd>

<dt>(@wf-assert condition type msg args)</dt>

<dd>If the condition is violated, @('okp') becomes @('nil') and we add
a (non-fatal) warning of the indicated type, message, and arguments.</dd>

<dt>(@wf-note condition type msg args)</dt>

<dd>We add a warning of the indicated type, message, and args, to the list of
warnings, but we do not set @('okp') to @('nil').  That is, this is just a way
to note suspicious things that aren't necessarily outright problems.</dd>

<dt>(@wf-call other-wf-check ...)</dt>

<dd>Becomes @('(other-wf-check-warn ...)').  In other words, this allows you to
call the vanilla version of some subsidiary well-formedness check from the
vanilla version of your function, and the debugging version from your debugging
function.</dd>

</dl>

<p>Note also that @(srclink defwellformed-list) allows you to call a
well-formedness predicate on every element in a list, and that @(srclink
mutual-defwellformed) is a replacement for @('mutual-recursion') that allows
for the mutually-recursive use of @('defwellformed').</p>")

(defmacro @wf-progn (&rest args)
  (declare (ignorable args))
  (er hard? '@wf-progn "@wf-progn used outside of defwellformed!"))

(defmacro @wf-and (&rest args)
  (declare (ignorable args))
  (er hard? '@wf-and "@wf-and used outside of defwellformed!"))

(defmacro @wf-assert (&rest args)
  (declare (ignorable args))
  (er hard? '@wf-assert "@wf-assert used outside of defwellformed!"))

(defmacro @wf-call (&rest args)
  (declare (ignorable args))
  (er hard? '@wf-call "@wf-call used outside of defwellformed!"))

(defund wf-progn-warn-fn (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      '(mv t warnings)
    `(b* (((mv __ok1__ warnings) ,(car lst))
          ((mv __ok2__ warnings) ,(wf-progn-warn-fn (cdr lst))))
         (mv (and __ok1__ __ok2__) warnings))))

(defund wf-and-warn-fn (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      '(mv t warnings)
    `(b* (((mv __ok1__ warnings) ,(car lst)))
         (if (not __ok1__)
             (mv nil warnings)
           ,(wf-and-warn-fn (cdr lst))))))

(defun wf-pretty-if (x y z)
  (declare (xargs :guard t))
  (if (equal x t)
      y
    (if (equal x nil)
        z
      `(if ,x ,y ,z))))

(defun wf-rewrite-body (warnp body)
  (declare (xargs :guard t))
  (cond ((atom body)
         body)

        ((equal (car body) 'quote)
         body)

        ((equal (car body) '@wf-progn)
         (let ((args (wf-rewrite-body warnp (cdr body))))
           (if warnp
               (wf-progn-warn-fn args)
             `(and . ,args))))

        ((equal (car body) '@wf-and)
         (let ((args (wf-rewrite-body warnp (cdr body))))
           (if warnp
               (wf-and-warn-fn args)
             `(and . ,args))))

        ((equal (car body) '@wf-note)
         (cond ((and (true-listp body)
                     (equal (len body) 5))
                ;; (@wf-note condition type msg args)
                (let ((condition (second body))
                      (type      (third body))
                      (msg       (fourth body))
                      (args      (fifth body)))
                  (if warnp
                      `(if ,condition
                           (mv t warnings)
                         (mv t
                             (cons (make-vl-warning :type ,type
                                                    :msg ,msg
                                                    :args ,args)
                                   warnings)))
                    t)))
               (t
                (er hard? 'wf-rewrite-body "Malformed @wf-note: ~x0." body))))

        ((equal (car body) '@wf-assert)
         (cond ((and (true-listp body)
                     (equal (len body) 5))
                ;; (@wf-assert condition type msg args)
                (let ((condition (second body))
                      (type      (third body))
                      (msg       (fourth body))
                      (args      (fifth body)))
                  (if warnp
                      `(if ,condition
                           (mv t warnings)
                         (mv nil
                             (cons (make-vl-warning :type ,type
                                                    :msg ,msg
                                                    :args ,args)
                                   warnings)))
                    (wf-pretty-if condition t nil))))
               ((and (true-listp body)
                     (equal (len body) 2))
                ;; (@wf-assert condition)
                (let ((condition (second body)))
                  (if warnp
                      `(mv ,(wf-pretty-if condition t nil) warnings)
                    (wf-pretty-if condition t nil))))
               (t
                (er hard? 'wf-rewrite-body "Malformed @wf-assert: ~x0." body))))

        ((equal (car body) '@wf-call)
         ;; (@wf-call fn ...)
         (cond ((and (true-listp body)
                     (<= 2 (len body))
                     (symbolp (second body)))
                (let* ((name      (second body))
                       (name-warn (intern-in-package-of-symbol
                                   (concatenate 'string (symbol-name name) "-WARN")
                                   name))
                       (args      (cddr body)))
                  (if warnp
                      (cons name-warn (append args (list 'warnings)))
                    (cons name args))))
               (t
                (er hard? 'wf-rewrite-body "Malformed @wf-call: ~x0." body))))

        (t
         (cons (wf-rewrite-body warnp (car body))
               (wf-rewrite-body warnp (cdr body))))))



(defun wf-warn-name (name)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-WARN")
                               name))

(defprojection wf-warn-name-list (x)
  (wf-warn-name x)
  :mode :program
  :optimize nil
  :parents nil)

(defun wf-normal-defun (name formals guard body extra-decls)
  (declare (xargs :mode :program))
  `(defund ,name ,formals
     (declare (xargs :guard ,guard
                     :normalize nil)
              ,@extra-decls)
     ,(wf-rewrite-body nil body)))

(defun wf-warn-defun (name formals guard body extra-decls)
  (declare (xargs :mode :program))
  `(defund ,(wf-warn-name name) (,@formals warnings)
     (declare (xargs :guard (and ,guard
                                 (vl-warninglist-p warnings))
                     :normalize nil)
              (ignorable warnings)
              ,@extra-decls)
     ,(wf-rewrite-body t body)))


(defmacro defwellformed (name formals &key guard body extra-decls parents short long)
  (let ((name-warn (intern-in-package-of-symbol
                    (concatenate 'string (symbol-name name) "-WARN")
                    name)))
    `(defsection ,name
       ,@(and parents `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))

       ,(wf-normal-defun name formals guard body extra-decls)
       ,(wf-warn-defun name formals guard body extra-decls)

       (local (in-theory (e/d (,name ,name-warn)
                              ((force)))))

       (defthm ,(intern-in-package-of-symbol
                 (concatenate 'string "ELIMINATE-" (symbol-name name-warn))
                 name-warn)
         (equal (mv-nth 0 (,name-warn ,@formals warnings))
                (,name ,@formals)))

       (defthm ,(intern-in-package-of-symbol
                 (concatenate 'string "VL-WARNINGLIST-P-OF-" (symbol-name name-warn))
                 name-warn)
         (implies (force (vl-warninglist-p warnings))
                  (vl-warninglist-p (mv-nth 1 (,name-warn ,@formals warnings))))))))


(defmacro defwellformed-list (list-name formals &key element guard parents short long)
  `(encapsulate
    ()
    (defwellformed ,list-name ,formals
      :parents ,parents
      :short ,short
      :long ,long
      :guard ,guard
      :body (if (atom x)
                (@wf-assert t)
              (@wf-progn
               (@wf-call ,element ,@(subst '(car x) 'x formals))
               (@wf-call ,list-name ,@(subst '(cdr x) 'x formals)))))

    (deflist ,list-name ,formals
      (,element ,@formals)
      :already-definedp t
      :parents nil)))


;; Supporting mutual recursion takes some work

(defun wf-parse-defwellformed-forms (x)
  (declare (xargs :mode :program))
  (cond ((atom x)
         nil)
        ((not (and (consp (car x))
                   (equal (caar x) 'defwellformed)))
         (er hard? 'wf-parse-defwellformed-forms
             "Expected (defwellformed ...), but found ~x0." (car x)))
        (t
         (let ((guard       (FLAG::extract-keyword-from-args :guard (cdar x)))
               (body        (FLAG::extract-keyword-from-args :body (cdar x)))
               (extra-decls (FLAG::extract-keyword-from-args :extra-decls (cdar x)))
               (parents     (FLAG::extract-keyword-from-args :parents (cdar x)))
               (short       (FLAG::extract-keyword-from-args :short (cdar x)))
               (long        (FLAG::extract-keyword-from-args :long (cdar x)))
               (rest        (FLAG::throw-away-keyword-parts (cdar x))))
           (if (not (and (equal (len rest) 2)
                         (symbolp (first rest))
                         (symbol-listp (second rest))))
               (er hard? 'wf-parse-defwellformed-forms "Bad (defwellformed ...) form: ~x0." (car x))
             (cons (list (cons :name (first rest))
                         (cons :formals (second rest))
                         (cons :parents parents)
                         (cons :short short)
                         (cons :long long)
                         (cons :guard guard)
                         (cons :body body)
                         (cons :extra-decls extra-decls))
                   (wf-parse-defwellformed-forms (cdr x))))))))

(defun wf-parsed-forms-to-normal-defuns (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (cons (wf-normal-defun (cdr (assoc :name (car x)))
                           (cdr (assoc :formals (car x)))
                           (cdr (assoc :guard (car x)))
                           (cdr (assoc :body (car x)))
                           (cdr (assoc :extra-decls (car x))))
          (wf-parsed-forms-to-normal-defuns (cdr x)))))

(defun wf-parsed-forms-to-warn-defuns (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (cons (wf-warn-defun (cdr (assoc :name (car x)))
                         (cdr (assoc :formals (car x)))
                         (cdr (assoc :guard (car x)))
                         (cdr (assoc :body (car x)))
                         (cdr (assoc :extra-decls (car x))))
          (wf-parsed-forms-to-warn-defuns (cdr x)))))

(defun wf-parsed-forms-to-names (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (cons (cdr (assoc :name (car x)))
          (wf-parsed-forms-to-names (cdr x)))))

(defun wf-flag-elim-cases (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (let* ((name       (cdr (assoc :name (car x))))
           (formals    (cdr (assoc :formals (car x))))
           (name-warn  (wf-warn-name name)))
      (cons `(,name-warn (equal (mv-nth 0 (,name-warn ,@formals warnings))
                                (,name ,@formals)))
            (wf-flag-elim-cases (cdr x))))))

(defun wf-flag-wlist-cases (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (let* ((name       (cdr (assoc :name (car x))))
           (formals    (cdr (assoc :formals (car x))))
           (name-warn  (wf-warn-name name)))
      (cons `(,name-warn (implies (force (vl-warninglist-p warnings))
                                  (vl-warninglist-p (mv-nth 1 (,name-warn ,@formals warnings)))))
            (wf-flag-wlist-cases (cdr x))))))

(defun mutual-defwellformed-start-fn (x)
  (declare (xargs :mode :program))
  (let* ((parsed    (wf-parse-defwellformed-forms x))
         (normal    (cons 'mutual-recursion (wf-parsed-forms-to-normal-defuns parsed)))
         (warn      (cons 'mutual-recursion (wf-parsed-forms-to-warn-defuns parsed))))
    `(progn ,normal ,warn)))

(defun mutual-defwellformed-finish-fn (x world)
  (declare (xargs :mode :program))
  (let* ((parsed    (wf-parse-defwellformed-forms x))
         (names     (wf-parsed-forms-to-names parsed))
         (names-w   (wf-warn-name-list names))
         (names-w1  (car names-w))
         (flag-fn-name
          (intern-in-package-of-symbol (concatenate 'string "FLAG-" (symbol-name names-w1)) names-w1))
         (defthm-macro-name
           (intern-in-package-of-symbol (concatenate 'string "DEFTHM-" (symbol-name flag-fn-name)) flag-fn-name))

         (elim-cases  (wf-flag-elim-cases parsed))
         (wlist-cases (wf-flag-wlist-cases parsed))

         ;; VERY GROSS.  Pulling stuff right from make-flag-fn.  BOZO look
         ;; into using the tables generated in flag instead.
         (flag-var (intern-in-package-of-symbol "FLAG" flag-fn-name))
         (alist    (pairlis$ (FLAG::get-clique-members names-w1 world)
                             (FLAG::get-clique-members names-w1 world)))
         (formals  (FLAG::merge-formals alist world)))

    `(encapsulate
      ()
      (FLAG::make-flag ,flag-fn-name ,names-w1
                       :defthm-macro-name ,defthm-macro-name)

      (local (in-theory (e/d (,@names ,@names-w)
                             ((force)))))

      (,defthm-macro-name ,(intern-in-package-of-symbol
                            (concatenate 'string "ELIMINATE-" (symbol-name names-w1))
                            names-w1)
        ,@elim-cases
        :hints(("Goal"
                :induct (,flag-fn-name ,flag-var . ,formals))
               (and stable-under-simplificationp
                    (FLAG::expand-calls-computed-hint ACL2::clause
                                                      ',(cons flag-fn-name (strip-cars alist))))))

      (,defthm-macro-name ,(intern-in-package-of-symbol
                            (concatenate 'string "VL-WARNINGLIST-P-OF-" (symbol-name names-w1))
                            names-w1)
        ,@wlist-cases
        :hints(("Goal"
                :induct (,flag-fn-name ,flag-var . ,formals))
               (and stable-under-simplificationp
                    (FLAG::expand-calls-computed-hint ACL2::clause
                                                      ',(cons flag-fn-name (strip-cars alist))))))

      )))

(defmacro mutual-defwellformed (&rest args)
  `(encapsulate
    ()
    ,(mutual-defwellformed-start-fn args)
    (make-event (let ((world (w state)))
                  (value (mutual-defwellformed-finish-fn ',args world))))))




#||

;; Some examples.

(local (include-book  ;; fool dependency scanner
        "util-arithmetic"))

(defwellformed good-int-p (x)
  :guard (integerp x)
  :body (@wf-assert (> x 5)
                    :bad-int
                    "Expected good int, but ~x0 is too small."
                    (list x)))

(defwellformed-list good-intlist-p (x)
  :element good-int-p
  :guard (integer-listp x))

(mutual-defwellformed

 (defwellformed even-odd-p (x)
   :guard (integer-listp x)
   :body (if (atom x)
             (@wf-assert t)
           (@wf-progn
            (@wf-assert (evenp (car x))
                        :bad-even
                        "Expected even, but found ~x0."
                        (list (car x)))
            (@wf-call odd-even-p (cdr x)))))

 (defwellformed odd-even-p (x)
   :guard (integer-listp x)
   :body (if (atom x)
             (@wf-assert t)
           (@wf-progn
            (@wf-assert (oddp (car x))
                        :bad-odd
                        "Expected odd, but found ~x0."
                        (list (car x)))
            (@wf-call even-odd-p (cdr x))))))

(odd-even-p '(1 2 3 4 5 6))
(odd-even-p '(2 3 4 5 6 7))
(odd-even-p-warn '(1 2 3 4 5 6) nil)
(odd-even-p-warn '(2 3 4 5 6 7) nil)

||#
