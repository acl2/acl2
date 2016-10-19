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
;
; Additional Copyright Notice.
;
; This file is adapted from the Milawa Theorem Prover, Copyright (C) 2005-2009
; Kookamara LLC, which is also available under an MIT/X11 style license.

(in-package "STD")
(include-book "std/strings/defs-program" :dir :system)
(include-book "std/lists/append" :dir :system)
(include-book "centaur/nrev/pure" :dir :system)
(include-book "define")
(include-book "maybe-defthm")
(set-state-ok t)

(defun variable-or-constant-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (or (symbolp (car x))
             (quotep (car x))
             ;; things that quote to themselves
             (acl2-numberp (car x))
             (stringp (car x))
             (characterp (car x)))
         (variable-or-constant-listp (cdr x)))))

(defun collect-vars (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (legal-variablep (car x))
        (cons (car x) (collect-vars (cdr x)))
      (collect-vars (cdr x)))))


(defxdoc defprojection
  :parents (std/util)
  :short "Project a transformation across a list."

  :long "<p>Defprojection allows you to quickly introduce a function like
@('map f').  That is, given an element-transforming function, @('f'), it can
define a new function that applies @('f') to every element in a list.  It also
sets up a basic theory with rules about @(see len), @(see append), etc., and
generates basic, automatic @(see xdoc) documentation.</p>

<h4>General form:</h4>

@({
 (defprojection name extended-formals
   element
   [keyword options]
   [/// other events]
   )

 Options                 Defaults
  :nil-preservingp         nil
  :guard                   t
  :verify-guards           t
  :result-type             nil
  :returns                 nil
  :mode                    current defun-mode
  :already-definedp        nil
  :parallelize             nil
  :verbosep                nil
  :share-suffix            nil
  :parents                 nil
  :short                   nil
  :long                    nil
})

<h4>Basic Examples</h4>

@({
    (defprojection my-strip-cars (x)
      (car x)
      :guard (alistp x))
})

<p>defines a new function, @('my-strip-cars'), that is like the built-in ACL2
function @(see strip-cars).</p>

<p><b><color rgb='#ff0000'>Note</color></b>: @('x') is treated in a special
way.  It refers to the whole list in the formals and guards, but refers to
individual elements of the list in the @('element') portion.  This is similar
to how other macros like @(see deflist), @(see defalist), and @(see
defmapappend) handle @('x').</p>

<p>A @(see define)-like syntax is also available:</p>

@({
    (defprojection my-square-list ((x integer-listp))
      :result (squared-x integer-listp)
      (* x x))
})

<h3>Usage and Optional Arguments</h3>

<p>Let @('pkg') be the package of @('name').  All functions, theorems, and
variables are created in this package.  One of the formals must be @('pkg::x'),
and this argument represents the list that will be transformed.  Otherwise, the
only restriction on formals is that you may not use the names @('pkg::a'),
@('pkg::n'), @('pkg::y'), and @('pkg::acc'), because we use these variables in
the theorems we generate.</p>

<p>The optional @(':nil-preservingp') argument can be set to @('t') when the
element transformation satisfies @('(element nil ...) = nil').  This allows
@('defprojection') to produce slightly better theorems.</p>

<p>The optional @(':guard') and @(':verify-guards') are given to the
@('defund') event that we introduce.  Often @(see deflist) is convenient for
introducing the necessary guard.</p>

<p>The optional @(':result-type') keyword defaults to @('nil'), and in this
case no additional \"type theorem\" will be inferred.  But, if you instead give
the name of a unary predicate like @('nat-listp'), then a defthm will be
generated that looks like @('(implies (force guard) (nat-listp (name ...)))')
while @('name') is still enabled.  This is not a very general mechanism, but it
is often good enough to save a lot of typing.</p>

<p>The optional @(':returns') keyword is similar to that of @(see define), and
is a more general mechanism than @(':result-type').</p>

<p>The optional @(':already-definedp') keyword can be set if you have already
defined the function.  This can be used to generate all of the ordinary
@('defprojection') theorems without generating a @('defund') event, and is
useful when you are dealing with mutually recursive transformations.</p>

<p>The optional @(':mode') keyword can be set to @(':logic') or @(':program')
to introduce the recognizer in logic or program mode.  The default is whatever
the current default defun-mode is for ACL2, i.e., if you are already in program
mode, it will default to program mode, etc.</p>

<p>The optional @(':parallelize') keyword can be set to @('t') if you want to
try to speed up the execution of new function using parallelism.  This is
experimental and only works with ACL2(p).  Note: we don't do anything smart to
split the work up into large chunks, and you lose tail-recursion when you use
this.</p>

<p>The optional @(':share-suffix') keyword can be set to @('t') if you want to
try to reuse a suffix of the original list in cases where the transformation
sometimes does nothing (returns the identical element), in order to reduce
memory footprint.  This only works if the optimized @('nrev') implementation is
used, which carries a trust tag -- to use this, do @('(include-book
\"centaur/nrev/fast\" :dir :system)').</p>

<p>The optional @(':verbosep') flag can be set to @('t') if you want
defprojection to print everything it's doing.  This may be useful if you run
into any failures, or if you are simply curious about what is being
introduced.</p>

<p>The optional @(':parents'), @(':short'), and @(':long') keywords are as in
@(see defxdoc).  Typically you only need to specify @(':parents'), perhaps
implicitly with @(see xdoc::set-default-parents), and suitable documentation
will be automatically generated for @(':short') and @(':long').  If you don't
like this documentation, you can supply your own @(':short') and/or @(':long')
to override it.</p>

<h3>Support for Other Events</h3>

<p>Defprojection implements the same @('///') syntax as other macros like @(see
define).  This allows you to put related events near the definition and have
them included in the automatic documentation.  As with define, the new
projection function is enabled during the @('///') section.  Here is an
example:</p>

@({
    (defprojection square-each (x)
      (square x)
      :guard (integer-listp x)
      ///
      (defthm pos-listp-of-square-each
        (pos-listp (square-each x))))
})

<p>It is valid to use an @('///') section with a @(':result-type') theorem.  We
arbitrarily say the @(':result-type') theorem comes first.</p>

<p>Deprecated.  The optional @(':rest') keyword was a precursor to @('///').
It is still implemented, but its use is now discouraged.  If both @(':rest')
and @('///') events are used, we arbitrarily put the @(':rest') events
first.</p>

<p>The optional @(':optimize') keyword was historically used to optionally
optimize the projection using @('nreverse').  We now use @(see nrev::nrev)
instead, and since this doesn't require a ttag, the @(':optimize') flag
now does nothing.</p>")

(defthmd defprojection-append-nil-is-list-fix
  (equal (append x nil)
         (list-fix x)))

(deftheory defprojection-theory
  (union-theories '(acl2::append-to-nil
                    acl2::append-when-not-consp
                    acl2::append-of-cons
                    acl2::associativity-of-append
                    ;acl2::rev-of-cons
                    ;acl2::rev-when-not-consp
                    ;acl2::revappend-removal
                    ;acl2::reverse-removal
                    )
                  (theory 'minimal-theory)))
                  ;; (union-theories (theory 'minimal-theory)
                  ;;                 (theory 'deflist-support-lemmas))))


#!acl2
(defsection elementlist-projection-exec
  (defun elementlist-projection-exec (x acc)
    (if (atom x)
        acc
      (elementlist-projection-exec (cdr x) (cons (element-xformer (car x)) acc))))

  (def-projection-rule elementlist-projection-exec-removal
    (equal (elementlist-projection-exec x acc)
           (revappend (elementlist-projection x) acc))
    :requirement exec-fn))

#!acl2
(defsection elemenlist-projection-nrev
  (defun elementlist-projection-nrev (x nrev)
    (declare (xargs :stobjs nrev))
    (if (atom x)
        (nrev-fix nrev)
      (let ((nrev (nrev-push (element-xformer (car x)) nrev)))
        (elementlist-projection-nrev (cdr x) nrev))))

  (def-projection-rule elementlist-projection-nrev-removal
    (equal (elementlist-projection-nrev x nrev)
           (append nrev (elementlist-projection x)))
    :hints(("Goal" :in-theory (enable rcons)))
    :requirement nrev-fn))


(program)

(defun defprojection-substitution (name exec nrev formals element kwd-alist x)
  (b* ((already-definedp (getarg :already-definedp nil kwd-alist)))
    `((acl2::element-xformer (lambda (,x) ,element))
      (acl2::elementlist-projection (lambda (,x) (,name . ,formals)))
      ;; BOZO fix for when we deal with return types
      (acl2::element-p (lambda (,x) t))
      (acl2::outelement-p (lambda (,x) t))
      ,@(and (not already-definedp)
             `((acl2::elementlist-projection-nrev (lambda (,x nrev::nrev) (,nrev ,@formals nrev::nrev)))
               (acl2::elementlist-projection-exec (lambda (,x acl2::acc) (,exec ,@formals acl2::acc))))))))

(defun defprojection-requirement-alist (kwd-alist formals)
  (b* ((nil-preservingp (getarg :nil-preservingp nil kwd-alist))
       (already-definedp (getarg :already-definedp nil kwd-alist))
       (single-var (eql (len formals) 1))
       (cheap      (getarg :cheap      nil kwd-alist)))
    `((acl2::nil-preservingp . ,nil-preservingp)
      (acl2::nil-to-nil . ,nil-preservingp)
      (acl2::exec-fn . ,(not already-definedp))
      (acl2::nrev-fn . ,(not already-definedp))
      (acl2::single-var . ,single-var)
      (acl2::cheap      . ,cheap)
      (acl2::resulttype . nil))))

(mutual-recursion
 (defun defprojection-thmbody-subst (body element name exec nrev formals x)
   (if (atom body)
       body
     (case (car body)
       (acl2::element-xformer
        (cons (car element) (subst (cadr body) x (cdr element))))
       (acl2::elementlist-projection
        (cons name (subst (cadr body) x formals)))
       (acl2::elementlist-projection-exec
        (cons exec (append (subst (cadr body) x formals) (cddr body))))
       (acl2::elementlist-projection-nrev
        (cons nrev (append (subst (cadr body) x formals) (cddr body))))
       (t (if (symbolp (car body))
              (cons (car body)
                    (defprojection-thmbody-list-subst (cdr body) element name exec nrev formals x))
            (defprojection-thmbody-list-subst body element name exec nrev formals x))))))
 (defun defprojection-thmbody-list-subst (body element name exec nrev formals x)
   (if (atom body)
       body
     (cons (defprojection-thmbody-subst (car body) element name exec nrev formals x)
           (defprojection-thmbody-list-subst (cdr body) element name exec nrev formals x)))))


(defun defprojection-thmname-subst (thmname name element)
  (b* ((thmname (symbol-name thmname))
       (subst-list `(("ELEMENTLIST-PROJECTION" . ,(symbol-name name))
                     ("ELEMENT-XFORMER" . ,(symbol-name element)))))
    (intern-in-package-of-symbol
     (dumb-str-sublis subst-list thmname)
     name)))


(defun defprojection-instantiate (table-entry element name exec nrev formals kwd-alist x
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
       (thmname (defprojection-thmname-subst thmname-base name (car element)))
       (body (let ((look (assoc :body alist)))
               (if look (cadr look) (fgetprop inst-thm 'acl2::untranslated-theorem nil world))))
       ((when (not body)) (er hard? 'defprojection-instantiate
                              "Bad defprojection table entry: ~x0~%" inst-thm))
       (rule-classes
        (b* ((cheap-look (and (getarg :cheap nil kwd-alist)
                              (assoc :cheap-rule-classes alist)))
             ((when cheap-look) (cadr cheap-look))
             (look (assoc :rule-classes alist)))
          (if look (cadr look) (fgetprop inst-thm 'acl2::classes nil world)))))
    `((defthm ,thmname
        ,(defprojection-thmbody-subst body element name exec nrev formals x)
        :hints (("goal" :use ((:functional-instance
                               ,inst-thm
                               . ,fn-subst))))
        :rule-classes ,rule-classes))))


(defun defprojection-instantiate-table-thms-aux
  (table element name exec nrev formals kwd-alist x
         req-alist fn-subst world)
  (if (atom table)
      nil
    (append (defprojection-instantiate (car table) element name exec nrev formals kwd-alist x
              req-alist fn-subst world)
            (defprojection-instantiate-table-thms-aux (cdr table) element name exec nrev formals kwd-alist x
              req-alist fn-subst world))))

(defun defprojection-instantiate-table-thms (name exec nrev formals element kwd-alist x world)
  (b* ((table (table-alist 'acl2::projection-rules world))
       (fn-subst (defprojection-substitution name exec nrev formals element kwd-alist x))
       (req-alist (defprojection-requirement-alist kwd-alist formals)))
    (defprojection-instantiate-table-thms-aux table element name exec nrev formals kwd-alist x req-alist fn-subst world)))





(defconst *defprojection-valid-keywords*
  '(:nil-preservingp
    :guard
    :verify-guards
    :result-type
    :returns
    :mode
    :already-definedp
    :cheap
    :parallelize
    :share-suffix
    :verbosep
    :parents
    :short
    :long
    :rest     ;; deprecated
    :optimize ;; deprecated
    ))

(defun defprojection-fn (name raw-formals element kwd-alist other-events state)
  (declare (xargs :mode :program))
  (b* ((__function__ 'defprojection)
       (mksym-package-symbol name)
       (world (w state))

       ;; Special variables that are reserved by defprojection
       (x   (intern-in-package-of-symbol "X" name))
       (a   (intern-in-package-of-symbol "A" name))
       (n   (intern-in-package-of-symbol "N" name))
       (y   (intern-in-package-of-symbol "Y" name))
       (acc (intern-in-package-of-symbol "ACC" name))

       (eformals (parse-formals name raw-formals '(:type) world))
       (formal-names (formallist->names eformals))

       ((unless (no-duplicatesp formal-names))
        (raise "The formals must be a list of unique symbols, but the formals ~
                are ~x0." formal-names))
       ((unless (member x formal-names))
        (raise "The formals must contain X, but are ~x0." formal-names))
       ((unless (and (not (member a formal-names))
                     (not (member n formal-names))
                     (not (member y formal-names))
                     (not (member acc formal-names))))
        (raise "As a special restriction, formal-names may not mention a, n, or y, ~
                but the formals are ~x0." formal-names))
       ((unless (and (consp element)
                     (symbolp (car element))))
        (raise "The element transformation should be a function/macro call, ~
                but is ~x0." element))

       (list-fn   name)
       (list-args formal-names)
       (elem-fn   (car element))
       (elem-args (cdr element))
       (exec-fn   (mksym list-fn '-exec))
       (nrev-fn   (mksym list-fn '-nrev))
       (elem-syms (collect-vars elem-args))

       ((unless (variable-or-constant-listp elem-args))
        (raise "The element's arguments must be a function applied to the ~
                formals or constants, but are: ~x0." elem-args))

       ((unless (and (no-duplicatesp elem-syms)
                     (subsetp elem-syms formal-names)
                     (subsetp formal-names elem-syms)))
        (raise "The variables in the :element do not agree with the formals:~% ~
                - formals: ~x0~% ~
                - element vars: ~x1~%" formal-names elem-syms))


       (nil-preservingp  (getarg :nil-preservingp  nil kwd-alist))
       (guard            (getarg :guard            t   kwd-alist))
       (verify-guards    (getarg :verify-guards    t   kwd-alist))
       (result-type      (getarg :result-type      nil kwd-alist))
       (returns          (getarg :returns          nil kwd-alist))
       (already-definedp (getarg :already-definedp nil kwd-alist))
       (optimize         (getarg :optimize         t   kwd-alist))
       (parallelize      (getarg :parallelize      nil kwd-alist))
       (share-suffix     (getarg :share-suffix     nil kwd-alist))
       ;(verbosep         (getarg :verbosep         nil kwd-alist))
       (short            (getarg :short            nil kwd-alist))
       (long             (getarg :long             nil kwd-alist))

       (rest             (append
                          (getarg :rest nil kwd-alist)
                          other-events))

       (mode             (getarg :mode
                                 (default-defun-mode world)
                                 kwd-alist))

       (parents-p (assoc :parents kwd-alist))
       (parents   (cdr parents-p))
       (parents   (if parents-p
                      parents
                    (xdoc::get-default-parents world)))

       ((unless (booleanp verify-guards))
        (raise ":verify-guards must be a boolean, but is ~x0." verify-guards))
       ((unless (booleanp nil-preservingp))
        (raise ":nil-preservingp must be a boolean, but is ~x0." nil-preservingp))
       ((unless (booleanp already-definedp))
        (raise ":already-definedp must be a boolean, but is ~x0." already-definedp))
       ((unless (booleanp optimize))
        (raise ":optimize must be a boolean, but is ~x0." optimize))
       ((unless (booleanp parallelize))
        (raise ":parallelize must be a boolean, but is ~x0." parallelize))
       ((unless (symbolp result-type))
        (raise ":result-type must be a symbol, but is ~x0." result-type))
       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (raise ":mode must be one of :logic or :program, but is ~x0." mode))

       (short (or short
                  (and parents
                       (concatenate 'string "@(call " (xdoc::full-escape-symbol list-fn) ") maps "
                                    "@(see? " (xdoc::full-escape-symbol elem-fn) ") across a list."))))

       (long (or long
                 (and parents
                      (concatenate 'string
                                   "<p>This is an ordinary @(see std::defprojection).</p>"))))

       (prepwork (if already-definedp
                     nil
                   `((define ,exec-fn (,@raw-formals ,acc)
                       ;; For backwards compatibility we still define a -exec
                       ;; function, but it produces the elements in the wrong
                       ;; order so it is usually not what you want.
                       ;; Previously we required that acc was a true-listp in
                       ;; the guard.  But on reflection, this really isn't
                       ;; necessary, and omitting it can simplify the guards of
                       ;; other functions that are directly calling -exec
                       ;; functions.
                       :guard ,guard
                       :mode ,mode
                       ;; We tell ACL2 not to normalize because otherwise type
                       ;; reasoning can rewrite the definition, and ruin some
                       ;; of our theorems below, e.g., when ELEMENT is known to
                       ;; be zero always.
                       :normalize nil
                       :verify-guards nil
                       :parents nil
                       :hooks nil
                       (if (consp ,x)
                           (,exec-fn ,@(subst `(cdr ,x) x list-args)
                                     (cons (,elem-fn ,@(subst `(car ,x) x elem-args))
                                           ,acc))
                         ,acc))

                     (define ,nrev-fn (,@raw-formals nrev::nrev)
                       :guard ,guard
                       :mode ,mode
                       :normalize nil
                       :verify-guards nil
                       :parents nil
                       :hooks nil
                       (if (atom ,x)
                           (nrev::nrev-fix nrev::nrev)
                         (let ((nrev::nrev (nrev::nrev-push (,elem-fn ,@(subst `(car ,x) x elem-args)) nrev::nrev)))
                           (,nrev-fn ,@(subst `(cdr ,x) x list-args) nrev::nrev)))))))

       (def  (if already-definedp
                 nil
               `((define ,list-fn (,@raw-formals)
                   ,@(and parents-p `(:parents ,parents))
                   ,@(and short     `(:short ,short))
                   ,@(and long      `(:long ,long))
                   :returns ,returns
                   :guard ,guard
                   :mode ,mode
                   ;; we tell ACL2 not to normalize because otherwise type
                   ;; reasoning can rewrite the definition, and ruin some of our
                   ;; theorems below, e.g., when ELEMENT is known to be zero.
                   :normalize nil
                   :verify-guards nil
                   :prepwork ,prepwork
                   ,(if parallelize
                        `(if (consp ,x)
                             (pargs (cons (,elem-fn ,@(subst `(car ,x) x elem-args))
                                          (,list-fn ,@(subst `(cdr ,x) x list-args))))
                           nil)
                      `(mbe :logic
                            (if (consp ,x)
                                (cons (,elem-fn ,@(subst `(car ,x) x elem-args))
                                      (,list-fn ,@(subst `(cdr ,x) x list-args)))
                              nil)
                            :exec
                            (if (atom ,x)
                                nil
                              (nrev::with-local-nrev
                                ,(if share-suffix
                                     `(let ((nrev::nrev (nrev::nrev-set-hint ,x nrev::nrev)))
                                        (,nrev-fn ,@list-args nrev::nrev))
                                   `(,nrev-fn ,@list-args nrev::nrev))))))))))

       ((when (eq mode :program))
        `(defsection ,name
           (program)
           ,@def
           . ,(and rest
                   `((defsection ,(mksym name '-rest)
                       ,@(and parents
                              (not already-definedp)
                              `(:extension ,name))
                       . ,rest)))))

       (listp-when-not-consp  (mksym list-fn '-when-not-consp))
       (listp-of-cons         (mksym list-fn '-of-cons))
       (listp-nil-preservingp (mksym list-fn '-nil-preservingp-lemma))

       (main-thms
        `(
          ,@(and nil-preservingp
                 `((value-triple
                    (cw "Defprojection: attempting to justify, using your ~
                         current theory, :nil-preserving ~x0, if necessary.~%"
                        ',name))
                   (with-output :stack :pop
                     (local (maybe-defthm-as-rewrite
                             ,listp-nil-preservingp
                             (equal (,elem-fn ,@(subst ''nil x elem-args))
                                    nil)
                             ;; We just rely on the user to be able to prove this
                             ;; in their current theory.
                             )))))

          (local (make-event
                  ;; Bllalaaaaah... This sucks so bad.  I just want to have a
                  ;; rule with this name, whatever it is.
                  (if (is-theorem-p ',listp-nil-preservingp (w state))
                      (value '(value-triple :invisible))
                    (value '(defthm ,listp-nil-preservingp
                              (or (equal (alistp x) t)
                                  (equal (alistp x) nil))
                              :rule-classes :type-prescription
                              :hints(("Goal"
                                      :in-theory
                                      '((:type-prescription alistp)))))))))

          (value-triple (cw "Defprojection: proving defprojection theorems.~%"))
          ,(if already-definedp
               `(local (in-theory (enable ,list-fn)))
             `(local (in-theory (enable ,nrev-fn ,exec-fn ,list-fn))))
          ,@(defprojection-instantiate-table-thms
              list-fn exec-fn nrev-fn list-args element kwd-alist x world))))

    `(defsection ,name
       (logic)
       (value-triple (cw "Defprojection: defining ~x0.~%" ',name))
       ,@def
       (set-inhibit-warnings "disable" "double-rewrite" "non-rec") ;; implicitly local

       (defsection ,(mksym name '-rest)
         ,@(and parents
                (not already-definedp)
                `(:extension ,name))
         ,@main-thms
         ,@(and (not already-definedp)
                verify-guards
                `((value-triple
                   (cw "Defprojection: verifying guards for ~x0.~%" ',name))
                  (with-output
                    :stack :pop
                    :off (acl2::summary)
                    (progn
                      (verify-guards ,nrev-fn
                        :hints(("Goal"
                                :in-theory
                                (union-theories '()
                                                (theory 'defprojection-theory)))
                               (and stable-under-simplificationp
                                    '(:in-theory (enable )))))
                      (verify-guards ,list-fn
                        :hints(("Goal"
                                :in-theory
                                (union-theories '(,list-fn
                                                  ,(mksym nrev-fn '-removal)
                                                  nrev::nrev-set-hint
                                                  nrev::nrev$a-set-hint
                                                  nrev::nrev-finish
                                                  nrev::nrev$a-finish
                                                  acl2::create-nrev
                                                  acl2::list-fix-when-true-listp
                                                  ,(mksym 'true-listp-of- list-fn))
                                                (theory 'defprojection-theory)))
                               (and stable-under-simplificationp
                                    '(:in-theory (enable )))))
                      (verify-guards ,exec-fn
                        :hints(("Goal"
                                :in-theory
                                (union-theories '(,exec-fn)
                                                (theory 'defprojection-theory)))
                               (and stable-under-simplificationp
                                    '(:in-theory (enable )))))
                      ))))

         (local (in-theory (enable ,list-fn
                                   ,listp-when-not-consp
                                   ,listp-of-cons)))
         ,@(and result-type
                `((value-triple (cw "Defprojection: proving :result-type theorem.~%"))
                  (with-output
                    :stack :pop
                    (defthm ,(mksym result-type '-of- list-fn)
                      ,(if (eq guard t)
                           `(,result-type (,list-fn ,@list-args))
                         `(implies (force ,guard)
                                   (,result-type (,list-fn ,@list-args))))
                      :hints(("Goal"
                              :induct (len ,x)
                              :in-theory (enable (:induction len))))))))
         . ,(and rest
                 `((value-triple (cw "Defprojection: submitting /// events.~%"))
                   (with-output
                     :stack :pop
                     (progn . ,rest))))))))


(defmacro defprojection (name &rest args)
  (b* ((__function__ 'defprojection)
       ((unless (symbolp name))
        (raise "Name must be a symbol."))
       (ctx (list 'defprojection name))
       ((mv main-stuff other-events) (split-/// ctx args))
       ((mv kwd-alist formals-elem)
        (extract-keywords ctx *defprojection-valid-keywords* main-stuff nil))
       ((unless (tuplep 2 formals-elem))
        (raise "Wrong number of arguments to defprojection."))
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
        `(progn ,(defprojection-fn ',name ',formals ',element ',kwd-alist
                   ',other-events state)
                (value-triple '(defprojection ,',name)))))))
