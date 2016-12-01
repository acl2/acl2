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

(in-package "STD")
(include-book "std/strings/defs-program" :dir :system)
(include-book "std/lists/append" :dir :system)
(include-book "maybe-defthm")
(include-book "support")
(set-state-ok t)

(defxdoc defmapappend
  :parents (std/util)
  :short "Append transformations of list elements."

  :long "<p>Defmapappend allows you to quickly introduce a function like</p>

@({
 (loop for elem in x append (f elem))
})

<p>and produces some basic theorems about this new function.</p>

<p>General form:</p>

@({
 (defmapappend name formals
    transform
    &key guard                   ; t by default
         verify-guards           ; t by default
         transform-exec          ; nil by default
         transform-true-list-p   ; nil by default
         mode                    ; default defun-mode by default
         parents                 ; nil by default
         short                   ; nil by default
         long                    ; nil by default
         rest                    ; nil by default
         already-definedp        ; nil by default
         )
})

<p>For instance,</p>

@({
 (defmapappend append-square-lists (x)
    (square-lists x)
    :guard (integer-list-listp x))
})

<p>would introduce a new function, @('append-square-lists'), that applies
@('square-lists') to every element of its argument and appends together all of
the results.</p>

<p>Note that <b>x</b> is treated in a special way: it refers to the whole list
in the formals and guards, but refers to the individual elements of the list in
the @('element') portion.  This is similar to how other macros like @(see
deflist), @(see defalist), and @(see defprojection) handle @('x').</p>



<h3>Usage and Arguments</h3>

<p>Let @('pkg') be the package of @('name').  All functions, theorems, and
variables are created in this package.  One of the formals must be @('pkg::x'),
and this argument represents the list that will be transformed.  Otherwise, the
only restriction on formals is that you may not use the names @('pkg::a'),
@('pkg::y'), and @('pkg::acc'), because we use these variables in the theorems
we generate.</p>

<p>The @('transform') should indicate an element transforming function that
produces a list of some kind as its output.  Adopting an ML-like syntax,
@('transform') should have a signature such as the following:</p>

@({
  transform : elem -> A list
})

<p>We produce a new function of the given @('name'), which has the
signature:</p>

@({
  name : elem list -> A list
})

<p>Our new function applies @('transform') to every element in its input list,
and appends together all of the results.  That is, the logical definition of
the new function we introduce is as follows:</p>

@({
 (defun name (x)
   (if (atom x)
       nil
     (append (transform (car x))
             (name (cdr x)))))
})

<p>The new function will be more efficient than the above.  In particular, we
write a @('mappappend-exec') function that builds the answer in reverse using
revappend and reverses it at the end.  An even more efficient version is
possible when the @(':transform-exec') option is provided; see below for
details.</p>

<p>The optional @(':guard') and @(':verify-guards') are given to the
@('defund') event that we introduce.  Often @(see deflist) is convenient for
introducing the necessary guard.</p>

<p>The optional @(':mode') keyword can be set to @(':logic') or @(':program')
to introduce the recognizer in logic or program mode.  The default is whatever
the current default defun-mode is for ACL2, i.e., if you are already in program
mode, it will default to program mode, etc.</p>

<p>The optional @(':already-definedp') keyword can be set if you have already
defined the function.  This can be used to generate all of the ordinary
@('defmapappend') theorems without generating a @('defund') event, and is
useful when you are dealing with mutually recursive transformations.</p>

<p>The optional @(':transform-true-list-p') argument can be set to @('t')
whenever the transformation is known to unconditionally produce a true list,
and allows us to slightly optimize our function.</p>

<h4>The :transform-exec argument</h4>

<p>When provided, the optional @(':transform-exec') argument should be the name
of a function that satisfies the following property:</p>

@({
   (equal (transform-exec x acc)
          (revappend (transform x)))
})

<p>Note that such functions are automatically introduced by @(see
defprojection).  For instance,</p>

@({
 (defprojection square-list (x)
   (square x))
})

<p>generates a suitable function named @('square-list-exec').  Amusingly,
suitable functions are also generated by defmapappend, itself.</p>

<p>When such a function is provided, we can use it to generate a more efficient
implementation, which uses the tail-recursive function to build the answer in
reverse, and then reverses it at the very end, avoiding even the intermediate
computation of the lists emitted by @('transform').</p>

<p>The optional @(':parents'), @(':short'), and @(':long') options are as in
@(see xdoc), and are analogous to those of @(see deflist) or @(see
defprojection).</p>

<p>The optional @(':rest') option is as in @(see deflist), and allows you to
add theorems into the same section.</p>")



#!acl2
(defsection elementlist-mapappend-exec
  (defun elementlist-mapappend-exec (x acc)
    (if (atom x)
        acc
      (elementlist-mapappend-exec
       (cdr x) (revappend (element-listxformer (car x)) acc))))

  (def-mapappend-rule elementlist-mapappend-exec-removal
    (equal (elementlist-mapappend-exec x acc)
           (revappend (elementlist-mapappend x) acc))
    :requirement exec-fn))


(program)

(defun defmapappend-substitution (name exec formals element kwd-alist x)
  (b* ((already-definedp (getarg :already-definedp nil kwd-alist)))
    `((acl2::element-listxformer (lambda (,x) ,element))
      (acl2::elementlist-mapappend (lambda (,x) (,name . ,formals)))
      ;; BOZO fix for when we deal with return types
      (acl2::element-p (lambda (,x) t))
      (acl2::outelement-p (lambda (,x) t))
      (acl2::outelement-list-p (lambda (,x) t))
      (acl2::outelement-list-final-cdr-p (lambda (,x) t))
      ,@(and (not already-definedp)
             `((acl2::elementlist-mapappend-exec (lambda (,x acl2::acc) (,exec ,@formals acl2::acc))))))))

(defun defmapappend-requirement-alist (kwd-alist formals)
  (b* ((already-definedp (getarg :already-definedp nil kwd-alist))
       (single-var (eql (len formals) 1))
       (cheap      (getarg :cheap      nil kwd-alist)))
    `((acl2::exec-fn . ,(not already-definedp))
      (acl2::single-var . ,single-var)
      (acl2::cheap      . ,cheap)
      (acl2::resulttype . nil))))

(mutual-recursion
 (defun defmapappend-thmbody-subst (body element name exec formals x)
   (if (atom body)
       body
     (case (car body)
       (acl2::element-listxformer
        (cons (car element) (subst (cadr body) x (cdr element))))
       (acl2::elementlist-mapappend
        (cons name (subst (cadr body) x formals)))
       (acl2::elementlist-mapappend-exec
        (cons exec (append (subst (cadr body) x formals) (cddr body))))
       (t (if (symbolp (car body))
              (cons (car body)
                    (defmapappend-thmbody-list-subst (cdr body) element name exec formals x))
            (defmapappend-thmbody-list-subst body element name exec formals x))))))
 (defun defmapappend-thmbody-list-subst (body element name exec formals x)
   (if (atom body)
       body
     (cons (defmapappend-thmbody-subst (car body) element name exec formals x)
           (defmapappend-thmbody-list-subst (cdr body) element name exec formals x)))))


(defun defmapappend-thmname-subst (thmname name element)
  (b* ((thmname (symbol-name thmname))
       (subst-list `(("ELEMENTLIST-MAPAPPEND" . ,(symbol-name name))
                     ("ELEMENT-LISTXFORMER" . ,(symbol-name element)))))
    (intern-in-package-of-symbol
     (dumb-str-sublis subst-list thmname)
     name)))


(defun defmapappend-instantiate (table-entry element name exec formals kwd-alist x
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
       (thmname (defmapappend-thmname-subst thmname-base name (car element)))
       (body (let ((look (assoc :body alist)))
               (if look (cadr look) (fgetprop inst-thm 'acl2::untranslated-theorem nil world))))
       ((when (not body)) (er hard? 'defmapappend-instantiate
                              "Bad defmapappend table entry: ~x0~%" inst-thm))
       (rule-classes
        (b* ((cheap-look (and (getarg :cheap nil kwd-alist)
                              (assoc :cheap-rule-classes alist)))
             ((when cheap-look) (cadr cheap-look))
             (look (assoc :rule-classes alist)))
          (if look (cadr look) (fgetprop inst-thm 'acl2::classes nil world)))))
    `((defthm ,thmname
        ,(defmapappend-thmbody-subst body element name exec formals x)
        :hints (("goal" :use ((:functional-instance
                               ,inst-thm
                               . ,fn-subst))))
        :rule-classes ,rule-classes))))

(defun defmapappend-instantiate-table-thms-aux
  (table element name exec formals kwd-alist x
         req-alist fn-subst world)
  (if (atom table)
      nil
    (append (defmapappend-instantiate (car table) element name exec formals kwd-alist x
              req-alist fn-subst world)
            (defmapappend-instantiate-table-thms-aux (cdr table) element name exec formals kwd-alist x
              req-alist fn-subst world))))

(defun defmapappend-instantiate-table-thms (name exec formals element kwd-alist x world)
  (b* ((table (table-alist 'acl2::mapappend-rules world))
       (fn-subst (defmapappend-substitution name exec formals element kwd-alist x))
       (req-alist (defmapappend-requirement-alist kwd-alist formals)))
    (defmapappend-instantiate-table-thms-aux table element name exec formals kwd-alist x req-alist fn-subst world)))


(defconst *defmapappend-valid-keywords*
  '(:guard
    :verify-guards
    :transform-exec
    :transform-true-list-p
    :already-definedp
    :mode
    :parents
    :short
    :long
    :rest ;; deprecated
    ))

(defun defmapappend-fn (name formals transform kwd-alist other-events state)
  (declare (xargs :mode :program))
  (b* (((unless (symbolp name))
        (er hard? 'defmapappend "Name must be a symbol, but is ~x0." name))

       (mksym-package-symbol name)

       ;; Special variables that are reserved by defmapappend
       (x   (intern-in-package-of-symbol "X" name))
       (a   (intern-in-package-of-symbol "A" name))
       (n   (intern-in-package-of-symbol "N" name))
       (y   (intern-in-package-of-symbol "Y" name))
       (acc (intern-in-package-of-symbol "ACC" name))

       ((unless (and (symbol-listp formals)
                     (no-duplicatesp formals)))
        (er hard 'defmapappend
            "The formals must be a list of unique symbols, but the ~
            formals are ~x0." formals))

       (world (w state))

       (guard                 (getarg :guard                 t      kwd-alist))
       (verify-guards         (getarg :verify-guards         t      kwd-alist))
       (transform-exec        (getarg :transform-exec        nil    kwd-alist))
       (transform-true-list-p (getarg :transform-true-list-p t      kwd-alist))
       (already-definedp      (getarg :already-definedp      nil    kwd-alist))
       (mode                  (getarg :mode                  :logic kwd-alist))
       (short                 (getarg :short                 nil    kwd-alist))
       (long                  (getarg :long                  nil    kwd-alist))

       (rest                  (append (getarg :rest nil kwd-alist)
                                      other-events))

       ((unless (member x formals))
        (er hard 'defmapappend
            "The formals must contain X, but are ~x0.~%" formals))

       ((unless (and (not (member a formals))
                     (not (member n formals))
                     (not (member y formals))
                     (not (member acc formals))))
        (er hard 'defmapappend
            "As a special restriction, formals may not mention a, n, ~
            or y, but the formals are ~x0." formals))

       ((unless (and (consp transform)
                     (symbolp (car transform))))
        (er hard 'defmapappend
            "The transform must be a function applied to the formals, ~
             but is ~x0." transform))

       (exec-fn        (mksym name '-exec))
       (transform-fn   (car transform))
       (transform-args (cdr transform))

       ((unless (and (subsetp-equal transform-args formals)
                     (subsetp-equal formals transform-args)))
        (er hard 'defmapappend
            "The transform's formals do not agree with the defmapappend ~
             function's formals."))

       ((unless (booleanp verify-guards))
        (er hard 'defmapappend
            ":verify-guards must be a boolean, but is ~x0."
            verify-guards))

       ((unless (booleanp transform-true-list-p))
        (er hard 'defmapappend
            ":transform-true-list-p must be a boolean, but is ~x0."
            transform-true-list-p))

       ((unless (symbolp transform-exec))
        (er hard 'defmapappend
            ":transform-exec must be a symbol, but is ~x0."
            transform-exec))

       ((unless (member mode '(:logic :program)))
        (er hard 'defmapappend
            ":mode must be :logic or :program, but is ~x0."
            mode))

       (parents-p (assoc :parents kwd-alist))
       (parents   (cdr parents-p))

       (squelch-docs-p
        ;; Special hack to avoid overwriting existing documentation if we have
        ;; nothing to say.  BOZO it would be better to use the deflist approach
        ;; and always create an extension of a topic.  That might work well if
        ;; we switch this to use DEFINE, too.
        (and already-definedp
             (not short)
             (not long)
             (not parents)))

       (parents (and (not squelch-docs-p)
                     (if parents-p
                         parents
                       (xdoc::get-default-parents world))))

       (short (and (not squelch-docs-p)
                   (or short
                       (and parents
                            (concatenate 'string  "@(call " (xdoc::full-escape-symbol name)
                                         ") applies @(see? " (xdoc::full-escape-symbol transform-fn)
                                         ") to every member of the list @('x'), "
                                         "and appends together all the resulting lists.")))))

       (long (and (not squelch-docs-p)
                  (or long
                      (and parents
                           (concatenate 'string  "<p>This is an ordinary @(see std::defmapappend).</p>"
                                        "@(def " (xdoc::full-escape-symbol name) ")")))))

       (def
        (if already-definedp
            nil
          `((defund ,exec-fn (,@formals ,acc)
              (declare (xargs :guard ,guard
                              :verify-guards nil))
              (if (consp ,x)
                  (,exec-fn ,@(subst `(cdr ,x) x formals)
                            ,(if transform-exec
                                 `(,transform-exec ,@(subst `(car ,x) x transform-args) ,acc)
                               `(,(if transform-true-list-p
                                      'revappend
                                    'revappend-without-guard)
                                 (,transform-fn . ,(subst `(car ,x) x transform-args))
                                 ,acc)))
                ,acc))

            (defund ,name (,@formals)
              (declare (xargs :guard ,guard
                              :verify-guards nil))
              (mbe :logic (if (consp ,x)
                              (append (,transform-fn . ,(subst `(car ,x) x transform-args))
                                      (,name . ,(subst `(cdr ,x) x formals)))
                            nil)
                   :exec (reverse (,exec-fn ,@formals nil)))))))

       ((when (eq mode :program))
        `(defsection ,name
           ,@(and (or parents-p squelch-docs-p parents) `(:parents ,parents))
           ,@(and short   `(:short ,short))
           ,@(and long    `(:long ,long))
           ,@(and squelch-docs-p `(:no-xdoc-override t))
           (program)
           ,@def
           . ,rest))

       (events
        `((logic)
          ,@def
          (local (in-theory (enable ,@(if already-definedp
                                          `(,name)
                                        `(,name ,exec-fn)))))
          ,@(defmapappend-instantiate-table-thms
              name exec-fn formals transform kwd-alist x world)
          . ,(and (not already-definedp)
                  verify-guards
                  `((verify-guards ,exec-fn)
                    (verify-guards ,name))))))

    `(defsection ,name
       ,@(and (or parents-p squelch-docs-p parents) `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))
       ,@(and squelch-docs-p `(:no-xdoc-override t))
       . ,(if (not rest)
              events
            `(;; keep all our deflist theory stuff bottled up
              (encapsulate () . ,events)
              ;; now do the rest of the events with name enabled, so they get
              ;; included in the section
              (local (in-theory (enable ,name)))
              . ,rest)))))

(defmacro defmapappend (name &rest args)
  (b* ((__function__ 'defmapappend)
       ((unless (symbolp name))
        (raise "Name must be a symbol."))
       (ctx (list 'defmapappend name))
       ((mv main-stuff other-events) (split-/// ctx args))
       ((mv kwd-alist formals-elem)
        (extract-keywords ctx *defmapappend-valid-keywords* main-stuff nil))
       ((unless (tuplep 2 formals-elem))
        (raise "Wrong number of arguments to defmapappend."))
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
        `(progn ,(defmapappend-fn ',name ',formals ',element ',kwd-alist
                   ',other-events state)
                (value-triple '(defmapappend ,',name)))))))

