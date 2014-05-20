; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "STD")
(include-book "defprojection")

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

(defun defmapappend-fn (name formals transform
                             guard verify-guards
                             transform-exec transform-true-list-p
                             mode
                             parents short long
                             rest
                             )
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

       (short (or short
                  (and parents
                       (concatenate 'string  "@(call " (symbol-name name)
                                    ") applies @(see " (symbol-name transform-fn)
                                    ") to every member of the list @('x'), "
                                    "and appends together all the resulting lists."))))

       (long (or long
                 (and parents
                      (concatenate 'string  "<p>This is an ordinary @(see std::defmapappend).</p>"
                                   "@(def " (symbol-name name) ")"))))

       (def
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
                 :exec (reverse (,exec-fn ,@formals nil))))))

       ((when (eq mode :program))
        `(defsection ,name
           ,@(and parents `(:parents ,parents))
           ,@(and short   `(:short ,short))
           ,@(and long    `(:long ,long))
           (program)
           ,@def
           . ,rest))

       (events
        `((logic)
          ,@def
          (defthm ,(mksym name '-when-not-consp)
            (implies (not (consp ,x))
                     (equal (,name . ,formals)
                            nil))
            :hints(("Goal" :in-theory (enable ,name))))

          (defthm ,(mksym name '-of-cons)
            (equal (,name . ,(subst `(cons ,a ,x) x formals))
                   (append (,transform-fn . ,(subst a x transform-args))
                           (,name . ,formals)))
            :hints(("Goal" :in-theory (enable ,name))))

          (local (defthm lemma
                   (implies (true-listp ,acc)
                            (true-listp (,exec-fn ,@formals ,acc)))
                   :hints(("Goal" :in-theory (enable ,exec-fn)))))

          (defthm ,(mksym exec-fn '-removal)
            (equal (,exec-fn ,@formals ,acc)
                   (append (rev (,name ,@formals)) ,acc))
            :hints(("Goal" :in-theory (enable ,exec-fn))))

          ,@(if verify-guards
                `((verify-guards ,exec-fn)
                  (verify-guards ,name))
              nil)

          (defthm ,(mksym name '-of-list-fix)
            (equal (,name . ,(subst `(list-fix ,x) x formals))
                   (,name . ,formals))
            :hints(("Goal" :induct (len ,x))))

          (defthm ,(mksym name '-of-append)
            (equal (,name . ,(subst `(append ,x ,y) x formals))
                   (append (,name . ,formals)
                           (,name . ,(subst y x formals))))
            :hints(("Goal" :induct (len ,x)))))))

    `(defsection ,name
       ,@(and parents `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))
       . ,(if (not rest)
              events
            `(;; keep all our deflist theory stuff bottled up
              (encapsulate () . ,events)
              ;; now do the rest of the events with name enabled, so they get
              ;; included in the section
              (local (in-theory (enable ,name)))
              . ,rest)))))

(defmacro defmapappend (name formals transform
                             &key
                             transform-exec
                             (transform-true-list-p 't)
                             (guard 't)
                             (verify-guards 't)
                             mode
                             (parents 'nil parents-p)
                             (short 'nil)
                             (long 'nil)
                             (rest 'nil))
  `(make-event (let ((mode    (or ',mode (default-defun-mode (w state))))
                     (parents (if ',parents-p
                                  ',parents
                                (or (xdoc::get-default-parents (w state))
                                    '(acl2::undocumented)))))
                 (defmapappend-fn ',name ',formals ',transform
                   ',guard ',verify-guards
                   ',transform-exec ',transform-true-list-p
                   mode
                   parents ',short ',long
                   ',rest))))


