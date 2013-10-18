; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2011 Centaur Technology
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
;
; Additional copyright notice:
;
; This file is adapted from Milawa, which is also released under the GPL.

(in-package "STD")
(include-book "deflist")
(include-book "std/lists/append" :dir :system)

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
    (if (and (symbolp (car x))
             (not (keywordp (car x))))
        (cons (car x) (collect-vars (cdr x)))
      (collect-vars (cdr x)))))


(defxdoc defprojection
  :parents (std/util)
  :short "Project a transformation across a list."

  :long "<p>Defprojection allows you to quickly introduce a function like
@('map f').  That is, given an element-transforming function, @('f'), it can
define a new function that applies @('f') to every element in a list.</p>

<p>General form:</p>

@({
 (defprojection name formals
   element
   &key guard                   ; t by default
        verify-guards           ; t by default
        nil-preservingp         ; nil by default
        result-type             ; nil by default
        already-definedp        ; nil by default
        mode                    ; current defun-mode by default
        optimize                ; t by default
        result-type             ; nil by default
        parents                 ; nil by default
        short                   ; nil by default
        long                    ; nil by default
        parallelize             ; nil by default
        rest                    ; nil by default
        )
})

<p>For example,</p>

@({
 (defprojection my-strip-cars (x)
   (car x)
   :guard (alistp x))
})

<p>defines a new function, @('my-strip-cars'), that is like the built-in ACL2
function @('strip-cars').</p>

<p>Note that <b>x</b> is treated in a special way: it refers to the whole list
in the formals and guards, but refers to individual elements of the list in the
@('element') portion.  This is similar to how other macros like @(see deflist),
@(see defalist), and @(see defmapappend) handle @('x').</p>

<h3>Usage and Arguments</h3>

<p>Let @('pkg') be the package of @('name').  All functions, theorems, and
variables are created in this package.  One of the formals must be @('pkg::x'),
and this argument represents the list that will be transformed.  Otherwise, the
only restriction on formals is that you may not use the names @('pkg::a'),
@('pkg::n'), @('pkg::y'), and @('pkg::acc'), because we use these variables in
the theorems we generate.</p>

<p>The optional @(':guard') and @(':verify-guards') are given to the
@('defund') event that we introduce.  Often @(see deflist) is convenient for
introducing the necessary guard.</p>

<p>The optional @(':nil-preservingp') argument can be set to @('t') when the
element transformation satisfies @('(element nil ...) = nil').  This allows
@('defprojection') to produce slightly better theorems.</p>

<p>The optional @(':result-type') keyword defaults to @('nil'), and in this
case no additional \"type theorem\" will be inferred.  But, if you instead give
the name of a unary predicate like @('nat-listp'), then a defthm will be
generated that looks like @('(implies (force guard) (nat-listp (name ...)))')
while @('name') is still enabled.  This is not a very general mechanism, but it
is often good enough to save a lot of work.</p>

<p>The optional @(':rest') keyword can be used to stick in additional events
after the end of the projection.  These events will be submitted after
everything else, including the @(':result-type') theorem.  The theory will have
the projection function enabled.  This is a more general but less automatic
than @(':result-type'), i.e., you typically have to include full @(see defthm)s
here.</p>

<p>The optional @(':already-definedp') keyword can be set if you have already
defined the function.  This can be used to generate all of the ordinary
@('defprojection') theorems without generating a @('defund') event, and is
useful when you are dealing with mutually recursive transformations.</p>

<p>The optional @(':mode') keyword can be set to @(':logic') or @(':program')
to introduce the recognizer in logic or program mode.  The default is whatever
the current default defun-mode is for ACL2, i.e., if you are already in program
mode, it will default to program mode, etc.</p>

<p>The optional @(':optimize') keyword can be set to @('nil') if you do not
want the projection to be optimized with @('nreverse').  This will result in a
slightly slower transformation function, but avoids a ttag.</p>

<p>The optional @(':parents'), @(':short'), and @(':long') keywords are as in
@(see defxdoc).  Typically you only need to specify @(':parents'), perhaps
implicitly with @(see xdoc::set-default-parents), and suitable documentation
will be automatically generated for @(':short') and @(':long').  If you don't
like this documentation, you can supply your own @(':short') and/or @(':long')
to override it.</p>

<p>The optional @(':parallelize') keyword can be set to @('t') if you want to
try to speed up the execution of new function using parallelism.  This is
experimental and will only work with ACL2(p).  Note that we don't do anything
smart to split the work up into large chunks, and you lose tail-recursion when
you use this.</p>")

(deftheory defprojection-theory
  (union-theories '(acl2::append-to-nil
                    acl2::append-when-not-consp
                    acl2::append-of-cons
                    acl2::associativity-of-append
                    acl2::rev-of-cons
                    acl2::rev-when-not-consp
                    acl2::revappend-removal
                    acl2::reverse-removal)
                  (union-theories (theory 'minimal-theory)
                                  (theory 'deflist-support-lemmas))))


(defun defprojection-fn (name formals element
                              nil-preservingp already-definedp
                              guard verify-guards
                              mode optimize result-type
                              parents short long rest
                              parallelize)
  (declare (xargs :mode :program))
  (b* (((unless (symbolp name))
        (er hard? 'defprojection "Name must be a symbol, but is ~x0." name))

       (mksym-package-symbol name)

       ;; Special variables that are reserved by defprojection
       (x   (intern-in-package-of-symbol "X" name))
       (a   (intern-in-package-of-symbol "A" name))
       (n   (intern-in-package-of-symbol "N" name))
       (y   (intern-in-package-of-symbol "Y" name))
       (acc (intern-in-package-of-symbol "ACC" name))

       ((unless (and (symbol-listp formals)
                     (no-duplicatesp formals)))
        (er hard 'defprojection
            "The formals must be a list of unique symbols, but the ~
            formals are ~x0." formals))

       ((unless (member x formals))
        (er hard 'defprojection
            "The formals must contain X, but are ~x0.~%" formals))

       ((unless (and (not (member a formals))
                     (not (member n formals))
                     (not (member y formals))
                     (not (member acc formals))))
        (er hard 'defprojection
            "As a special restriction, formals may not mention a, n, ~
            or y, but the formals are ~x0." formals))

       ((unless (and (consp element)
                     (symbolp (car element))))
        (er hard 'defprojection
            "The element transformation should be a function/macro call, ~
             but is ~x0." element))

       (list-fn   name)
       (list-args formals)
       (elem-fn   (car element))
       (elem-args (cdr element))
       (exec-fn   (mksym list-fn '-exec))
       (elem-syms (collect-vars elem-args))

       ((unless (variable-or-constant-listp elem-args))
        (er hard? 'defprojection
            "The element's arguments must be a function applied to the ~
             formals or constants, but are: ~x0." elem-args))

       ((unless (and (no-duplicatesp elem-syms)
                     (subsetp elem-syms formals)
                     (subsetp formals elem-syms)))
        (er hard 'defprojection
            "The variables in the :element do not agree with the formals:~% ~
              - formals: ~x0~% ~
              - element vars: ~x1~%" formals elem-syms))

       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (er hard 'defprojection
            ":mode must be one of :logic or :program, but is ~x0." mode))

       ((unless (booleanp verify-guards))
        (er hard 'defprojection
            ":verify-guards must be a boolean, but is ~x0."
            verify-guards))

       ((unless (booleanp nil-preservingp))
        (er hard 'defprojection
            ":nil-preservingp must be a boolean, but is ~x0."
            nil-preservingp))

       ((unless (booleanp already-definedp))
        (er hard 'defprojection
            ":already-definedp must be a boolean, but is ~x0."
            already-definedp))

       ((unless (booleanp optimize))
        (er hard 'defprojection
            ":optimize must be a boolean, but is ~x0."
            optimize))

       ((unless (symbolp result-type))
        (er hard 'defprojection
            ":result-type must be a symbol, but is ~x0."
            result-type))

       (short (or short
                  (and parents
                       (str::cat "@(call " (symbol-name list-fn) ") maps "
                                 "@(see " (symbol-package-name elem-fn)
                                 "::" (symbol-name elem-fn) ") across a list."))))

       (long (or long
                 (and parents
                      (str::cat "<p>This is an ordinary @(see defprojection).</p>"))))

       (def  (if already-definedp
                 nil
               `((defund ,exec-fn (,@list-args ,acc)
                   (declare (xargs :guard
                                   ;; Previously we required that acc was a
                                   ;; true-listp in the guard.  But on reflection,
                                   ;; this really isn't necessary, and omitting it
                                   ;; can simplify the guards of other functions
                                   ;; that are directly calling -exec functions.

                                   ;; ,(if (equal guard t)
                                   ;;      `(true-listp ,acc)
                                   ;;    `(and (true-listp ,acc)
                                   ;;          ,guard))
                                   ,guard

                                   :mode ,mode
                                   ;; we tell ACL2 not to normalize because
                                   ;; otherwise type reasoning can rewrite the
                                   ;; definition, and ruin some of our theorems
                                   ;; below, e.g., when ELEMENT is known to be
                                   ;; zero always.
                                   :normalize nil
                                   :verify-guards nil))
                   (if (consp ,x)
                       (,exec-fn ,@(subst `(cdr ,x) x list-args)
                                 (cons (,elem-fn ,@(subst `(car ,x) x elem-args))
                                       ,acc))
                     ,acc))

                 (defund ,list-fn (,@list-args)
                   (declare (xargs :guard ,guard
                                   :mode ,mode
                                   ;; we tell ACL2 not to normalize because
                                   ;; otherwise type reasoning can rewrite the
                                   ;; definition, and ruin some of our theorems
                                   ;; below, e.g., when ELEMENT is known to be
                                   ;; zero.
                                   :normalize nil
                                   :verify-guards nil))
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
                            (reverse (,exec-fn ,@list-args nil))))))))

       (ndef      `(defun ,list-fn (,@list-args)
                     (nreverse (,exec-fn ,@list-args nil))))

       (opt       (and optimize
                       (not already-definedp)
                       `((progn
                           (make-event
                            (if (acl2::global-val
                                 'acl2::include-book-path (w state))
                                ;; We're in an include book.  Don't print.
                                (value '(value-triple :invisible))
                              (value
                               '(value-triple
                                 (cw "~|~%Optimizing definition of ~s0:~%  ~p1~%~%"
                                     ',list-fn ',ndef)))))
                           (defttag std-optimize)
                           ;; To justify nreverse, exec-fn must never be memoized
                           (never-memoize ,exec-fn)
                           (progn! (set-raw-mode t)
                                   ,ndef)
                           (defttag nil)))))

       ((when (eq mode :program))
        `(defsection ,name
           ,@(and parents `(:parents ,parents))
           ,@(and short   `(:short ,short))
           ,@(and long    `(:long ,long))
           (program)
           ,@def
           ,@opt
           ,@rest))

       (listp-when-not-consp  (mksym list-fn '-when-not-consp))
       (listp-of-cons         (mksym list-fn '-of-cons))
       (listp-nil-preservingp (mksym list-fn '-nil-preservingp-lemma))

       (main-thms
        `(,@(and nil-preservingp
                 `((local (maybe-defthm-as-rewrite
                           ,listp-nil-preservingp
                           (equal (,elem-fn ,@(subst ''nil x elem-args))
                                  nil)
                           ;; We just rely on the user to be able to prove this
                           ;; in their current theory.
                           ))))

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

          (defthm ,listp-when-not-consp
            (implies (not (consp ,x))
                     (equal (,list-fn ,@list-args)
                            nil))
            :hints(("Goal"
                    :in-theory
                    (union-theories '(,list-fn)
                                    (theory 'defprojection-theory)))))

          (defthm ,listp-of-cons
            (equal (,list-fn ,@(subst `(cons ,a ,x) x list-args))
                   (cons (,elem-fn ,@(subst a x elem-args))
                         (,list-fn ,@list-args)))
            :hints(("Goal"
                    :in-theory
                    (union-theories '(,list-fn)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym 'true-listp-of- list-fn)
            (equal (true-listp (,list-fn ,@list-args))
                   t)
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym 'len-of- list-fn)
            (equal (len (,list-fn ,@list-args))
                   (len ,x))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym 'consp-of- list-fn)
            (equal (consp (,list-fn ,@list-args))
                   (consp ,x))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym 'car-of- list-fn)
            (equal (car (,list-fn ,@list-args))
                   ,(if nil-preservingp
                        `(,elem-fn ,@(subst `(car ,x) x elem-args))
                      `(if (consp ,x)
                           (,elem-fn ,@(subst `(car ,x) x elem-args))
                         nil)))
            :hints(("Goal"
                    :in-theory
                    (union-theories '(,listp-when-not-consp
                                      ,listp-of-cons
                                      . ,(and nil-preservingp
                                              `(,listp-nil-preservingp
                                                acl2::default-car)))
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym 'cdr-of- list-fn)
            (equal (cdr (,list-fn ,@list-args))
                   (,list-fn ,@(subst `(cdr ,x) x list-args)))
            :hints(("Goal"
                    :in-theory
                    (union-theories '(,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))


          (defthm ,(mksym list-fn '-under-iff)
            (iff (,list-fn ,@list-args)
                 (consp ,x))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym list-fn '-of-list-fix)
            (equal (,list-fn ,@(subst `(list-fix ,x) x list-args))
                   (,list-fn ,@list-args))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym list-fn '-of-append)
            (equal (,list-fn ,@(subst `(append ,x ,y) x list-args))
                   (append (,list-fn ,@list-args)
                           (,list-fn ,@(subst y x list-args))))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym list-fn '-of-rev)
            (equal (,list-fn ,@(subst `(rev ,x) x list-args))
                   (rev (,list-fn ,@list-args)))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(,(mksym list-fn '-of-append)
                                      ,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym list-fn '-of-revappend)
            (equal (,list-fn ,@(subst `(revappend ,x ,y) x list-args))
                   (revappend (,list-fn ,@list-args)
                              (,list-fn ,@(subst y x list-args))))
            :hints(("Goal" :in-theory
                    (union-theories '(,(mksym list-fn '-of-append)
                                      ,(mksym list-fn '-of-rev))
                                    (theory 'defprojection-theory)))))

          ,@(if nil-preservingp
                `((defthm ,(mksym 'take-of- list-fn)
                    (equal (take ,n (,list-fn ,@list-args))
                           (,list-fn ,@(subst `(take ,n ,x) x list-args)))
                    :hints(("Goal"
                            :induct (take ,n ,x)
                            :in-theory
                            (union-theories '(acl2::take-redefinition
                                              ,listp-when-not-consp
                                              ,listp-of-cons
                                              . ,(and nil-preservingp
                                                      `(,listp-nil-preservingp
                                                        acl2::default-car)))
                                            (theory 'defprojection-theory))))))
              nil)

          (defthm ,(mksym 'nthcdr-of- list-fn)
            (equal (nthcdr ,n (,list-fn ,@list-args))
                   (,list-fn ,@(subst `(nthcdr ,n ,x) x list-args)))
            :hints(("Goal"
                    :induct (nthcdr ,n ,x)
                    :in-theory
                    (union-theories '(nthcdr
                                      ,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym 'member-equal-of- elem-fn '-in- list-fn '-when-member-equal)
            (implies (member-equal ,a (double-rewrite ,x))
                     (member-equal (,elem-fn ,@(subst a x elem-args))
                                   (,list-fn ,@list-args)))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(member-equal
                                      ,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          (defthm ,(mksym 'subsetp-equal-of- list-fn 's-when-subsetp-equal)
            (implies (subsetp-equal (double-rewrite ,x)
                                    (double-rewrite ,y))
                     (subsetp-equal (,list-fn ,@list-args)
                                    (,list-fn ,@(subst y x list-args))))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory
                    (union-theories '(subsetp-equal
                                      ,(mksym 'member-equal-of- elem-fn
                                              '-in- list-fn '-when-member-equal)
                                      ,listp-when-not-consp
                                      ,listp-of-cons)
                                    (theory 'defprojection-theory)))))

          ,@(if nil-preservingp
                `((defthm ,(mksym 'nth-of- list-fn)
                    (equal (nth ,n (,list-fn ,@list-args))
                           (,elem-fn ,@(subst `(nth ,n ,x) x elem-args)))
                    :hints(("Goal"
                            :induct (nth ,n ,x)
                            :in-theory
                            (union-theories '(nth
                                              ,listp-when-not-consp
                                              ,listp-of-cons
                                              . ,(and nil-preservingp
                                                      `(,listp-nil-preservingp
                                                        acl2::default-car)))
                                            (theory 'defprojection-theory))))))
              nil)

          ,@(if already-definedp
                nil
              `((defthm ,(mksym exec-fn '-removal)
                  ;; we don't need the hyp... (implies (force (true-listp ,acc))
                  (equal (,exec-fn ,@list-args ,acc)
                         (revappend (,list-fn ,@list-args) ,acc))
                  :hints(("Goal"
                          :induct (,exec-fn ,@list-args ,acc)
                          :in-theory
                          (union-theories '(,exec-fn
                                            ,listp-when-not-consp
                                            ,listp-of-cons)
                                          (theory 'defprojection-theory)))))))


          )))

    `(defsection ,name
       ,@(and parents `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))
       (logic)
       ,@def
       (set-inhibit-warnings "disable") ;; implicitly local
       ,@main-thms
       ,@(and (not already-definedp)
              verify-guards
              `((verify-guards ,exec-fn
                  :hints(("Goal"
                          :in-theory
                          (union-theories '(,exec-fn)
                                          (theory 'defprojection-theory)))
                         (and stable-under-simplificationp
                              '(:in-theory (enable )))))
                (verify-guards ,list-fn
                  :hints(("Goal"
                          :in-theory
                          (union-theories '(,list-fn
                                            ,(mksym exec-fn '-removal)
                                            ,(mksym 'true-listp-of- list-fn)
                                            acl2::reverse-removal
                                            acl2::revappend-removal
                                            acl2::rev-of-append
                                            acl2::rev-of-rev)
                                          (theory 'defprojection-theory)))
                         (and stable-under-simplificationp
                              '(:in-theory (enable )))))))
       ,@opt
       (local (in-theory (enable ,list-fn
                                 ,listp-when-not-consp
                                 ,listp-of-cons)))
       ,@(and result-type
              `((defthm ,(mksym result-type '-of- list-fn)
                  ,(if (eq guard t)
                       `(,result-type (,list-fn ,@list-args))
                     `(implies (force ,guard)
                               (,result-type (,list-fn ,@list-args))))
                  :hints(("Goal"
                          :induct (len ,x)
                          :in-theory (enable (:induction len)))))))
       . ,rest)))

(defmacro defprojection (name formals element &key nil-preservingp already-definedp
                              (optimize 't)
                              result-type
                              (guard 't)
                              (verify-guards 't)
                              mode
                              (parents 'nil parents-p)
                              (short 'nil)
                              (long 'nil)
                              (rest 'nil)
                              (parallelize 'nil))
  `(make-event (let ((mode    (or ',mode (default-defun-mode (w state))))
                     (parents (if ',parents-p
                                  ',parents
                                (or (xdoc::get-default-parents (w state))
                                    '(acl2::undocumented)))))
                 (defprojection-fn ',name ',formals ',element
                   ',nil-preservingp ',already-definedp
                   ',guard ',verify-guards
                   mode ',optimize ',result-type
                   parents ',short ',long ',rest
                   ',parallelize))))
