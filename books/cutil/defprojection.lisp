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

(in-package "CUTIL")
(include-book "deflist")


(defxdoc defprojection
  :parents (cutil)
  :short "Project a transformation across a list."

  :long "<p>Defprojection allows you to quickly introduce a function like
<tt>map f</tt>.  That is, given an element-transforming function, <tt>f</tt>,
it can define a new function that applies <tt>f</tt> to every element in a
list.</p>

<p>General form:</p>

<code>
 (defprojection name formals
   element
   &amp;key guard                   ; t by default
        verify-guards           ; t by default
        nil-preservingp         ; nil by default
        result-type             ; nil by default
        already-definedp        ; nil by default
        mode                    ; current defun-mode by default
        optimize                ; t by default
        result-type             ; nil by default
        parents                 ; '(acl2::undocumented) by default
        short                   ; nil by default
        long                    ; nil by default
        )
</code>

<p>For example,</p>

<code>
 (defprojection my-strip-cars (x)
   (car x)
   :guard (alistp x))
</code>

<p>defines a new function, <tt>my-strip-cars</tt>, that is like the built-in
ACL2 function <tt>strip-cars</tt>.</p>

<p>Note that <b>x</b> is treated in a special way: it refers to the whole list
in the formals and guards, but refers to individual elements of the list in the
<tt>element</tt> portion.  This is similar to how other macros like @(see
deflist), @(see defalist), and @(see defmapappend) handle <tt>x</tt>.</p>

<h3>Usage and Arguments</h3>

<p>Let <tt>pkg</tt> be the package of <tt>name</tt>.  All functions, theorems,
and variables are created in this package.  One of the formals must be
<tt>pkg::x</tt>, and this argument represents the list that will be
transformed.  Otherwise, the only restriction on formals is that you may not
use the names <tt>pkg::a</tt>, <tt>pkg::n</tt>, <tt>pkg::y</tt>, and
<tt>pkg::acc</tt>, because we use these variables in the theorems we
generate.</p>

<p>The optional <tt>:guard</tt> and <tt>:verify-guards</tt> are given to the
<tt>defund</tt> event that we introduce.  Often @(see deflist) is convenient
for introducing the necessary guard.</p>

<p>The optional <tt>:nil-preservingp</tt> argument can be set to <tt>t</tt>
when the element transformation satisfies <tt>(element nil ...) = nil</tt>.
This allows <tt>defprojection</tt> to produce slightly better theorems.</p>

<p>The optional <tt>:result-type</tt> keyword defaults to <tt>nil</tt>, and in
this case no additional \"type theorem\" will be inferred.  But, if you instead
give the name of a unary predicate like <tt>nat-listp</tt>, then a defthm will
be generated that looks like <tt>(implies (force guard) (nat-listp (name
...)))</tt> while <tt>name</tt> is still enabled.  This is not a very general
mechanism, but it is often good enough to save a lot of work.</p>

<p>The optional <tt>:already-definedp</tt> keyword can be set if you have
already defined the function.  This can be used to generate all of the ordinary
<tt>defprojection</tt> theorems without generating a <tt>defund</tt> event, and
is useful when you are dealing with mutually recursive transformations.</p>

<p>The optional <tt>:mode</tt> keyword can be set to <tt>:logic</tt> or
<tt>:program</tt> to introduce the recognizer in logic or program mode.  The
default is whatever the current default defun-mode is for ACL2, i.e., if you
are already in program mode, it will default to program mode, etc.</p>

<p>The optional <tt>:optimize</tt> keyword can be set to <tt>nil</tt> if you do
not want the projection to be optimized with <tt>nreverse</tt>.  This will
result in a slightly slower transformation function, but avoids a ttag.</p>

<p>The optional <tt>:parents</tt>, <tt>:short</tt>, and <tt>:long</tt> keywords
are as in @(see defxdoc).  Typically you only need to specify
<tt>:parents</tt>, and suitable documentation will be automatically generated
for <tt>:short</tt> and <tt>:long</tt>.  If you don't like this documentation,
you can supply your own <tt>:short</tt> and/or <tt>:long</tt> to override
it.</p>")

(defthmd defprojection-append-of-nil
  (implies (true-listp a)
           (equal (append a nil) a)))

(defthmd defprojection-associativity-of-append
  (equal (append (append x y) z)
         (append x (append y z))))

(defun defprojection-fn (name formals element
                              nil-preservingp already-definedp
                              guard verify-guards
                              mode optimize result-type
                              parents short long)
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
            "The element transformation must be a function applied ~
            to the formals, but is ~x0." element))

       (list-fn   name)
       (list-args formals)
       (elem-fn   (car element))
       (elem-args (cdr element))
       (exec-fn   (mksym list-fn '-exec))

       ((unless (and (symbol-listp elem-args)
                     (no-duplicatesp elem-args)
                     (subsetp elem-args formals)
                     (subsetp formals elem-args)))
        (er hard 'defprojection
            "The element transformation's formals do not agree with ~
             the list transformation's formals."))

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
                                 "@(see " (symbol-name elem-fn) ") across a list."))))

       (long (or long
                 (and parents
                      (str::cat "<p>This is an ordinary @(see defprojection).</p>"
                                "@(def " (symbol-name list-fn) ")"))))

       (doc (if (or parents short long)
                `((defxdoc ,name :parents ,parents :short ,short :long ,long))
              nil))

       (def  (if already-definedp
                 nil
               `((defun ,exec-fn (,@list-args ,acc)
                   (declare (xargs :guard ,(if (equal guard t)
                                               `(true-listp ,acc)
                                             `(and (true-listp ,acc)
                                                   ,guard))
                                   :mode ,mode
                                   :verify-guards nil))
                   (if (consp ,x)
                       (,exec-fn ,@(subst `(cdr ,x) x list-args)
                                 (cons (,elem-fn ,@(subst `(car ,x) x elem-args))
                                       ,acc))
                     ,acc))

                 (defun ,list-fn (,@list-args)
                   (declare (xargs :guard ,guard
                                   :mode ,mode
                                   :verify-guards nil))
                   (mbe :logic
                        (if (consp ,x)
                            (cons (,elem-fn ,@(subst `(car ,x) x elem-args))
                                  (,list-fn ,@(subst `(cdr ,x) x list-args)))
                          nil)
                        :exec
                        (reverse (,exec-fn ,@list-args nil)))))))

       (ndef      `(defun ,list-fn (,@list-args)
                     (nreverse (,exec-fn ,@list-args nil))))

       (opt       (if (or already-definedp (not optimize))
                      nil
                    `((progn
                        (make-event
                         (if (acl2::global-val 'acl2::include-book-path (w state))
                             ;; We're in an include book.  Don't print.
                             (value '(value-triple :invisible))
                           (value '(value-triple
                                    (cw "~|~%Optimizing definition of ~s0:~%  ~p1~%~%"
                                        ',list-fn ',ndef)))))
                        (defttag cutil-optimize)
                        (progn!
                         (set-raw-mode t)
                         ;; Never allow exec function to be memoized, to justify nreverse
                         (setf (gethash ',exec-fn ACL2::*never-profile-ht*) t)
                         ,ndef)
                        (defttag nil)))))

       ((when (eq mode :program))
        `(encapsulate
           ()
           (program)
           ,@doc
           ,@def
           ,@opt)))

      `(encapsulate
        ()
        (logic)

        ,@doc
        ,@def

        ,@(if already-definedp
              nil
            `((in-theory (disable ,list-fn ,exec-fn))))

        (local (in-theory (enable defprojection-append-of-nil
                                  defprojection-associativity-of-append)))

        (defthm ,(mksym list-fn '-when-not-consp)
          (implies (not (consp ,x))
                   (equal (,list-fn ,@list-args)
                          nil))
          :hints(("Goal" :in-theory (enable ,list-fn))))

        (defthm ,(mksym list-fn '-of-cons)
          (equal (,list-fn ,@(subst `(cons ,a ,x) x list-args))
                 (cons (,elem-fn ,@(subst a x elem-args))
                       (,list-fn ,@list-args)))
          :hints(("Goal" :in-theory (enable ,list-fn))))

        (defthm ,(mksym 'true-listp-of- list-fn)
          (equal (true-listp (,list-fn ,@list-args))
                 t)
          :hints(("Goal" :induct (len ,x))))

        (defthm ,(mksym 'len-of- list-fn)
          (equal (len (,list-fn ,@list-args))
                 (len ,x))
          :hints(("Goal" :induct (len ,x))))

        (defthm ,(mksym 'consp-of- list-fn)
          (equal (consp (,list-fn ,@list-args))
                 (consp ,x))
          :hints(("Goal" :induct (len ,x))))

        (defthm ,(mksym 'car-of- list-fn)
          (equal (car (,list-fn ,@list-args))
                 ,(if nil-preservingp
                      `(,elem-fn ,@(subst `(car ,x) x elem-args))
                    `(if (consp ,x)
                         (,elem-fn ,@(subst `(car ,x) x elem-args))
                       nil))))

        (defthm ,(mksym 'cdr-of- list-fn)
          (equal (cdr (,list-fn ,@list-args))
                 (,list-fn ,@(subst `(cdr ,x) x list-args))))

        (defthm ,(mksym list-fn '-under-iff)
          (iff (,list-fn ,@list-args)
               (consp ,x))
          :hints(("Goal" :induct (len ,x))))

        (defthm ,(mksym list-fn '-of-list-fix)
          (equal (,list-fn ,@(subst `(list-fix ,x) x list-args))
                 (,list-fn ,@list-args))
          :hints(("Goal" :induct (len ,x))))

        (defthm ,(mksym list-fn '-of-append)
          (equal (,list-fn ,@(subst `(append ,x ,y) x list-args))
                 (append (,list-fn ,@list-args)
                         (,list-fn ,@(subst y x list-args))))
          :hints(("Goal" :induct (len ,x))))

        (defthm ,(mksym list-fn '-of-rev)
          (equal (,list-fn ,@(subst `(rev ,x) x list-args))
                 (rev (,list-fn ,@list-args)))
          :hints(("Goal" :induct (len ,x))))

        (defthm ,(mksym list-fn '-of-revappend)
          (equal (,list-fn ,@(subst `(revappend ,x ,y) x list-args))
                 (revappend (,list-fn ,@list-args)
                            (,list-fn ,@(subst y x list-args)))))

        ,@(if nil-preservingp
              `((defthm ,(mksym 'simpler-take-of- list-fn)
                  (equal (simpler-take ,n (,list-fn ,@list-args))
                         (,list-fn ,@(subst `(simpler-take ,n ,x) x list-args)))
                  :hints(("Goal"
                          :in-theory (enable simpler-take)
                          :induct (simpler-take ,n ,x)))))
            nil)

        (defthm ,(mksym 'nthcdr-of- list-fn)
          (equal (nthcdr ,n (,list-fn ,@list-args))
                 (,list-fn ,@(subst `(nthcdr ,n ,x) x list-args)))
          :hints(("Goal"
                  :in-theory (enable nthcdr)
                  :induct (nthcdr ,n ,x))))

        (defthm ,(mksym 'member-equal-of- elem-fn '-in- list-fn '-when-member-equal)
          (implies (member-equal ,a (double-rewrite ,x))
                   (member-equal (,elem-fn ,@(subst a x elem-args))
                                 (,list-fn ,@list-args)))
          :hints(("Goal" :induct (len ,x))))

        (defthm ,(mksym 'subsetp-equal-of- list-fn 's-when-subsetp-equal)
          (implies (subsetp-equal (double-rewrite ,x)
                                  (double-rewrite ,y))
                   (subsetp-equal (,list-fn ,@list-args)
                                  (,list-fn ,@(subst y x list-args))))
          :hints(("Goal"
                  ;; bleh
                  :in-theory (enable subsetp-equal)
                  :induct (len ,x))))

        ,@(if nil-preservingp
              `((defthm ,(mksym 'nth-of- list-fn)
                  (equal (nth ,n (,list-fn ,@list-args))
                         (,elem-fn ,@(subst `(nth ,n ,x) x elem-args)))
                  :hints(("Goal"
                          :in-theory (enable nth)
                          :induct (nth ,n ,x)))))
            nil)

        ,@(if already-definedp
              nil
            `((defthm ,(mksym exec-fn '-removal)
                (implies (force (true-listp ,acc))
                         (equal (,exec-fn ,@list-args ,acc)
                                (revappend (,list-fn ,@list-args) ,acc)))
                :hints(("Goal" :in-theory (enable ,exec-fn))))

              ,@(if verify-guards
                    `((verify-guards ,exec-fn)
                      (verify-guards ,list-fn))
                  nil)))

        ,@(and result-type
               `((defthm ,(mksym result-type '-of- list-fn)
                   ,(if (eq guard t)
                        `(,result-type (,list-fn ,@list-args))
                      `(implies (force ,guard)
                                (,result-type (,list-fn ,@list-args))))
                   :hints(("Goal"
                           :induct (len ,x)
                           :in-theory (enable (:induction len)))))))

        ,@opt

      )))

(defmacro defprojection (name formals element &key nil-preservingp already-definedp
                              (optimize 't)
                              result-type
                              (guard 't)
                              (verify-guards 't)
                              mode
                              (parents '(acl2::undocumented))
                              (short 'nil)
                              (long 'nil))
  `(make-event (let ((mode (or ',mode (default-defun-mode (w state)))))
                 (defprojection-fn ',name ',formals ',element
                   ',nil-preservingp ',already-definedp
                   ',guard ',verify-guards
                   mode ',optimize ',result-type
                   ',parents ',short ',long))))
