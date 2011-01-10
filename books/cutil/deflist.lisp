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
(include-book "tools/bstar" :dir :system)
(include-book "str/cat" :dir :system)
(include-book "finite-set-theory/osets/sets" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(include-book "unicode/list-fix" :dir :system)
(include-book "unicode/take" :dir :system)
(include-book "unicode/repeat" :dir :system)
(include-book "unicode/rev" :dir :system)
(local (include-book "deflist-aux"))

(defxdoc deflist
  :parents (cutil)
  :short "Introduce a recognizer for a typed list."

  :long "<p>Deflist allows you to quickly introduce a recognizer for a typed
list (e.g., <tt>nat-listp</tt>), and proves basic theorems about it.</p>

<p>Unlike many ACL2 list recognizers, the recognizers introduced by
<tt>deflist</tt> do not require that the list be nil-terminated.  We think this
behavior is better with regards to the so-called <i>list-fix convention</i>: a
function that expects a list should ignore the final cdr of the list.</p>

<p>General form:</p>

<code>
 (deflist name formals
   element
   &amp;key guard               ; t by default
        verify-guards       ; t by default
        already-definedp    ; nil by default
        negatedp            ; nil by default
        mode                ; current defun-mode by default
        parents             ; '(acl2::undocumented) by default
        short               ; nil by default
        long                ; nil by default
        )
</code>

<p>For example,</p>

<code>
 (deflist my-integer-listp (x)
   (integerp x))
</code>

<p>introduces a new function, <tt>my-integer-listp</tt>, which recognizes lists
whose every element satisfies <tt>integerp</tt>, and also introduces many
theorems about this new function.</p>

<p>Note that <b>x</b> is treated in a special way: it refers to the whole list
in the formals and guards, but refers to individual elements of the list in the
<tt>element</tt> portion.  This is similar to how other macros like @(see
defalist), @(see defprojection), and @(see defmapappend) handle <tt>x</tt>.</p>

<h3>Usage and Arguments</h3>

<p>Let <tt>pkg</tt> be the package of <tt>name</tt>.  All functions, theorems,
and variables are created in this package.  One of the formals must be
<tt>pkg::x</tt>, and this argument represents the list to check.  Otherwise,
the only restriction on the formals is that you may not use the names
<tt>pkg::a</tt>, <tt>pkg::n</tt>, or <tt>pkg::y</tt>, because we use these
variables in the theorems we generate.</p>

<p>The optional <tt>:guard</tt> and <tt>:verify-guards</tt> are given to the
<tt>defund</tt> event that we introduce.  In other words, these are the guards
that will be used for the list recognizer, not the element recognizer.</p>

<p>The optional <tt>:already-definedp</tt> keyword can be set if you have
already defined the function.  This can be used to generate all of the ordinary
<tt>deflist</tt> theorems without generating a <tt>defund</tt> event, and is
useful when you are dealing with mutually recursive recognizers.</p>

<p>The optional <tt>:value-of-nil</tt> keyword can be used when <tt>(elementp
nil ...)</tt> is always known to be <tt>t</tt> or <tt>nil</tt>.  When it is
provided, <tt>deflist</tt> can generate slightly better theorems.</p>

<p>The optional <tt>:negatedp</tt> keyword can be used to recognize a list
whose every element does not satisfy elementp.</p>

<p>The optional <tt>:mode</tt> keyword can be set to <tt>:logic</tt> or
<tt>:program</tt> to introduce the recognizer in logic or program mode.  The
default is whatever the current default defun-mode is for ACL2, i.e., if you
are already in program mode, it will default to program mode, etc.</p>

<p>The optional <tt>:parents</tt>, <tt>:short</tt>, and <tt>:long</tt> keywords
are as in @(see defxdoc).  Typically you only need to specify
<tt>:parents</tt>, and suitable documentation will be automatically generated
for <tt>:short</tt> and <tt>:long</tt>.  If you don't like this documentation,
you can supply your own <tt>:short</tt> and/or <tt>:long</tt> to override
it.</p>


<h3>More Examples</h3>

<p>Recognizing a list with no natural numbers:</p>

<code>
 (deflist nat-free-listp (x)
   (natp x)
   :negatedp t)
</code>

<p>Recognizing lists whose elements exceed some minimum:</p>

<code>
 (deflist all-greaterp (min x)
   (> x min)
   :guard (and (natp n)
               (nat-listp x)))
</code>")


(defthmd deflist-lemma-1
  (iff (member-equal (car x) x)
       (consp x)))

(encapsulate
  ()
  (local (include-book "finite-set-theory/osets/set-order" :dir :system))

  (local (defthm sets-in-list-as-member-equal
           (equal (sets::in-list a x)
                  (if (member-equal a x)
                      t
                    nil))
           :hints(("Goal" :in-theory (enable sets::in-list)))))

  (local (defthm member-equal-is-in
           (implies (setp x)
                    (iff (member-equal a x)
                         (in a x)))
           :hints(("Goal" :in-theory (enable sets::primitive-reasoning)))))

  (local (defthm member-equal-of-append
           (iff (member-equal a (append x y))
                (or (member-equal a x)
                    (member-equal a y)))))

  (defthmd deflist-lemma-2
    (and (subsetp-equal (mergesort x) x)
         (subsetp-equal x (mergesort x))))

  (defthmd deflist-lemma-3
    (subsetp-equal (difference x y) x))

  (defthmd deflist-lemma-4
    (and (subsetp-equal (intersect x y) x)
         (subsetp-equal (intersect x y) y))
    :hints(("Goal" :in-theory (enable sets::primitive-reasoning
                                      subsetp-equal))))

  (defthmd deflist-lemma-5
    (subsetp-equal (union x y) (append x y)))

  (defthmd deflist-lemma-6
    (subsetp-equal (duplicated-members x) x)))


(defun concatenate-symbol-names (x)
  (declare (xargs :guard (symbol-listp x)))
  (if (consp x)
      (acl2::concatenate 'string
                         (symbol-name (car x))
                         (concatenate-symbol-names (cdr x)))
    ""))

(defmacro mksym (&rest args)
  `(intern-in-package-of-symbol
    (concatenate-symbol-names (list ,@args))
    mksym-package-symbol))

(defun deflist-fn (name formals element negatedp guard verify-guards
                        already-definedp elementp-of-nil mode
                        parents short long)
  (declare (xargs :mode :program))
  (b* (((unless (symbolp name))
        (er hard 'deflist "Name must be a symbol, but is ~x0." name))

       (mksym-package-symbol name)

       ;; Special variables that are reserved by deflist.
       (x (intern-in-package-of-symbol "X" name))
       (a (intern-in-package-of-symbol "A" name))
       (n (intern-in-package-of-symbol "N" name))
       (y (intern-in-package-of-symbol "Y" name))

       ((unless (and (symbol-listp formals)
                     (no-duplicatesp formals)))
        (er hard 'deflist
            "The formals must be a list of unique symbols, but the ~
            formals are ~x0." formals))

       ((unless (member x formals))
        (er hard 'deflist
            "The formals must contain X, but are ~x0.~%" formals))

       ((unless (and (not (member a formals))
                     (not (member n formals))
                     (not (member y formals))))
        (er hard 'deflist
            "As a special restriction, formals may not mention a, n, ~
            or y, but the formals are ~x0." formals))

       ((unless (and (consp element)
                     (symbolp (car element))))
        (er hard 'deflist
            "The element recognizer must be a function applied ~
            to the formals, but is ~x0." element))
       (elementp     (car element))
       (elem-formals (cdr element))

       ((unless (booleanp negatedp))
        (er hard 'deflist
            ":negatedp must be a boolean, but is ~x0."
            negatedp))

       ((unless (booleanp verify-guards))
        (er hard 'deflist
            ":verify-guards must be a boolean, but is ~x0."
            verify-guards))

       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (er hard 'deflist
            ":mode must be one of :logic or :program, but is ~x0." mode))

       ((unless (or (eq mode :logic)
                    (not already-definedp)))
        (er hard 'deflist
            ":mode :program and already-definedp cannot be used together."))

       ((unless (member elementp-of-nil '(t nil :unknown)))
        (er hard 'deflist
            ":elementp-of-nil must be t, nil, or :unknown"))

       (short (or short
                  (and parents
                       (str::cat "@(call " (symbol-name name)
                                 ") recognizes lists where every element "
                                 (if negatedp
                                     "is rejected by "
                                   "satisfies ")
                                 "@(see " (symbol-name elementp) ")."))))

       (long (or long
                 (and parents
                      (str::cat "<p>This is an ordinary @(see deflist).</p>"
                                "@(def " (symbol-name name) ")"))))

       (doc (if (or parents short long)
                `((defxdoc ,name :parents ,parents :short ,short :long ,long))
              nil))

       (def (if already-definedp
                nil
              `((defund ,name (,@formals)
                  (declare (xargs :guard ,guard
                                  ,@(and (eq mode :logic)
                                         `(:verify-guards ,verify-guards))))
                  (if (consp ,x)
                      (and ,(if negatedp
                                `(not (,elementp ,@(subst `(car ,x) x elem-formals)))
                              `(,elementp ,@(subst `(car ,x) x elem-formals)))
                           (,name ,@(subst `(cdr ,x) x formals)))
                    t)))))

       (last-ditch-hint
        `(and stable-under-simplificationp
              '(:in-theory (enable ,(mksym name '-last-ditch-rules)))))

       ((when (eq mode :program))
        `(encapsulate
           ()
           (program)
           ,@doc
           ,@def)))

    `(encapsulate
       ()
       (logic)

       (set-inhibit-warnings "theory" "free" "non-rec") ;; Note: implicitly local

       ,@doc
       ,@def

       (local (in-theory (theory 'minimal-theory)))
       (local (in-theory (enable car-cons cdr-cons car-cdr-elim
                                 zp len natp
                                 acl2::take-redefinition
                                 deflist-lemma-1
                                 deflist-lemma-2
                                 deflist-lemma-3
                                 deflist-lemma-4
                                 ;; not 5.
                                 deflist-lemma-6
                                 )))

       (local (deftheory ,(mksym name '-last-ditch-rules)
                (set-difference-equal (current-theory ',name)
                                      (current-theory :here))))

       ;; (local (make-event
       ;;         (prog2$
       ;;          (cw "LAST-DITCH-RULES: ~x0.~%"
       ;;              (let ((world (w state)))
       ;;                (theory '(mksym name '-last-ditch-rules))))
       ;;          (value '(value-triple :invisible)))))

       (defthm ,(mksym name '-when-not-consp)
         (implies (not (consp ,x))
                  (equal (,name ,@formals)
                         t))
         :hints(("Goal" :in-theory (enable ,name))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-cons)
         (equal (,name ,@(subst `(cons ,a ,x) x formals))
                (and ,(if negatedp
                          `(not (,elementp ,@(subst a x elem-formals)))
                        `(,elementp ,@(subst a x elem-formals)))
                     (,name ,@formals)))
         :hints(("Goal" :in-theory (enable ,name))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-list-fix)
         (equal (,name ,@(subst `(list-fix ,x) x formals))
                (,name ,@formals))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable list-fix))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-append)
         (equal (,name ,@(subst `(append ,x ,y) x formals))
                (and (,name ,@formals)
                     (,name ,@(subst y x formals))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable append))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-rev)
         (equal (,name ,@(subst `(rev ,x) x formals))
                (,name ,@formals))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable rev))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-revappend)
         (equal (,name ,@(subst `(revappend ,x ,y) x formals))
                (and (,name ,@formals)
                     (,name ,@(subst y x formals))))
         :hints(("Goal"
                 :induct (revappend ,x ,y)
                 :in-theory (enable revappend))
                ,last-ditch-hint))

       (defthm ,(mksym elementp '-of-car-when- name)
         (implies (,name ,@formals)
                  (equal (,elementp ,@(subst `(car ,x) x elem-formals))
                         ,(cond ((equal elementp-of-nil nil)
                                 (if negatedp
                                     ;; If x is a cons, then its car is not an element.
                                     ;; Else its car is nil, which is not an element.
                                     nil
                                   ;; If x is a cons, then its car is an element.
                                   ;; Else its car is nil, which is not an element.
                                   `(consp ,x)))
                                ((equal elementp-of-nil t)
                                 (if negatedp
                                     ;; If x is a cons, then its car is not an element.
                                     ;; Else its car is nil, which is an element.
                                     `(not (consp ,x))
                                   ;; If x is a cons, then its car is an element.
                                   ;; Else its car is nil, which is an element.
                                   t))
                                (t ;; elementp-of-nil is :unknown
                                 `(if (consp ,x)
                                      ,(not negatedp)
                                    (,elementp ,@(subst nil x elem-formals)))))))
         :hints(,last-ditch-hint))

       (defthm ,(mksym name '-of-cdr-when- name)
         (implies (,name ,@formals)
                  (equal (,name ,@(subst `(cdr ,x) x formals))
                         t))
         :hints(,last-ditch-hint))

       (defthm ,(mksym elementp '-when-member-equal-of- name)
         (implies (and (,name ,@formals)
                       (member-equal ,a (double-rewrite ,x)))
                  (equal (,elementp ,@(subst a x elem-formals))
                         ,(not negatedp)))
         :rule-classes ((:rewrite)
                        (:rewrite :corollary
                                  (implies (and (member-equal ,a (double-rewrite ,x))
                                                (,name ,@formals))
                                           (equal (,elementp ,@(subst a x elem-formals))
                                                  ,(not negatedp)))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable member-equal))
                ,last-ditch-hint))


       (defthm ,(mksym name '-when-subsetp-equal)
         (implies (and (,name ,@(subst y x formals))
                       (subsetp-equal (double-rewrite ,x)
                                      (double-rewrite ,y)))
                  (equal (,name ,@formals)
                         t))
         :rule-classes ((:rewrite)
                        (:rewrite :corollary
                                  (implies (and (subsetp-equal (double-rewrite ,x) ,y)
                                                (,name ,@(subst y x formals)))
                                           (equal (,name ,@formals)
                                                  t))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable subsetp-equal))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-nthcdr)
         (implies (force (,name ,@formals))
                  (equal (,name ,@(subst `(nthcdr ,n ,x) x formals))
                         t))
         :hints(("Goal"
                 :induct (nthcdr ,n ,x)
                 :in-theory (enable nthcdr))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-simpler-take)
         ,(cond ( ;; Careful if you edit this, elementp-of-nil might be :unknown, too.
                 (or (and (equal elementp-of-nil t)
                          (not negatedp))
                     (and (equal elementp-of-nil nil)
                          negatedp))
                 `(implies (force (,name ,@formals))
                           (equal (,name ,@(subst `(simpler-take ,n ,x) x formals))
                                  t)))
                (t
                 `(implies (and (force (,name ,@formals))
                                (force (<= ,n (len ,x))))
                           (equal (,name ,@(subst `(simpler-take ,n ,x) x formals))
                                  t))))
         :hints(("Goal"
                 :in-theory (enable simpler-take)
                 :induct (simpler-take ,n ,x))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-repeat)
         (equal (,name ,@(subst `(repeat ,x ,n) x formals))
                (or ,(cond (negatedp
                            `(not (,elementp ,@formals)))
                           (t
                            `(,elementp ,@formals)))
                    (zp ,n)))
         :hints(("Goal"
                 :induct (repeat ,x ,n)
                 :in-theory (enable repeat))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-mergesort)
         (equal (,name ,@(subst `(mergesort ,x) x formals))
                (,name ,@formals))
         :hints(("Goal" :cases ((,name ,@formals)))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-last)
         (implies (force (,name ,@formals))
                  (equal (,name ,@(subst `(last ,x) x formals))
                         t))
         :hints(("Goal"
                 :induct (last ,x)
                 :in-theory (enable last))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-butlast)
         ,(cond ((or (and (equal elementp-of-nil t)
                          (not negatedp))
                     (and (equal elementp-of-nil nil)
                          negatedp))
                 `(implies (force (,name ,@formals))
                           (equal (,name ,@(subst `(butlast ,x ,n) x formals))
                                  t)))
                (t
                 `(implies (and (force (,name ,@formals))
                                (force (natp ,n)))
                           (equal (,name ,@(subst `(butlast ,x ,n) x formals))
                                  t))))
         :hints(("Goal" :in-theory (enable butlast))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-set-difference-equal)
         (implies (force (,name ,@formals))
                  (equal (,name ,@(subst `(set-difference-equal ,x ,y) x formals))
                         t))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable set-difference-equal))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-union-equal)
         (implies (and (force (,name ,@formals))
                       (force (,name ,@(subst y x formals))))
                  (equal (,name ,@(subst `(union-equal ,x ,y) x formals))
                         t))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable union-equal))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-difference)
         (implies (force (,name ,@formals))
                  (equal (,name ,@(subst `(difference ,x ,y) x formals))
                         t))
         :hints(,last-ditch-hint))

       (defthm ,(mksym name '-of-intersect-1)
         (implies (,name ,@formals)
                  (equal (,name ,@(subst `(intersect ,x ,y) x formals))
                         t))
         :hints(,last-ditch-hint))

       (defthm ,(mksym name '-of-intersect-2)
         (implies (,name ,@(subst y x formals))
                  (equal (,name ,@(subst `(intersect ,x ,y) x formals))
                         t))
         :hints(,last-ditch-hint))

       (defthm ,(mksym name '-of-union)
         (implies (and (force (,name ,@formals))
                       (force (,name ,@(subst y x formals))))
                  (,name ,@(subst `(union ,x ,y) x formals)))
         :hints(("Goal"
                 :use ((:instance deflist-lemma-5 (x ,x) (y ,y))
                       (:instance ,(mksym name '-of-append)))
                 :in-theory (disable ,(mksym name '-of-append)))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-duplicated-members)
         (implies (force (,name ,@formals))
                  (equal (,name ,@(subst `(duplicated-members ,x) x formals))
                         t))
         :hints(,last-ditch-hint))
       )))

(defmacro deflist (name formals element
                        &key
                        (negatedp 'nil)
                        (guard 't)
                        (verify-guards 't)
                        (already-definedp 'nil)
                        (elementp-of-nil ':unknown)
                        mode
                        (parents '(acl2::undocumented))
                        (short 'nil)
                        (long 'nil))
  `(make-event (let ((mode (or ',mode (default-defun-mode (w state)))))
                 (deflist-fn ',name ',formals ',element ',negatedp ',guard ',verify-guards
                   ',already-definedp ',elementp-of-nil mode ',parents ',short ',long))))

