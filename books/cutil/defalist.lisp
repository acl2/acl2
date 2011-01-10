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

(in-package "CUTIL")
(include-book "deflist")
(include-book "misc/hons-help" :dir :system)

(defxdoc defalist
  :parents (cutil)
  :short "Introduce a recognizer for a typed alist."

  :long "<p>Defalist allows you to quickly introduce a recognizer for a typed
association list (e.g., <tt>string-nat-alistp</tt>) and proves basic theorems
about it.</p>

<p>Unlike many ACL2 alist recognizers, the recognizers introduced by defalist
do not imply <tt>(alistp x)</tt>, but they do imply something like
<tt>(cons-listp x)</tt>.  That is, we require that each element is a cons, but
we do not require the alists to be nil-terminated.  This is sometimes
unfortunate when you want to use functions like <tt>strip-cars</tt> or
<tt>strip-cdrs</tt> that expect their argument to be a true-list.  But it means
you can use size hints, names, etc., for fast alists.</p>

<p>General form:</p>

<code>
 (defalist name formals
    &amp;key key               ; required
         val               ; required
         guard             ; t by default
         verify-guards     ; t by default
         keyp-of-nil       ; :unknown by default
         valp-of-nil       ; :unknown by default
         mode              ; current defun-mode by default
         parents           ; '(acl2::undocumented) by default
         short             ; nil by default
         long              ; nil by default
         )
</code>

<p>For example,</p>

<code>
 (defalist string-nat-alistp (x)
    :key (stringp x)
    :val (natp x))
</code>

<p>introduces a new function, <tt>string-nat-alistp</tt>, that recognizes
alists whose keys are strings and whose values are natural numbers.  It also
proves many theorems about this new function.</p>

<p>Note that <b>x</b> is treated in a special way: it refers to the whole alist
in the formals and guards, but refers to individual keys or values in the
<tt>:key</tt> and <tt>:val</tt> positions.  This is similar to how @(see
deflist), @(see defprojection), and @(see defmapappend) handle <tt>x</tt>.</p>

<h3>Usage and Arguments</h3>

<p>Let <tt>pkg</tt> be the package of <tt>name</tt>.  All functions, theorems,
and variables are created in this package.  One of the formals must be
<tt>pkg::x</tt>, and this argument represents the alist to check.  Otherwise,
the only restriction on the formals is that you may not use the names
<tt>pkg::a</tt>, <tt>pkg::n</tt>, or <tt>pkg::y</tt>, because we use these
variables in the theorems we generate.</p>

<p>The <tt>:key</tt> and <tt>:val</tt> arguments are required and should be
simple function calls involving some subset of the formals.  The basic idea is
that you write <tt>x</tt> for the particular key or value that is being
inspected.</p>

<p>The optional <tt>:guard</tt> and <tt>:verify-guards</tt> are given to the
<tt>defund</tt> event that we introduce.  In other words, these are the guards
that will be used for the list recognizer, not the element recognizer.</p>

<p>The optional <tt>:keyp-of-nil</tt> (similarly <tt>:valp-of-nil</tt>)
keywords can be used when <tt>(key-recognizer nil ...)</tt> (similarly
<tt>(val-recognzier nil ...)</tt>) is always known to be <tt>t</tt> or
<tt>nil</tt>.  When it is provided, <tt>defalist</tt> can generate slightly
better theorems.</p>

<p>The optional <tt>:mode</tt> keyword can be set to <tt>:program</tt> to
introduce the recognizer in program mode.  In this case, no theorems are
introduced.</p>

<p>The optional <tt>:parents</tt>, <tt>:short</tt>, and <tt>:long</tt> keywords
are as in @(see defxdoc).  Typically you only need to specify
<tt>:parents</tt>, and suitable documentation will be automatically generated
for <tt>:short</tt> and <tt>:long</tt>.  If you don't like this documentation,
you can supply your own <tt>:short</tt> and/or <tt>:long</tt> to override
it.</p>")

(defun defalist-fn (name formals key val
                         guard verify-guards
                         keyp-of-nil valp-of-nil
                         mode parents short long)
  (declare (xargs :mode :program))
  (b* (((unless (symbolp name))
        (er hard 'deflist "Name must be a symbol, but is ~x0." name))

       (mksym-package-symbol name)

       ;; Special variables that are reserved by defalist.
       (x (intern-in-package-of-symbol "X" name))
       (a (intern-in-package-of-symbol "A" name))
       (n (intern-in-package-of-symbol "N" name))
       (y (intern-in-package-of-symbol "Y" name))

       ((unless (and (symbol-listp formals)
                     (no-duplicatesp formals)))
        (er hard 'defalist
            "The formals must be a list of unique symbols, but the ~
            formals are ~x0." formals))

       ((unless (member x formals))
        (er hard 'defalist
            "The formals must contain X, but are ~x0.~%" formals))

       ((when (or (member a formals)
                  (member n formals)
                  (member y formals)))
        (er hard 'defalist
            "As a special restriction, formals may not mention a, n, ~
            or y, but the formals are ~x0." formals))

       ((unless (and (consp key)
                     (symbolp (car key))))
        (er hard 'defalist
            "The key recognizer must be a function applied ~
             to the formals, but is ~x0." key))
       (keyp         (car key))
       (key-formals  (cdr key))

       ((unless (and (consp val)
                     (symbolp (car val))))
        (er hard 'defalist
            "The value recognizer must be a function applied ~
             to the formals, but is ~x0." val))
       (valp         (car val))
       (val-formals  (cdr val))

       ((unless (member keyp-of-nil '(t nil :unknown)))
        (er hard? 'defalist
            "keyp-of-nil must be a boolean or :unknown."))

       ((unless (member valp-of-nil '(t nil :unknown)))
        (er hard? 'defalist
            "valp-of-nil must be a boolean or :unknown."))

       ((unless (booleanp verify-guards))
        (er hard 'defalist
            ":verify-guards must be a boolean, but is ~x0."
            verify-guards))

       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (er hard 'defalist
            ":mode must be one of :logic or :program, but is ~x0." mode))

       (short (or short
                  (and parents
                       (str::cat "@(call " (symbol-name name) ") recognizes
association lists where every key satisfies @(see " (symbol-name keyp) ") and
each value satisfies @(see " (symbol-name valp) ")."))))

       (long (or long
                 (and parents
                      (str::cat "<p>This is an ordinary @(see defalist).</p>"
                                "@(def " (symbol-name name) ")"))))

       (doc (if (or parents short long)
                `((defxdoc ,name :parents ,parents :short ,short :long ,long))
              nil))

       (last-ditch-hint
        `(and stable-under-simplificationp
              '(:in-theory (enable ,(mksym name '-last-ditch-rules)))))

       (def `(defund ,name (,@formals)
               (declare (xargs :guard ,guard
                               :verify-guards ,verify-guards
                               :mode ,mode))
               (or (atom ,x)
                   (and (consp (car ,x))
                        (,keyp ,@(subst `(caar ,x) x key-formals))
                        (,valp ,@(subst `(cdar ,x) x val-formals))
                        (,name ,@(subst `(cdr ,x) x formals))))))

       ((when (eq mode :program))
        `(progn
           ,@doc
           ,def)))

    `(encapsulate
       ()
       (logic)

       (set-inhibit-warnings "theory" "free" "non-rec") ;; Note: implicitly local

       ,@doc
       ,def

       (local (in-theory (theory 'minimal-theory)))
       (local (in-theory (enable car-cons cdr-cons car-cdr-elim
                                 zp len natp
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

       ;; basic deflist style theorems

       (defthm ,(mksym name '-when-not-consp)
         (implies (not (consp ,x))
                  (equal (,name ,@formals)
                         t))
         :hints(("Goal" :in-theory (enable ,name))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-cons)
         (equal (,name ,@(subst `(cons ,a ,x) x formals))
                (and (consp ,a)
                     (,keyp ,@(subst `(car ,a) x key-formals))
                     (,valp ,@(subst `(cdr ,a) x val-formals))
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

       (defthm ,(mksym keyp '-of-caar-when- name)
         (implies (,name ,@formals)
                  (equal (,keyp ,@(subst `(caar ,x) x key-formals))
                         ,(cond ((not keyp-of-nil)
                                 `(consp ,x))
                                ((eq keyp-of-nil t)
                                 t)
                                (t ;; keyp-of-nil is :unknown
                                 `(or (consp ,x)
                                      (,keyp ,@(subst nil x key-formals)))))))
         :hints(,last-ditch-hint))

       (defthm ,(mksym valp '-of-cdar-when- name)
         (implies (,name ,@formals)
                  (equal (,valp ,@(subst `(cdar ,x) x val-formals))
                         ,(cond ((not valp-of-nil)
                                 `(consp ,x))
                                ((eq valp-of-nil t)
                                 t)
                                (t ;; keyp-of-nil is :unknown
                                 `(or (consp ,x)
                                      (,valp ,@(subst nil x val-formals)))))))
         :hints(,last-ditch-hint))

       (defthm ,(mksym name '-of-cdr-when- name)
         (implies (,name ,@formals)
                  (equal (,name ,@(subst `(cdr ,x) x formals))
                         t))
         :hints(,last-ditch-hint))

       (defthm ,(mksym 'consp-when-member-equal-of- name)
         (implies (and (,name ,@formals)
                       (member-equal ,a (double-rewrite ,x)))
                  (equal (consp ,a)
                         t))
         :rule-classes ((:rewrite :backchain-limit-lst 0)
                        (:rewrite :backchain-limit-lst 0
                                  :corollary
                                  (implies (and (member-equal ,a (double-rewrite ,x))
                                                (,name ,@formals))
                                           (equal (consp ,a)
                                                  t))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable member-equal))
                ,last-ditch-hint))

       (defthm ,(mksym keyp '-of-car-when-member-equal-of- name)
         (implies (and (,name ,@formals)
                       (member-equal ,a (double-rewrite ,x)))
                  (equal (,keyp ,@(subst `(car ,a) x key-formals))
                         t))
         :rule-classes ((:rewrite)
                        (:rewrite :corollary
                                  (implies (and (member-equal ,a (double-rewrite ,x))
                                                (,name ,@formals))
                                           (equal (,keyp ,@(subst `(car ,a) x key-formals))
                                                  t))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable member-equal))
                ,last-ditch-hint))

       (defthm ,(mksym valp '-of-cdr-when-member-equal-of- name)
         (implies (and (,name ,@formals)
                       (member-equal ,a (double-rewrite ,x)))
                  (equal (,valp ,@(subst `(cdr ,a) x val-formals))
                         t))
         :rule-classes ((:rewrite)
                        (:rewrite :corollary
                                  (implies (and (member-equal ,a (double-rewrite ,x))
                                                (,name ,@formals))
                                           (equal (,valp ,@(subst `(cdr ,a) x val-formals))
                                                  t))))
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
         (implies (and (force (,name ,@formals))
                       (force (<= ,n (len ,x))))
                  (equal (,name ,@(subst `(simpler-take ,n ,x) x formals))
                         t))
         :hints(("Goal"
                 :in-theory (enable simpler-take)
                 :induct (simpler-take ,n ,x))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-repeat)
         (equal (,name ,@(subst `(repeat ,a ,n) x formals))
                (or (and (consp ,a)
                         (,keyp ,@(subst `(car ,a) x key-formals))
                         (,valp ,@(subst `(cdr ,a) x val-formals)))
                    (zp ,n)))
         :hints(("Goal"
                 :induct (repeat ,a ,n)
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
         (implies (and (force (,name ,@formals))
                       (force (natp ,n)))
                  (equal (,name ,@(subst `(butlast ,x ,n) x formals))
                         t))
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

       ;; additional theorems for alists

       (defthm ,(mksym name '-of-hons-acons)
         (equal (,name ,@(subst `(hons-acons ,a ,n ,x) x formals))
                (and (,keyp ,@(subst a x key-formals))
                     (,valp ,@(subst n x val-formals))
                     (,name ,@formals)))
         :hints(("Goal"
                 :in-theory (enable hons-acons))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-hons-shrink-alist)
         (implies (and (force (,name ,@formals))
                       (force (,name ,@(subst y x formals))))
                  (,name ,@(subst `(hons-shrink-alist ,x ,y) x formals)))
         :hints(("Goal"
                 :induct (hons-shrink-alist ,x ,y)
                 :in-theory (enable hons-shrink-alist))
                ,last-ditch-hint))

       (defthm ,(mksym name '-of-make-fal)
         (implies (and (force (,name ,@formals))
                       (force (,name ,@(subst y x formals))))
                  (,name ,@(subst `(make-fal ,x ,y) x formals)))
         :hints(("Goal"
                 :induct (make-fal ,x ,y)
                 :in-theory (enable make-fal))
                ,last-ditch-hint))

       (defthm ,(mksym valp '-of-cdr-of-hons-assoc-equal-when- name)
         (implies (,name ,@formals)
                  (equal (,valp (cdr (hons-assoc-equal ,a ,x)))
                         ,(cond ((eq valp-of-nil t)
                                 t)
                                ((eq valp-of-nil nil)
                                 `(if (hons-assoc-equal ,a ,x)
                                      t
                                    nil))
                                (t
                                 `(if (hons-assoc-equal ,a ,x)
                                      t
                                    (,valp ,@(subst nil x val-formals)))))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable hons-assoc-equal))
                ,last-ditch-hint))

        )))

(defmacro defalist (name formals
                         &key
                         key
                         val
                         (guard 't)
                         (verify-guards 't)
                         (keyp-of-nil ':unknown)
                         (valp-of-nil ':unknown)
                         mode
                         (parents '(acl2::undocumented))
                         (short 'nil)
                         (long 'nil))
  `(make-event (let ((mode (or ',mode (default-defun-mode (w state)))))
                 (defalist-fn ',name ',formals ',key ',val
                   ',guard ',verify-guards
                   ',keyp-of-nil ',valp-of-nil
                   mode
                   ',parents ',short ',long))))

