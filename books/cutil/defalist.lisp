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
  :short "Introduce a recognizer for a typed association list (alist)."

  :long "<p>Defalist allows you to quickly introduce a recognizer for a typed
association list (e.g., @('string-nat-alistp')) and proves basic theorems about
it.</p>

<p>Unlike many ACL2 alist recognizers, the recognizers introduced by defalist
<b>do not</b>, by default, imply @('(alistp x)'), but they do imply something
like @('(cons-listp x)').  That is,</p>

<ul>
<li>We require that each element is a cons, but</li>
<li>We do not require the alists to be nil-terminated.</li>
</ul>

<p>Not requiring @('nil') termination has some advantages.  It plays well with
@(see equivalence) relations like @(see list-equiv) and @(see
acl2::alist-equiv).  It also allows you to use features of @(see fast-alists)
such as \"size hints\" and \"alist names\" (see @(see hons-acons) for
details).</p>

<p>But there is also a disadvantage.  Namely, it may be difficult to operate on
a defalist using traditional alist functions, whose @(see guard)s require @(see
alistp).  Fortunately, there are generally good alternatives to these
traditional functions with no such requirement, e.g.,:</p>

<ul>
<li>@(see acons) &rarr; @(see hons-acons) or ordinary @(see cons)es.</li>
<li>@(see assoc) &rarr; @(see hons-get) for fast alists, or @(see hons-assoc-equal)
    for ordinary alists</li>
<li>@(see strip-cars) &rarr; @(see alist-keys)</li>
<li>@(see strip-cdrs) &rarr; @(see alist-vals)</li>
</ul>

<p>General form:</p>

@({
 (defalist name formals
    &key key               ; required
         val               ; required
         guard             ; t by default
         verify-guards     ; t by default
         keyp-of-nil       ; :unknown by default
         valp-of-nil       ; :unknown by default
         true-listp        ; nil by default
         mode              ; current defun-mode by default
         parents           ; '(acl2::undocumented) by default
         short             ; nil by default
         long              ; nil by default
         )
})

<p>For example,</p>

@({
 (defalist string-nat-alistp (x)
    :key (stringp x)
    :val (natp x))
})

<p>introduces a new function, @('string-nat-alistp'), that recognizes alists
whose keys are strings and whose values are natural numbers.  It also proves
many theorems about this new function.</p>

<p>Note that <b>x</b> is treated in a special way: it refers to the whole alist
in the formals and guards, but refers to individual keys or values in the
@(':key') and @(':val') positions.  This is similar to how @(see deflist),
@(see defprojection), and @(see defmapappend) handle @('x').</p>

<h3>Usage and Arguments</h3>

<p>Let @('pkg') be the package of @('name').  All functions, theorems, and
variables are created in this package.  One of the formals must be @('pkg::x'),
and this argument represents the alist to check.  Otherwise, the only
restriction on the formals is that you may not use the names @('pkg::a'),
@('pkg::n'), or @('pkg::y'), because we use these variables in the theorems we
generate.</p>

<p>The @(':key') and @(':val') arguments are required and should be simple
function calls involving some subset of the formals.  The basic idea is that
you write @('x') for the particular key or value that is being inspected.</p>

<p>The optional @(':guard') and @(':verify-guards') are given to the
@('defund') event that we introduce.  In other words, these are the guards that
will be used for the list recognizer, not the element recognizer.</p>

<p>The optional @(':true-listp') argument can be used to make the new
recognizer \"strict\" and only accept alists that are @('nil')-terminated; by
default the recognizer will be \"loose\" and will not pay attention to the
final <tt>cdr</tt>.  See @(see strict-list-recognizers) for further
discussion.</p>

<p>The optional @(':keyp-of-nil') (similarly @(':valp-of-nil')) keywords can be
used when @('(key-recognizer nil ...)') (similarly @('(val-recognzier nil
...)')) is always known to be @('t') or @('nil').  When it is provided,
@('defalist') can generate slightly better theorems.</p>

<p>The optional @(':mode') keyword can be set to @(':program') to introduce the
recognizer in program mode.  In this case, no theorems are introduced.</p>

<p>The optional @(':parents'), @(':short'), and @(':long') keywords are as in
@(see defxdoc).  Typically you only need to specify @(':parents'), and suitable
documentation will be automatically generated for @(':short') and @(':long').
If you don't like this documentation, you can supply your own @(':short')
and/or @(':long') to override it.</p>")

(defun defalist-fn (name formals key val
                         guard verify-guards
                         keyp-of-nil valp-of-nil
                         mode parents short long true-listp)
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

       (def `(defund ,name (,@formals)
               (declare (xargs :guard ,guard
                               :verify-guards ,verify-guards
                               :mode ,mode
                               ;; We tell ACL2 not to normalize because
                               ;; otherwise type reasoning can rewrite the
                               ;; definition, and ruin some of our theorems
                               ;; below, e.g., when KEYP is known to always be
                               ;; true.
                               :normalize nil
                               ))
               (if (consp ,x)
                   (and (consp (car ,x))
                        (,keyp ,@(subst `(caar ,x) x key-formals))
                        (,valp ,@(subst `(cdar ,x) x val-formals))
                        (,name ,@(subst `(cdr ,x) x formals)))
                 ,(if true-listp
                         `(null ,x)
                       t))))

       ((when (eq mode :program))
        `(progn
           ,@doc
           ,def)))

    `(encapsulate
       ()
       ,@doc

       (logic)
       (set-inhibit-warnings "theory" "free" "non-rec") ;; Note: implicitly local

       (local
        (encapsulate
          ()
          ;; FAUGH.  It's horrible to get this to work in all cases.
          ;;
          ;; See defalist-tests: if we have something like ALLP or NONEP, ACL2
          ;; can "helpfully" reduce them for us during preprocessing and then
          ;; rejects our rules because they look like we're trying to prove
          ;; (booleanp t) or (booleanp nil).
          ;;
          ;; To prevent that from happening, we have to turn off at least the
          ;; tau system and the type-prescription rules for keyp/valp.  But we
          ;; can't even do *THAT* reliably, because not all functions have
          ;; type-prescriptions.  (Woah, really?  Yes really: for instance,
          ;; built-ins like stringp.)
          ;;
          ;; So, as a horrible workaround, I'll prove these with rule-classes
          ;; nil and then re-prove them in the nil theory.

          (local (defthm ,(mksym 'booleanp-of- keyp '-for- name '-key-lemma)
                   (or (equal (,keyp ,@key-formals) t)
                       (equal (,keyp ,@key-formals) nil))
                   :rule-classes nil))

          (local (defthm ,(mksym 'booleanp-of- valp '-for- name '-val-lemma)
                   (or (equal (,valp ,@val-formals) t)
                       (equal (,valp ,@val-formals) nil))
                   :rule-classes nil))

          ,@(and (not (eq keyp-of-nil :unknown))
                 `((local (defthm ,(mksym keyp '-of-nil-for- name '-key-lemma)
                            (equal (,keyp ,@(subst ''nil x key-formals))
                                   ',keyp-of-nil)
                            :rule-classes nil))))

          ,@(and (not (eq valp-of-nil :unknown))
                 `((local (defthm ,(mksym valp '-of-nil-for- name '-val-lemma)
                            (equal (,valp ,@(subst ''nil x val-formals))
                                   ',valp-of-nil)
                            :rule-classes nil))))

          (local (in-theory nil))

          (defthm ,(mksym 'booleanp-of- keyp '-for- name '-key)
            (or (equal (,keyp ,@key-formals) t)
                (equal (,keyp ,@key-formals) nil))
            :rule-classes :type-prescription
            :hints(("Goal" :by ,(mksym 'booleanp-of- keyp '-for- name '-key-lemma))))

          (defthm ,(mksym 'booleanp-of- valp '-for- name '-val)
            (or (equal (,valp ,@val-formals) t)
                (equal (,valp ,@val-formals) nil))
            :rule-classes :type-prescription
            :hints(("Goal" :by ,(mksym 'booleanp-of- valp '-for- name '-val-lemma))))

          ,@(and (not (eq keyp-of-nil :unknown))
                 `((maybe-defthm-as-rewrite
                    ,(mksym keyp '-of-nil-for- name '-key)
                     (equal (,keyp ,@(subst ''nil x key-formals))
                            ',keyp-of-nil)
                     :hints(("Goal" :by ,(mksym keyp '-of-nil-for-
                                                name '-key-lemma))))))

          ,@(and (not (eq valp-of-nil :unknown))
                 `((maybe-defthm-as-rewrite
                    ,(mksym valp '-of-nil-for- name '-val)
                    (equal (,valp ,@(subst ''nil x val-formals))
                           ',valp-of-nil)
                    :hints(("Goal" :by ,(mksym valp '-of-nil-for-
                                               name '-val-lemma))))))
          ))

       ,def

       (local (in-theory (theory 'minimal-theory)))
       (local (in-theory (disable (:executable-counterpart tau-system))))
       (local (in-theory (enable deflist-support-lemmas
                                 ,(mksym 'booleanp-of- keyp '-for- name '-key)
                                 ,(mksym 'booleanp-of- valp '-for- name '-val)
                                 (:type-prescription ,name)
                                 default-car
                                 default-cdr)))
       (local (enable-if-theorem ,(mksym keyp '-of-nil-for- name '-key)))
       (local (enable-if-theorem ,(mksym valp '-of-nil-for- name '-val)))


; basic deflist style theorems ------------------------------------------------

       (defthm ,(mksym name '-when-not-consp)
         (implies (not (consp ,x))
                  (equal (,name ,@formals)
                         ,(if true-listp
                              `(not ,x)
                            t)))
         :hints(("Goal" :in-theory (enable ,name))))

       (defthm ,(mksym name '-of-cons)
         (equal (,name ,@(subst `(cons ,a ,x) x formals))
                (and (consp ,a)
                     (,keyp ,@(subst `(car ,a) x key-formals))
                     (,valp ,@(subst `(cdr ,a) x val-formals))
                     (,name ,@formals)))
         :hints(("Goal" :in-theory (enable ,name))))

       ;; Occasionally the user might prove these theorems on his own, e.g.,
       ;; due to a mutual recursion.  When this happens, they can end up
       ;; locally DISABLED!!!!  because of the theory hint we gave above.  So,
       ;; make sure they're explicitly enabled.
       (local (in-theory (enable ,(mksym name '-when-not-consp)
                                 ,(mksym name '-of-cons))))

       (local (in-theory (disable ,name)))

       ,@(and true-listp
              `((defthm ,(mksym 'true-listp-when- name)
                  (implies (,name ,@formals)
                           (true-listp ,x))
                  :rule-classes
                  ,(if (eql (len formals) 1)
                       :compound-recognizer
                     ;; Unfortunately we can't use a compound recognizer rule
                     ;; in this case.  I guess we'll try a rewrite rule, even
                     ;; though it could get expensive.
                     :rewrite)
                  :hints(("Goal" :induct (len ,x))))

                (defthm ,(mksym 'alistp-when- name)
                  (implies (,name ,@formals)
                           (alistp ,x))
                  :rule-classes
                  ,(if (eql (len formals) 1)
                       :tau-system
                     ;; Unfortunately we can't use a tau-system rule in this
                     ;; case.  I guess we'll try a rewrite rule, even though it
                     ;; could get expensive.
                     :rewrite)
                  :hints (("Goal" :in-theory (enable alistp))))

                (defthm ,(mksym name '-of-list-fix)
                  ;; See comments in deflist.lisp!
                  (implies (,name ,@formals)
                           (,name ,@(subst `(list-fix ,x) x formals))))))

       (defthm ,(mksym 'consp-when-member-equal-of- name)
         (implies (and (,name ,@formals)
                       (member-equal ,a ,x))
                  (equal (consp ,a)
                         t))
         :rule-classes ((:rewrite :backchain-limit-lst 0)
                        (:rewrite :backchain-limit-lst 0
                                  :corollary
                                  (implies (and (member-equal ,a ,x)
                                                (,name ,@formals))
                                           (equal (consp ,a)
                                                  t))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable member-equal))))

       (defthm ,(mksym keyp '-of-car-when-member-equal-of- name)
         (implies (and (,name ,@formals)
                       (member-equal ,a ,x))
                  (equal (,keyp ,@(subst `(car ,a) x key-formals))
                         t))
         :rule-classes
         ((:rewrite)
          (:rewrite :corollary
                    (implies (and (member-equal ,a ,x)
                                  (,name ,@formals))
                             (equal (,keyp ,@(subst `(car ,a) x key-formals))
                                    t))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable member-equal))))

       (defthm ,(mksym valp '-of-cdr-when-member-equal-of- name)
         (implies (and (,name ,@formals)
                       (member-equal ,a ,x))
                  (equal (,valp ,@(subst `(cdr ,a) x val-formals))
                         t))
         :rule-classes
         ((:rewrite)
          (:rewrite :corollary
                    (implies (and (member-equal ,a ,x)
                                  (,name ,@formals))
                             (equal (,valp ,@(subst `(cdr ,a) x val-formals))
                                    t))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable member-equal))))

       (defthm ,(mksym name '-when-subsetp-equal)
         (implies (and (,name ,@(subst y x formals))
                       (subsetp-equal ,x ,y))
                  (equal (,name ,@formals)
                         ,(if true-listp
                              `(true-listp ,x)
                            t)))
         :rule-classes ((:rewrite)
                        (:rewrite :corollary
                                  (implies (and (subsetp-equal ,x ,y)
                                                (,name ,@(subst y x formals)))
                                           (equal (,name ,@formals)
                                                  ,(if true-listp
                                                       `(true-listp ,x)
                                                     t)))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable subsetp-equal)
                 :expand ((,name ,@formals)
                          (true-listp ,x)))))

       ,@(and (not true-listp)
              `((defthm ,(mksym name '-preserves-set-equiv)
                  (implies (set-equiv ,x ,y)
                           (equal (,name ,@formals)
                                  (,name ,@(subst y x formals))))
                  :rule-classes :congruence
                  :hints(("Goal"
                          :in-theory (enable set-equiv)
                          :cases ((,name ,@formals))
                          :do-not-induct t)))))

       (defthm ,(mksym name '-of-append)
         (equal (,name ,@(subst `(append ,x ,y) x formals))
                (and (,name ,@(if true-listp
                                  (subst `(list-fix ,x) x formals)
                                formals))
                     (,name ,@(subst y x formals))))
         :hints(("Goal"
                 :induct (len ,x)
                 :in-theory (enable append))))

       ,@(and true-listp
              ;; We don't need these for the non true-listp case -- set
              ;; reasoning handles it.
              `((defthm ,(mksym name '-of-rev)
                  (equal (,name ,@(subst `(rev ,x) x formals))
                         (,name ,@(subst `(list-fix ,x) x formals)))
                  :hints(("Goal"
                          :induct (len ,x)
                          :in-theory (enable rev list-fix))))

                (defthm ,(mksym name '-of-revappend)
                  (equal (,name ,@(subst `(revappend ,x ,y) x formals))
                         (and (,name ,@(if true-listp
                                           (subst `(list-fix ,x) x formals)
                                         formals))
                              (,name ,@(subst y x formals))))
                  :hints(("Goal"
                          :induct (revappend ,x ,y)
                          :in-theory (enable revappend))))))

       (defthm ,(mksym keyp '-of-caar-when- name)
         (implies (,name ,@formals)
                  (equal (,keyp ,@(subst `(caar ,x) x key-formals))
                         ,(cond ((not keyp-of-nil)
                                 `(consp ,x))
                                ((eq keyp-of-nil t)
                                 t)
                                (t ;; keyp-of-nil is :unknown
                                 `(or (consp ,x)
                                      (,keyp ,@(subst nil x key-formals))))))))

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
         :hints(("Goal" :expand (,name ,@formals))))

       (defthm ,(mksym name '-of-cdr-when- name)
         (implies (,name ,@formals)
                  (equal (,name ,@(subst `(cdr ,x) x formals))
                         t)))

       (defthm ,(mksym name '-of-nthcdr)
         (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                  (equal (,name ,@(subst `(nthcdr ,n ,x) x formals))
                         t))
         :hints(("Goal" :do-not-induct t)))

       (defthm ,(mksym name '-of-take)
         (implies (and (,name ,@(subst `(double-rewrite ,x) x formals))
                       (force (<= ,n (len ,x))))
                  (equal (,name ,@(subst `(take ,n ,x) x formals))
                         t))
         :hints(("Goal"
                 :in-theory (enable acl2::take-redefinition)
                 :induct (take ,n ,x))))

       (defthm ,(mksym name '-of-repeat)
         (equal (,name ,@(subst `(repeat ,a ,n) x formals))
                (or (and (consp ,a)
                         (,keyp ,@(subst `(car ,a) x key-formals))
                         (,valp ,@(subst `(cdr ,a) x val-formals)))
                    (zp ,n)))
         :hints(("Goal"
                 :induct (repeat ,a ,n)
                 :in-theory (enable repeat))))

       (defthm ,(mksym name '-of-last)
         (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                  (equal (,name ,@(subst `(last ,x) x formals))
                         t))
         :hints(("Goal" :do-not-induct t)))

       (defthm ,(mksym name '-of-butlast)
         (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                  (equal (,name ,@(subst `(butlast ,x ,n) x formals))
                         t))
         :hints(("Goal" :do-not-induct t)))

       (defthm ,(mksym name '-of-duplicated-members)
         (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                  (equal (,name ,@(subst `(duplicated-members ,x) x formals))
                         t))
         :hints(("Goal" :do-not-induct t)))

       (defthm ,(mksym name '-of-set-difference-equal)
         (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                  (equal (,name ,@(subst `(set-difference-equal ,x ,y) x formals))
                         t))
         :hints(("Goal" :do-not-induct t)))

       (defthm ,(mksym name '-of-intersection-equal-1)
         (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                  (equal (,name ,@(subst `(intersection-equal ,x ,y) x formals))
                         t))
         :hints(("Goal" :do-not-induct t)))

       (defthm ,(mksym name '-of-intersection-equal-2)
         (implies (,name ,@(subst `(double-rewrite ,y) x formals))
                  (equal (,name ,@(subst `(intersection-equal ,x ,y) x formals))
                         t))
         :hints(("Goal" :do-not-induct t)))

       (defthm ,(mksym name '-of-sfix)
         ;; This rule is important for sets::under-set-equiv rules to work
         ;; right in the context of a foo-listp.
         (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                  (equal (,name ,@(subst `(sfix ,x) x formals))
                         t))
         :hints(("Goal"
                 :do-not-induct t
                 :cases ((setp ,x)))))

       ,@(and true-listp
              ;; Don't need these in the non true-listp case, set reasoning
              ;; handles it.
              `((defthm ,(mksym name '-of-union-equal)
                  (equal (,name ,@(subst `(union-equal ,x ,y) x formals))
                         (and (,name ,@(subst `(list-fix ,x) x formals))
                              (,name ,@(subst y x formals))))
                  :hints(("Goal"
                          :induct (len ,x)
                          :in-theory (enable union-equal))))

                (defthm ,(mksym name '-of-difference)
                  (implies (,name ,@formals)
                           (equal (,name ,@(subst `(difference ,x ,y) x formals))
                                  t))
                  :hints(("Goal" :do-not-induct t)))

                (defthm ,(mksym name '-of-intersect-1)
                  (implies (,name ,@formals)
                           (equal (,name ,@(subst `(intersect ,x ,y) x formals))
                                  t))
                  :hints(("Goal" :do-not-induct t)))

                (defthm ,(mksym name '-of-intersect-2)
                  (implies (,name ,@(subst y x formals))
                           (equal (,name ,@(subst `(intersect ,x ,y) x formals))
                                  t))
                  :hints(("Goal" :do-not-induct t)))

                (defthm ,(mksym name '-of-mergesort)
                  (equal (,name ,@(subst `(mergesort ,x) x formals))
                         (,name ,@(subst `(list-fix ,x) x formals)))
                  :hints(("Goal"
                          :do-not-induct t
                          :use ((:instance ,(mksym name '-when-subsetp-equal)
                                           (,x (mergesort ,x))
                                           (,y (list-fix ,x)))
                                (:instance ,(mksym name '-when-subsetp-equal)
                                           (,y (mergesort ,x))
                                           (,x (list-fix ,x)))))))

                (local
                 (defthm ,(mksym name '-of-union-lemma-1)
                   (implies (,name ,@(subst `(union ,x ,y) x formals))
                            (and (,name ,@(subst `(sfix ,x) x formals))
                                 (,name ,@(subst `(sfix ,y) x formals))))
                   :hints(("Goal" :do-not-induct t))))

                (local
                 (defthm ,(mksym name '-of-union-lemma-2)
                   (implies (and (,name ,@(subst `(sfix ,x) x formals))
                                 (,name ,@(subst `(sfix ,y) x formals)))
                            (,name ,@(subst `(union ,x ,y) x formals)))
                   :hints(("Goal"
                           :do-not-induct t
                           :in-theory (disable sets::union-under-set-equiv
                                               deflist-lemma-subsetp-of-union)
                           :use ((:instance deflist-lemma-subsetp-of-union
                                            (x ,x)
                                            (y ,y)))))))

                (defthm ,(mksym name '-of-union)
                  (equal (,name ,@(subst `(union ,x ,y) x formals))
                         (and (,name ,@(subst `(sfix ,x) x formals))
                              (,name ,@(subst `(sfix ,y) x formals))))
                  :hints(("Goal"
                          :cases ((,name ,@(subst `(union ,x ,y) x formals)))
                          :do-not-induct t)))

                ))

; additional theorems for alists ----------------------------------------------

       (defthm ,(mksym name '-of-hons-acons)
         ;; Not clear that hons-acons will ever be disabled, but just in case...
         (equal (,name ,@(subst `(hons-acons ,a ,n ,x) x formals))
                (and (,keyp ,@(subst a x key-formals))
                     (,valp ,@(subst n x val-formals))
                     (,name ,@formals)))
         :hints(("Goal" :in-theory (enable hons-acons))))

       (defthm ,(mksym name '-of-hons-shrink-alist)
         (implies (and (,name ,@formals)
                       (,name ,@(subst y x formals)))
                  (,name ,@(subst `(hons-shrink-alist ,x ,y) x formals)))
         :hints(("Goal"
                 :induct (hons-shrink-alist ,x ,y)
                 :in-theory (enable hons-shrink-alist))))

       (defthm ,(mksym name '-of-make-fal)
         (implies (and (,name ,@formals)
                       (,name ,@(subst y x formals)))
                  (,name ,@(subst `(make-fal ,x ,y) x formals)))
         :hints(("Goal"
                 :induct (make-fal ,x ,y)
                 :in-theory (enable make-fal))))

       (defthm ,(mksym valp '-of-cdr-of-hons-assoc-equal-when- name)
         (implies
          (,name ,@formals)
          (equal (,valp ,@(subst `(cdr (hons-assoc-equal ,a ,x)) x val-formals))
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
                 :in-theory (enable hons-assoc-equal))))

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
                         (long 'nil)
                         (true-listp 'nil))
  `(make-event (let ((mode (or ',mode (default-defun-mode (w state)))))
                 (defalist-fn ',name ',formals ',key ',val
                   ',guard ',verify-guards
                   ',keyp-of-nil ',valp-of-nil
                   mode
                   ',parents ',short ',long ',true-listp))))

