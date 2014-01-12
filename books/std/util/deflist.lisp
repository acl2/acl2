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
;
; Additional copyright notice:
;
; This file is adapted from Milawa, which is also released under the GPL.

(in-package "STD")
(include-book "xdoc/top" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "str/cat" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(include-book "std/lists/sets" :dir :system)
(include-book "std/lists/list-fix" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "maybe-defthm")
(include-book "support")
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
   :mode                    current defun-mode
   :already-definedp        nil
   :verbosep                nil
   :parents                 nil
   :short                   nil
   :long                    nil
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

<p>The optional @(':already-definedp') keyword can be set if you have already
defined the function.  This can be used to generate all of the ordinary
@('deflist') theorems without generating a @('defund') event, and is useful
when you are dealing with mutually recursive recognizers.</p>

<p>The optional @(':mode') keyword can be set to @(':logic') or @(':program')
to introduce the recognizer in logic or program mode.  The default is whatever
the current default defun-mode is for ACL2, i.e., if you are already in program
mode, it will default to program mode, etc.</p>

<p>The optional @(':verbosep') flag can be set to @('t') if you want deflist to
print everything it's doing.  This may be useful if you run into any failures,
or if you are simply curious about what is being introduced.</p>

<p>The optional @(':parents'), @(':short'), and @(':long') keywords are as in
@(see defxdoc).  Typically you only need to specify @(':parents'), perhaps
implicitly with @(see xdoc::set-default-parents), and suitable documentation
will be automatically generated for @(':short') and @(':long').  If you don't
like this documentation, you can supply your own @(':short') and/or @(':long')
to override it.</p>

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
first.</p>")

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

<p>@(see deflist) originally came out of <a
href='http://www.cs.utexas.edu/users/jared/milawa/Web/'>Milawa</a>, where I
universally applied the loose approach, and in that context I think it is very
nice.  It's not entirely clear that loose recognizers are a good fit for ACL2.
Really one of the main objections to the loose style is: ACL2's built-in list
recognizers use the strict approach, and it can become irritating to keep track
of which recognizers require true-listp and which don't.</p>")

(defsection deflist-lemmas

  ;; Deflist does most of its work in a very minimal theory.  These are a few
  ;; lemmas that we enable so that it will work.

  (local (include-book "std/osets/under-set-equiv" :dir :system))

  (defthmd deflist-lemma-member-of-car
    (iff (member-equal (car x) x)
         (consp x)))

  (defthmd deflist-lemma-subsetp-of-set-difference-equal
    (subsetp-equal (set-difference-equal x y) x))

  (defthmd deflist-lemma-subsetp-of-intersection-equal
    (and (subsetp-equal (intersection-equal x y) x)
         (subsetp-equal (intersection-equal x y) y)))

  (defthmd deflist-lemma-subsetp-equal-of-duplicated-members
    (subsetp-equal (duplicated-members x) x))

  (defthmd deflist-lemma-subsetp-of-nthcdr
    (subsetp-equal (nthcdr n x) x))

  (defthmd deflist-lemma-true-listp-of-nthcdr
    (equal (true-listp (nthcdr n x))
           (or (< (len x) (nfix n))
               (true-listp x)))
    :hints(("Goal" :induct (nthcdr n x))))

  (defthmd deflist-lemma-subsetp-of-last
    (subsetp-equal (last x) x))

  (defthmd deflist-lemma-true-listp-of-last
    (equal (true-listp (last x))
           (true-listp x)))

  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (defthmd c0
           (equal (< (+ a b) (+ a c))
                  (< b c))))

  (defthmd deflist-lemma-cancel-negative-constant
    (implies (syntaxp (and (quotep a)
                           (< (acl2::unquote a) 0)))
             (equal (< (+ a b) c)
                    (< b (+ (- a) c))))
    :hints(("Goal"
            :use ((:instance c0
                             (a (- a))
                             (b (+ a b))
                             (c c))))))

  (defthmd deflist-lemma-len-over-zero
    (equal (< 0 (len x))
           (consp x)))

  (defthmd deflist-lemma-nth-when-zp
    (implies (zp n)
             (equal (nth n x)
                    (car x))))

  (defthmd deflist-lemma-nth-when-atom
    (implies (atom x)
             (equal (nth n x)
                    nil)))

  (defthmd deflist-lemma-nth-of-cons
    (equal (nth n (cons a x))
           (if (zp n)
               a
             (nth (+ -1 n) x))))


  (local (defthm l0
           (implies (and (member a (take n x))
                         (<= (nfix n) (len x)))
                    (member a x))
           :hints(("Goal" :in-theory (enable acl2::take-redefinition)))))

  (local (defthm l1
           (implies (<= (nfix n) (len x))
                    (subsetp-equal (take n x) x))
           :hints(("Goal" :in-theory (enable acl2::take-redefinition)))))

  (defthmd deflist-lemma-subsetp-of-butlast
    (subsetp-equal (butlast x n) x))

  (defthmd deflist-lemma-true-listp-of-butlast
    (true-listp (butlast x n))
    :rule-classes :type-prescription)

  (defthmd deflist-lemma-sfix-when-not-setp
    (implies (not (setp x))
             (equal (sfix x) nil))
    :hints(("Goal" :in-theory (enable sfix empty))))

  (defthmd deflist-lemma-sfix-when-setp
    (implies (setp x)
             (equal (sfix x)
                    x))
    :hints(("Goal" :in-theory (enable sfix empty))))

  (defthmd deflist-lemma-subsetp-of-difference
    (subsetp-equal (difference x y) x))

  (local (defthm g1
           (implies (member a (sfix x))
                    (member a x))
           :hints(("Goal"
                   :do-not-induct t
                   :use ((:instance sets::in-to-member
                                    (sets::a a)
                                    (sets::x (sfix x))))))))

  (defthmd deflist-lemma-subsetp-of-intersect
    (and (subsetp-equal (intersect x y) x)
         (subsetp-equal (intersect x y) y))
    :hints(("Goal" :do-not-induct t)))

  (defthmd deflist-lemma-true-listp-of-sfix
    (true-listp (sfix x))
    :rule-classes :type-prescription)

  (defthmd deflist-lemma-subsetp-of-union
    (and (subsetp-equal (sfix x) (union x y))
         (subsetp-equal (sfix y) (union x y))
         (subsetp-equal (union x y) (append (sfix x) (sfix y))))))



(deftheory deflist-support-lemmas
  '((:type-prescription intersection-equal)
    (:type-prescription set-difference-equal)
    (:type-prescription duplicated-members)
    (:type-prescription list-fix)
    (:type-prescription rev)
    (:type-prescription len)
    deflist-lemma-member-of-car
    deflist-lemma-subsetp-of-set-difference-equal
    deflist-lemma-subsetp-of-intersection-equal
    deflist-lemma-subsetp-equal-of-duplicated-members
    deflist-lemma-cancel-negative-constant
    deflist-lemma-len-over-zero
    deflist-lemma-nth-when-zp
    deflist-lemma-nth-when-atom
    deflist-lemma-nth-of-cons
    deflist-lemma-sfix-when-not-setp
    deflist-lemma-sfix-when-setp
    deflist-lemma-subsetp-of-nthcdr
    deflist-lemma-subsetp-of-last
    deflist-lemma-subsetp-of-butlast
    deflist-lemma-true-listp-of-last
    deflist-lemma-true-listp-of-butlast
    deflist-lemma-true-listp-of-nthcdr
    deflist-lemma-subsetp-of-difference
    deflist-lemma-subsetp-of-intersect
    deflist-lemma-true-listp-of-sfix
    deflist-lemma-subsetp-of-union
    car-cons
    cdr-cons
    car-cdr-elim
    zp
    len
    natp
    nth
    update-nth
    nfix
    acl2::default-+-2
    acl2::default-<-1
    acl2::default-unary-minus
    acl2::unicity-of-0
    acl2::take-redefinition
    acl2::take-induction
    acl2::simpler-take-induction
    acl2::list-fix-when-not-consp
    acl2::list-fix-when-true-listp
    acl2::list-fix-of-cons
    sets::sets-are-true-lists
    sets::mergesort-set
    sets::union-set
    sets::intersect-set
    sets::difference-set
    acl2::set-equiv-implies-equal-subsetp-1
    acl2::set-equiv-implies-equal-subsetp-2
    acl2::subsetp-refl
    acl2::list-fix-under-list-equiv
    sets::mergesort-under-set-equiv
    acl2::binary-append-without-guard))


(defconst *deflist-valid-keywords*
  '(:negatedp
    :guard
    :verify-guards
    :guard-debug
    :guard-hints
    :already-definedp
    :elementp-of-nil
    :mode
    :parents
    :short
    :long
    :true-listp
    :rest
    :verbosep
    ;; Undocumented option for customizing the theory, mainly meant for
    ;; problematic cases, e.g., built-in functions where ACL2 "knows too much"
    :theory-hack))

(defun deflist-fn (name formals element kwd-alist other-events state)
  (declare (xargs :mode :program))
  (b* ((__function__ 'deflist)
       (mksym-package-symbol name)

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

       (negatedp         (getarg :negatedp         nil      kwd-alist))
       (true-listp       (getarg :true-listp       nil      kwd-alist))
       (verify-guards    (getarg :verify-guards    t        kwd-alist))
       (guard            (getarg :guard            t        kwd-alist))
       (guard-debug      (getarg :guard-debug      nil      kwd-alist))
       (guard-hints      (getarg :guard-hints      nil      kwd-alist))
       (already-definedp (getarg :already-definedp nil      kwd-alist))
       (elementp-of-nil  (getarg :elementp-of-nil  :unknown kwd-alist))
       (short            (getarg :short            nil      kwd-alist))
       (long             (getarg :long             nil      kwd-alist))
       (theory-hack      (getarg :theory-hack      nil      kwd-alist))

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
                       (str::cat "@(call " (symbol-name name)
                                 ") recognizes lists where every element "
                                 (if negatedp
                                     "is rejected by "
                                   "satisfies ")
                                 ;; bozo it'd be better to put the formals in
                                 ;; here, for multi-arity functions.
                                 "@(see " (symbol-name elementp) ")."))))

       (long (or long
                 (and parents
                      (if true-listp
                          "<p>This is an ordinary @(see std::deflist).  It is
                           \"strict\" in that it requires @('x') to be a
                           \"properly\" nil-terminated list.</p>"
                        "<p>This is an ordinary @(see std::deflist).  It is
                         \"loose\" in that it does not care whether @('x') is
                         nil-terminated.</p>"))))

       (def (if already-definedp
                nil
              `((defund ,name (,@formals)
                  (declare (xargs :guard ,guard
                                  ;; We tell ACL2 not to normalize because
                                  ;; otherwise type reasoning can rewrite the
                                  ;; definition, and ruin some of our theorems
                                  ;; below, e.g., when ELEMENTP is known to
                                  ;; always be true.
                                  :normalize nil
                                  ,@(and (eq mode :logic)
                                         `(:verify-guards ,verify-guards
                                           :guard-debug   ,guard-debug
                                           :guard-hints   ,guard-hints))))
                  (if (consp ,x)
                      (and ,(if negatedp
                                `(not (,elementp ,@(subst `(car ,x) x elem-formals)))
                              `(,elementp ,@(subst `(car ,x) x elem-formals)))
                           (,name ,@(subst `(cdr ,x) x formals)))
                    ,(if true-listp
                         `(null ,x)
                       t))))))

       ((when (eq mode :program))
        `(defsection ,name
           ,@(and parents `(:parents ,parents))
           ,@(and short   `(:short ,short))
           ,@(and long    `(:long ,long))
           (program)
           ,@def
           ,@rest))

       (events
        `((logic)
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
          (local (in-theory (enable deflist-support-lemmas
                                    ,name
                                    (:type-prescription ,name)
                                    deflist-local-booleanp-element-thm
                                    )))
          (local (enable-if-theorem deflist-local-elementp-of-nil-thm))
          ,@theory-hack

          (defthm ,(mksym name '-when-not-consp)
            (implies (not (consp ,x))
                     (equal (,name ,@formals)
                            ,(if true-listp
                                 `(not ,x)
                               t)))
            :hints(("Goal" :in-theory (enable ,name))))

          (defthm ,(mksym name '-of-cons)
            (equal (,name ,@(subst `(cons ,a ,x) x formals))
                   (and ,(if negatedp
                             `(not (,elementp ,@(subst a x elem-formals)))
                           `(,elementp ,@(subst a x elem-formals)))
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

                   (defthm ,(mksym name '-of-list-fix)
                     ;; This is not very satisfying.  Ideally, ACL2 would
                     ;; deeply understand, from the compound-recognizer rule
                     ;; showing true-listp when foo-listp, that whenever
                     ;; (foo-listp x) holds then (true-listp x) holds.
                     ;; Ideally, it could use this knowledge to rewrite
                     ;; (list-fix x) to x whenever we can show (foo-listp x).
                     ;;
                     ;; But compound recognizers aren't quite good enough for
                     ;; this.  For instance, ACL2 won't rewrite a term like
                     ;; (list-fix (accessor x)) into (accessor x) even if we
                     ;; have a rewrite rule that says (foo-listp (accessor x)).
                     ;;
                     ;; Some alternatives we considered:
                     ;;
                     ;;  - A rewrite rule version of (foo-listp x) ==>
                     ;;    (true-listp x).  But it seems like this would get
                     ;;    *really* expensive when you have 100 list
                     ;;    recognizers and you encounter a true-listp term.
                     ;;
                     ;;  - A rewrite rule that rewrites (list-fix x) ==> x when
                     ;;    (foo-listp x) is known.  This might be the right
                     ;;    compromise.  It's at least somewhat less common to
                     ;;    see list-fix than true-listp.  But it still suffers
                     ;;    from the same kind of scaling problem.
                     ;;
                     ;; David's rule, below, is not as powerful as either of
                     ;; these approaches, but it at least manages to localize
                     ;; the performance impact, and helps at least in some
                     ;; cases.  Perhaps TAU can somehow help with this in the
                     ;; future.
                     (implies (,name ,@formals)
                              (,name ,@(subst `(list-fix ,x) x formals))))))

          (defthm ,(mksym elementp '-when-member-equal-of- name)
            ;; We previously used double-rewrite here, but it interferes with
            ;; free-variable matching
            (implies (and (,name ,@formals)
                          (member-equal ,a ,x))
                     (equal (,elementp ,@(subst a x elem-formals))
                            ,(not negatedp)))
            :rule-classes ((:rewrite)
                           (:rewrite
                            :corollary
                            (implies (and (member-equal ,a ,x)
                                          (,name ,@formals))
                                     (equal (,elementp ,@(subst a x elem-formals))
                                            ,(not negatedp)))))
            :hints(("Goal"
                    :induct (len ,x)
                    :in-theory (enable member-equal))))

          (defthm ,(mksym name '-when-subsetp-equal)
            ;; We previously used double-rewrite here, but it interferes with
            ;; free-variable matching
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
                    :in-theory (enable subsetp-equal ,name)
                    :expand (true-listp ,x)
                    :do-not '(eliminate-destructors))

                   ;; Horrible, horrible hack.  I found that I couldn't get
                   ;; deflist to process ATOM-LISTP because ACL2 knows too much
                   ;; about ATOM, so the member-equal rule above ends up being
                   ;; no good because it tries to target ATOM instead of CONSP,
                   ;; and we get nowhere.  Solution: try to explicitly use the
                   ;; member rule if we get stuck.
                   (and stable-under-simplificationp
                        '(:in-theory (disable
                                      ,(mksym elementp '-when-member-equal-of- name))
                          :use ((:instance
                                 ,(mksym elementp '-when-member-equal-of- name)
                                 (,a (car ,x))
                                 (,x ,y)))))))

          ,@(and (not true-listp)
                 ;; Awesome set congruence rule for loose recognizers, but not
                 ;; a theorem for strict recognizers.
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
                    :expand (list-fix ,x)
                    :in-theory (enable append))))

          ,@(and true-listp
                 ;; We don't bother proving these for loose recognizers because
                 ;; the set-equiv congruence should handle them automatically
                 `((defthm ,(mksym name '-of-rev)
                     (equal (,name ,@(subst `(rev ,x) x formals))
                            (,name ,@(if true-listp
                                         (subst `(list-fix ,x) x formals)
                                       formals)))
                     :hints(("Goal"
                             :induct (len ,x)
                             :expand (list-fix ,x)
                             :in-theory (enable rev))))

                   (defthm ,(mksym name '-of-revappend)
                     (equal (,name ,@(subst `(revappend ,x ,y) x formals))
                            (and (,name ,@(if true-listp
                                              (subst `(list-fix ,x) x formals)
                                            formals))
                                 (,name ,@(subst y x formals))))
                     :hints(("Goal"
                             :induct (revappend ,x ,y)
                             :in-theory (enable revappend))))))

          (defthm ,(mksym elementp '-of-car-when- name)
            (implies
             (,name ,@(subst `(double-rewrite ,x) x formals))
             (equal (,elementp ,@(subst `(car ,x) x elem-formals))
                    ,(cond
                      ((eq elementp-of-nil nil)
                       (if negatedp
                           ;; If x is a cons, then its car is not an element.
                           ;; Else its car is nil, which is not an element.
                           nil
                         ;; If x is a cons, then its car is an element.
                         ;; Else its car is nil, which is not an element.
                         `(consp ,x)))
                      ((eq elementp-of-nil t)
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
            :hints(("Goal"
                    :in-theory (enable default-car)
                    :expand ((,name . ,formals)))))

          (defthm ,(mksym name '-of-cdr-when- name)
            (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                     (equal (,name ,@(subst `(cdr ,x) x formals))
                            t)))

          (defthm ,(mksym elementp '-of-nth-when- name)
            (implies
             (,name ,@(subst `(double-rewrite ,x) x formals))
             (equal (,elementp ,@(subst `(nth ,n ,x) x formals))
                    ,(cond
                      ((eq elementp-of-nil nil)
                       (if negatedp
                           ;; (elementp {e \in X}) = NIL, (elementp nil) = NIL
                           nil
                         ;; (elementp {(e \in X}) = T, (elementp nil) = NIL
                         `(< (nfix ,n) (len ,x))))
                      ((eq elementp-of-nil t)
                       (if negatedp
                           ;; (elementp {e \in X}) = NIL, (elementp nil) = T
                           `(>= (nfix ,n) (len ,x))
                         ;; (elementp {e \in X}) = T, (elementp nil) = T
                         t))
                      (t
                       (if negatedp
                           ;; (elementp {e \in X}) = NIL, (elementp nil) = ???
                           `(and (,elementp ,@(subst nil x elem-formals))
                                 (>= (nfix ,n) (len ,x)))
                         ;; (elementp {e \in X}) = T, (elementp nil) = ???
                         `(or (,elementp ,@(subst nil x elem-formals))
                              (< (nfix ,n) (len ,x))))))))
            :hints(("Goal" :induct (nth ,n ,x))))

          (defthm ,(mksym name '-of-update-nth-when- elementp)
            ;; 1. When (elementp nil) = NIL, there's a strong bound because if
            ;; you update something past the length of the list, you introduce
            ;; NILs into the list and then ruin foo-listp.
            ;;
            ;; 2. When (elementp nil) = T, there's no bound because no matter
            ;; whether you add NILs, they're still valid.
            ;;
            ;; 3. When (elementp nil) = Unknown, we restrict the rule to only
            ;; fire if N is in bounds
            ,(let ((val-okp (if negatedp
                                `(not (,elementp ,@(subst y x elem-formals)))
                              `(,elementp ,@(subst y x elem-formals)))))
               (cond ((eq elementp-of-nil negatedp)
                      `(implies
                        (,name ,@(subst `(double-rewrite ,x) x formals))
                        (equal (,name ,@(subst `(update-nth ,n ,y ,x) x formals))
                               (and (<= (nfix ,n) (len ,x))
                                    ,val-okp))))
                     ((eq elementp-of-nil (not negatedp))
                      `(implies
                        (,name ,@(subst `(double-rewrite ,x) x formals))
                        (equal (,name ,@(subst `(update-nth ,n ,y ,x) x formals))
                               ,val-okp)))
                     (t
                      `(implies
                        (and (<= (nfix ,n) (len ,x))
                             (,name ,@(subst `(double-rewrite ,x) x formals)))
                        (equal (,name ,@(subst `(update-nth ,n ,y ,x) x formals))
                               ,val-okp))))))

          (defthm ,(mksym name '-of-nthcdr)
            (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                     (equal (,name ,@(subst `(nthcdr ,n ,x) x formals))
                            t))
            :hints(("Goal" :do-not-induct t)))

          (defthm ,(mksym name '-of-take)
            (implies
             (,name ,@(subst `(double-rewrite ,x) x formals))
             (equal (,name ,@(subst `(take ,n ,x) x formals))
                    ,(cond
                      ((eq elementp-of-nil nil)
                       (if negatedp
                           t
                         `(<= (nfix ,n) (len ,x))))
                      ((eq elementp-of-nil t)
                       (if negatedp
                           `(<= (nfix ,n) (len ,x))
                         t))
                      (t
                       (if negatedp
                           `(or (not (,elementp ,@(subst nil x elem-formals)))
                                (<= (nfix ,n) (len ,x)))
                         `(or (,elementp ,@(subst nil x elem-formals))
                              (<= (nfix ,n) (len ,x))))))))
            :hints(("Goal"
                    :in-theory (enable acl2::take-redefinition)
                    :induct (take ,n ,x)
                    :expand ((,name ,@formals)
                             (:free (,x ,y)
                                    (,name ,@(subst `(cons ,x ,y) x formals)))))))

          (defthm ,(mksym name '-of-repeat)
            (equal (,name ,@(subst `(repeat ,x ,n) x formals))
                   (or ,(cond (negatedp
                               `(not (,elementp ,@formals)))
                              (t
                               `(,elementp ,@formals)))
                       (zp ,n)))
            :hints(("Goal"
                    :induct (repeat ,x ,n)
                    :in-theory (enable repeat deflist-local-booleanp-element-thm)
                    :expand ((,name ,@formals)
                             (:free (,x ,y)
                                    (,name ,@(subst `(cons ,x ,y) x formals)))))))

          (defthm ,(mksym name '-of-last)
            (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                     (equal (,name ,@(subst `(last ,x) x formals))
                            t))
            :hints(("Goal" :do-not-induct t)))

          (defthm ,(mksym name '-of-butlast)
            ;; Historically this was much more complicated, but after Matt
            ;; fixed up butlast to not be totally crazy in the -N case
            ;; (introduce NILs, etc.)  it simplifies down nicely.
            (implies (,name ,@(subst `(double-rewrite ,x) x formals))
                     (equal (,name ,@(subst `(butlast ,x ,n) x formals))
                            t))
            :hints(("Goal" :do-not-induct t)))

          (defthm ,(mksym name '-of-rcons)
            (equal (,name ,@(subst `(rcons ,a ,x) x formals))
                   (and ,(if negatedp
                             `(not (,elementp ,@(subst a x elem-formals)))
                           `(,elementp ,@(subst a x elem-formals)))
                        (,name ,@(if true-listp
                                     (subst `(list-fix ,x) x formals)
                                   formals))))
            :hints(("Goal" :in-theory (enable rcons))))

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
                 ;; These aren't needed in the non true-listp case, because set
                 ;; reasoning will reduce them to, e.g., append,
                 ;; set-difference-equal, intersection-equal, etc.
                 `((defthm ,(mksym name '-of-union-equal)
                     (equal (,name ,@(subst `(union-equal ,x ,y) x formals))
                            (and (,name ,@(subst `(list-fix ,x) x formals))
                                 (,name ,@(subst `(double-rewrite ,y) x formals))))
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
                             :in-theory (disable ,(mksym name '-when-subsetp-equal))
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

          )))

    `(defsection ,name
       ,@(and parents `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))
       ;; keep all our deflist theory stuff bottled up.  BOZO encapsulate is
       ;; slow, better to use a progn here
       (encapsulate ()
         . ,events)
       ;; now do the rest of the events with name enabled, so they get included
       ;; in the section
       . ,(and rest
               `((value-triple (cw "Deflist: submitting /// events.~%"))
                 (with-output
                   :stack :pop
                   (progn
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



