; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(include-book "base")

(defxdoc zfc
  :parents (projects)
  :short "Integration of set theory with ACL2"
  :long "<p>This project, in @(see community-books) directory
 @('projects/set-theory/'), develops an integration of first-order set theory
 with ACL2.  As a result, ACL2 can be used as a theorem prover for
 Zermelo-Fraenkel set theory (ZF) with choice (so, ZFC), as explained
 below.</p>

 <p><b>PLEASE NOTE:</b></p>

 <ul>

 <li>This remains work in progress as of April 2025, so substantial changes are
 still possible.</li>

 <li>This documentation is intended to be reasonably self-contained.  Basic
 familiarity with ZF set theory may be helpful but is probably not
 necessary.</li>

 <li>As discussed below, first-order set theory provides the ability to treat
 functions as first-class objects.  In that sense this work provides a
 &ldquo;higher-order&rdquo; capability that is somewhat like what is provided
 by @(tsee apply$).  However, the two approaches have different strengths.
 @('Apply$') has the advantage of supporting @(see lambda)-bindings and also
 the powerful and efficient @(tsee loop$) utility.  The set-theoretic approach
 described here truly provides functions as first-class objects (not merely as
 symbols to be applied) and is more in line with classical mathematics; in
 particular it avoids the notion of @(see tame)ness used with @('apply$').</li>

 </ul>

 <p>To use ACL2 as a set-theory prover one starts with the following command,
 which includes introduction of the @('\"ZF\"') @(see package) used by the
 set-theory books.  This documentation topic displays events as though the
 @(see current-package) is @('\"ZF\"').</p>

 @({
 (include-book \"projects/set-theory/top\" :dir :system)
 })

 <p>There is no use of trust tags (see @(see defttag)), so ACL2 support for set
 theory may seem like magic, as no changes were made to ACL2 that provide such
 support.  How can this be?</p>

 <p>The foundations are laid in the book @('base.lisp') using a zero-ary
 predicate, @('zfc').  Key functions and theorems (really, axioms) are
 introduced in an @(tsee encapsulate) event along with @('zfc').  The theorems
 have @('(zfc)') as a hypothesis, so they trivially hold in the first pass of
 the @('encapsulate') event because the @(see local) witness to @('zfc') is as
 follows.</p>

 @({
 (local (defun zfc () nil))
 })

 <p>This simple trick allows an @('encapsulate') event to export interesting
 theorems, that is, by introducing a zero-ary function whose @(see local)
 witness returns @('nil'), where that function serves as a hypothesis for
 exported theorems.  We will call such a function &mdash; for example, @('zfc')
 &mdash; a <i>hypothesis function</i>.</p>

 <p>Of course, one can always use a hypothesis function to produce any sort of
 theory, reasonable or not.  But we claim that the theorems exported by the
 @('encapsulate') event introducing @('zfc') are meaningful because @('(zfc)')
 can be true!  This claim is the subject of a separate documentation topic; see
 @(see zfc-model); the idea is to represent each concrete ACL2 object as a set.
 Thus, ACL2 natural numbers are finite ordinals, and in particular 0 is the
 empty set; and @(tsee cons) is the ordered-pair constructor.  The key thing to
 understand at this point about this representation is that <i>everything</i>
 is a set: indeed, one can get all sets by starting with the empty set and
 iterating the powerset operation through the ordinals.  See @(see
 zfc-model).</p>

 <p>A nice consequence of this <i>hypothesis function</i> approach (again: use
 of a constrained zero-ary function in hypotheses, witnessed with @('nil')), as
 opposed to using @(tsee defaxiom), is that everything we prove is indeed a
 theorem.  We still need a metatheoretic argument to justify ignoring the
 @('(zfc)') hypotheses; again, see @(see zfc-model).  Another benefit is that
 unlike @('defaxiom'), this approach does not interfere with functional
 instantiation (though it's not clear as of this writing whether that is
 important).</p>

 <p>The @(see events) that are exported by the @(tsee encapsulate) introducing
 @('zfc') may be seen by submitting the command @(':pe zfc') (after evaluating
 the @(tsee include-book) form displayed above).  The next section summarizes
 most of those events, and is followed by sections that further explore the
 integration of set theory with ACL2.</p>

 <h3>Events exported with @('zfc')</h3>

 <p>The @('encapsulate') event introducing @('zfc') introduces set-theoretic
 primitives along with @('zfc'), with the following list of signatures.</p>

 @({
 (((zfc) => *)
  ((in * *) => *)
  ((pair * *) => *)
  ((min-in *) => *)
  ((union *) => *)
  ((omega) => *)
  ((powerset *) => *)
 )
 })

 <p>These are mainly as expected, but here is a summary.</p>

 <ul>

 <li>@('zfc'): discussed above</li>

 <li>@('(in a x)'): set membership &mdash; @('a') is an element of the set
 @('x')</li>

 <li>@('(pair x y)'): unordered pair @('{x,y}')</li>

 <li>@('(min-in x)'): chooses a minimal element of non-empty @('x') (see
 below)</li>

 <li>@('(union x)'): union of the elements of @('x')</li>

 <li>@('(omega)'): the set of natural numbers (finite ordinals)</li>

 <li>@('(powerset x)'): the set of all subsets of @('x')</li>

 </ul>

 <p>That @('encapsulate') event also introduces the following key definitions.
 Others are discussed in our presentation of the model; see @(see
 zfc-model).</p>

 @({
 (defun-sk subset (x y) ; x is a subset of y
   (forall a
           (implies (in a x) (in a y))))

 (defun singleton (x) ; {x}
   (pair x x))

 (defun union2 (x y) ; x U y
   (union (pair x y)))

 (defun-sk in-in (a x) ; a is an element of an element of x
   (exists y (and (in a y) (in y x))))

 })

 <p>Convenient macros @('defthmz'), @('defthmdz'), and @('thmz') generate calls
 of @(tsee defthm), @(tsee defthmd), and @(tsee thm), respectively, in which
 @('(force (zfc))') has been added as a hypothesis.  These macros are used in
 most of the theorems exported from the @('encapsulate') that introduces
 @('zfc').  Here is one of those, stating that two sets are equal when they
 have the same elements.  (Recall that in our setting, everything is a
 set.)</p>

 @({
 (defthmdz extensionality
   (implies (and (subset x y)
                 (subset y x))
            (equal (equal x y)
                   t)))
 })

 <p>And here is its expansion (as seen using @(':')@(tsee trans1)), where
 @('(force? x)') is a macro call expanding to @('(force x)') if @('x') is
 either @('(zfc)') or of the form @('(foo$prop)') for some symbol @('foo'), and
 is @('x') otherwise.</p>

 @({
 (defthmd extensionality
   (implies (and (subset x y)
                 (subset y x)
                 (force? (zfc)))
            (equal (equal x y) t)))
 })

 <p>Here are other exported theorems.  Those that pertain to the representation
 of ACL2 objects as sets are omitted here; see @(see zfc-model).</p>

 @({
 (defthm booleanp-in
   (booleanp (in x y))
   :rule-classes :type-prescription)

 (defthmz min-in-1 ; (min-in z) picks an element of z when z is non-empty
   (equal (in (min-in z) z)
          (not (equal z 0))))

 (defthmz min-in-2 ; (min-in z) is minimal in that it does not intersect z
   (implies (in a z)
            (not (in a (min-in z)))))

 (defthm min-in-0 ; just a default
   (equal (min-in 0) 0))

 (defthmz in-pair ; the unordered pair {x,y} contains just x and y
   (equal (in a (pair x y))
          (or (equal a x) (equal a y))))

 (defthmz in-union ; (union x) contains the elements of elements of x
   (equal (in a (union x))
          (in-in a x)))

 (defthmz infinity ; our version of the axiom of infinity from ZF
   (equal (in n (omega)) (natp n)))

 (defthmz in-powerset
   (equal (in a (powerset x))
          (subset a x)))

 (defthm 0-is-emptyset
   (not (in a 0)))
 })

 <p>All of these theorems are essentially trivial consequences of ZF, except
 that the ones using @('min-in') implement not only ZF's Axiom of Regularity
 but also a form of global choice.  It is well known that this puts us in a
 conservative extension of ZFC (also see @(see zfc-model)).</p>

 <h3>Relations, functions, and their application</h3>

 <p>As usual, we consider a set to be a <i>relation</i> if it is a set of
 ordered pairs; this set is a <i>function</i> if furthermore, there is always
 at most one such @('y') for each @('x').  Recall that in our setting, @(tsee
 cons) is the ordered-pair constructor; thus the ordered pair of @('x') and
 @('y'), which in set theory is generally defined as @('{{x},{x,y}}'), is given
 by @('(cons x y)').</p>

 @({
 (defun-sk relation-p (r)
   (forall p
           (implies (in p r) (consp p)))
   :rewrite :direct)

 (defun-sk funp (f)
   (forall (p1 p2)
           (non-exec (and (relation-p f)
                          (implies (and (in p1 f)
                                        (in p2 f)
                                        (not (equal p1 p2)))
                                   (not (equal (car p1) (car p2)))))))
   :rewrite :direct)
})

 <p>We next introduce function application, @('(apply r x)'), not only for
 functions but for relations.  (Aside: Recall that we are working in the
 @('\"ZF\"') package; so here, @('apply') refers to @('zf::apply'), which is
 different from @('common-lisp::apply').)  The idea is that @('(apply r x)') is
 some @('y') such that the ordered pair @('(cons x y)') is an element of
 @('r').  The following event captures that idea.</p>

 @({
 (defchoose apply-base (y)
   (r x)
   (in (cons x y) r))
 })

 <p>However, it seems convenient to provide a default for the case that @('x')
 is not in the domain of @('r').  (We discuss formalization of domains further
 below.)  So we actually define function (and relation) application as
 follows.</p>

 @({
 (defun apply (r x)
   (declare (xargs :guard t))
   (let ((y (apply-base r x)))
     (if (in (cons x y) r)
         y
       0)))
 })

 <h3>Axiom schemes and their implementation with @('zsub') and @('zfn')</h3>

 <p>ZF is typically formulated not only with axioms as discussed above, but
 also with two axiom schemes: Comprehension (or Subset), which asserts that
 every definable subcollection of a set is a set; and Replacement, which
 asserts that a definable function maps into a set.  Versions of these schemes
 are implemented with macros @('zsub') and @('zfn'), which we now discuss in
 turn.</p>

 <p>The macro @('zsub') implements the Comprehension scheme.  If @('name') is a
 new name, @('(v1..vn)') is a formal parameters list, @('x') is a variable, and
 @('s') and @('prop') are terms, then @('(zsub name (v1..vn) x s u)')
 introduces a function (name v1..vn) = @('{x \in s: u}').  Here @('(v1..vn)')
 should include all variables occurring free in @('s') or @('u') other than
 @('x'), and must not occur in @('s').</p>

 <p>@('Zsub') is used for defining the domain of a relation.  Noted above is
 that @(tsee cons) is the ordered-pair constructor.  Consider an ordered pair
 @('<x,y>') = @('(cons x y)').  But the traditional set-theoretic definition of
 @('<x,y>') is: @('{{x},{x,y}}').  Thus for every @('<x,y>') in a set @('r'),
 @('{x}') is in the union of the elements of @('r'), i.e., in @('(union r)');
 hence @('x') is in @('(union (union r))').  Thus, the domain of @('r') can
 be defined using Comprehension as follows.</p>

 @({
 {x in (union (union r)): (in (cons x (apply r x)) r)}
 })

 <p>That definition is captured by the following invocation of @('zsub').</p>

 @({
 (zsub domain (r)                  ; name, args
       x                           ; x
       (union (union r))           ; s
       (in (cons x (apply r x)) r) ; u
       )
 })

 <p>That form generates an @(tsee encapsulate) event that constrains a function
 @('domain$prop') of no arguments and a function @('(domain r)'), exporting
 the following key property of @('domain').</p>

 @({
 (defthm domain$comprehension
   (implies (force (domain$prop))
            (equal (in x (domain r))
                   (and (in x (union (union r)))
                        (in (cons x (apply r x)) r)))))
 })

 <p>This is a typical use of @('zsub').  Many other uses may be found in the
 @(see community-books) directory, @('projects/set-theory/').</p>

 <p>Recall our trick of introducing a zero-ary <i>hypothesis function</i>,
 @('zfc'), in an @('encapsulate') event, to use in hypotheses of theorems
 exported from that @('encapsulate').  Similarly, the use of @('zsub') above
 has introduced the zero-ary function @('domain$prop') and used it in the
 hypothesis of the key property of @('domain'), displayed above.  Our
 explanation in documentation topic @(see zfc-model) provides consistent ACL2
 theories in which @('(zfc)') holds as do all hypothesis functions from
 invocations of @('zsub') and @('zfn').  That gives us justification for
 ignoring all such hypotheses in our theorems.</p>

 <p>This observation, that we can ignore such hypothesis functions, is
 supported by a keyword, @(':props'), for the @('defthmz'), @('defthmdz'), and
 @('thmz') macros.  The value of this keyword defaults is a list of symbols
 that defaults to @('(zfc)'), but this list can also include hypothesis
 functions introduced by @('zsub') or @('zfn').  So we could have written the
 @(tsee defthm) event introducing @('domain$comprehension') (above) as
 follows.</p>

 @({
 (defthmz domain$comprehension
   (equal (in x (domain r))
          (and (in x (union (union r)))
               (in (cons x (apply r x)) r)))
   :props (domain$prop))
 })

 <p>For each symbol @('p') in the list of @(':props'), @('(force? p)') is added
 as a hypothesis (after any existing hypotheses).  The point of @(':props') is
 that if we consider our events to be about the integration of set theory and
 ACL2 (see @(see zfc-model)), then we can ignore those properties because they
 are all true in that integration.</p>

 <p>Thus, each symbol in @(':props') undergoes a check that guarantees that it
 can be ignored in our intended ZFC integration.  The check is that the symbol
 either is @('zfc') or is a key @('p') of a certain @(see table),
 @('zfc-table').  That table associates @('p') either with an existing
 @('zsub') or @('zfn') event introducing @('p') as its hypothesis function, or
 else with a form @('(and (q0) (q1) ... (qk))') where each @('qi') is a key of
 @('zfc-table').  An event @('(extend-zfc-table p q0 q1 ... qk)') introduces a
 new zero-ary macro name, @('p'), which expands to @('(and (q0) (q1)
 ... (qk))') and makes the above table entry.  For example, the following event
 introduces @('zify-prop'), to be used further below, as the conjunction of
 @('(prod2$prop)'), @('(domain$prop)'), @('(inverse$prop)'), and @('(zfc)'),
 and makes a suitable note in the @('zfc-table').</p>

 @({
 (extend-zfc-table zify-prop
                   prod2$prop domain$prop inverse$prop zfc)
 })

 <p>We turn now to the macro @('zfn'), which implements a version of the
 Replacement scheme.  It will likely be used much less frequently than
 @('zsub').  The general form is @('(zfn fn args x y bound u)').  Think of
 @('u') as a property that associates some values of @('x') in a set,
 @('bound'), with corresponding @('y'); then @('fn') is a function associating
 each such @('x') with a corresponding @('y').  More precisely, @('u') is a
 term typically mentioning @('x') and @('y') and perhaps other variables, where
 those others are all in @('args'); then @('fn') has formal parameters list
 @('args') and the application @('(fn . args)') produces a set of ordered
 pairs, namely a function mapping suitable @('x') in @('bound') to suitable
 @('y'), as described above (i.e., satisfying @('u')).  Thus, @('(zfn fn args x
 y bound u)') introduces the following axioms, each conditionalized with a
 hypothesis function obtained by adding suffix @('\"$PROP\"') to @('fn').  Here
 we show the special case (which is actually quite typical) that @('args') is
 @('()'); otherwise replace @('(fn)') below by @('(fn arg1 .. argk)') where
 @('args') is @('(arg1 .. argk)').</p>

 @({
 (funp (fn))
 (subset (domain (fn)) bound)
 (implies (and (in x bound)
               u)
          (in x (domain (fn))))
 (implies (equal y (apply (fn) x))
          u)
 })

 <p>Let's see a use of @('zfn') in the book @('base.lisp'), to define a
 function (as an ACL2 object) with domain the set @('(omega)') of natural
 numbers, which maps each natural number @('x') to the value @('(v-map x)'),
 as described further below.</p>

 @({
 (zfn v                             ; name
      ()                            ; args
      x                             ; x
      y                             ; y
      (omega)                       ; bound
      (equal (equal y (v-map x)) t) ; u
      )
 })

 <p>The nature of @('v-map') isn't important here, but for those interested, we
 note that for a natural number @('n'), @('(v-map n)') is the result of
 iterating the powerset operation @('n') times on the empty set, @('0').  The
 definition of @('v-map') is a typical ACL2 recursive definition, which
 illustrates a cool benefit of combining ACL2 with ZF in this way: the richness
 of ZF is combined with ACL2 mechanization, including induction and
 recursion.</p>

 @({
 (defun v-map (n)
   (declare (type (integer 0 *) n))
   (if (zp n)
       0
     (powerset (v-map (1- n)))))
 })

 <p>Now that we have an ACL2 object, @('(v)'), that is a function mapping each
 natural number @('n') to @('(v-map n)'), we define the union of these
 @('(v-map n)') as follows.  See @('base.lisp') for the definition of the image
 of a function @('fn'), @('(image fn)').</p>

 @({
 (defun v-omega nil
   (declare (xargs :guard t))
   (union (image (v))))
 })

 <p>Future work may introduce ordinal recursion to extend this sort of
 construction through the ordinals.</p>

 <h3>Higher-order capabilities using @('zify') and @('zify*')</h3>

 <p>If an ACL2 function @('F_A') is represented as a constant @('(F)') that
 denotes a function object (which is a set of ordered pairs), then @('(F)') can
 be applied to an argument @('s') with @('(apply (F) s)').  Although that
 application will not be executable, nevertheless, during a proof @('(apply (F)
 s)') might be rewritten to @('(F_A s)'), which may be executable.</p>

 <p>We thus see that ACL2 has a sort of &ldquo;higher-order&rdquo; capability.
 Consider the simple example of a standard mapping function.</p>

 @({
 (defun map (f lst)
   (declare (xargs :guard (true-listp lst)))
   (cond ((endp lst) nil)
         (t (cons (apply f (car lst))
                  (map f (cdr lst))))))
 })

 <p>It is easy for ACL2 to prove generic properties of @('map') automatically,
 like the following.</p>

 @({
 (defthm map-append
   (equal (map f (append x y))
          (append (map f x) (map f y))))
 })

 <p>A second generic property proved automatically by ACL2 is the following,
 about mapping the composition of two functions over a list.  (See
 @('base.lisp') for the definition of @('compose') using @('zsub') and the
 definition of @('list-to-set').)</p>

 @({
 (defthmz map-compose
   (implies (and (force (funp f))
                 (force (funp g))
                 (force (subset (list-to-set lst) (domain g))))
            (equal (map (compose f g) lst)
                   (map f (map g lst))))
   :props (zfc domain$prop prod2$prop compose$prop inverse$prop))
 })

 <p>Now suppose we want to map a given ACL2 function over a list using
 @('map').  For that, we need to create a set-theoretic function object (set of
 ordered pairs) corresponding to that ACL2 function.  This section uses
 examples to describe the use of macros @('zify') and @('zify*') to create such
 function objects.  These examples should give a good idea of how to use these
 macros, but more documentation may appear later, especially if requested by
 someone who expects to use these macros.  Note that the word
 &ldquo;zify&rdquo; may be pronounced to rhyme with &ldquo;reify&rdquo;, which
 is appropriate since @('zify') takes an existing ACL2 function symbol and
 essentially realizes (i.e., reifies) it as a set-theoretic (or ZF) function: a
 set of ordered pairs.  Both @('zify') and @('zify*') invoke @('zsub') to
 create the desired function.</p>

 <p>Consider for example the standard definition of a Fibonacci function.</p>

 @({
 (defun fib (n)
   (declare ...)
   (cond ((zp n) 0)
         ((= n 1) 1)
         (t (+ (fib (- n 1)) (fib (- n 2))))))
 })

 <p>Evaluation of the following macro creates a zero-ary function, @('zfib'),
 which agrees with @('fib') on the natural numbers.  The @(':dom') and
 @(':ran') arguments specify the natural numbers as the domain and
 codomain (i.e., range, i.e., a set containing the image).</p>

 @({
 (zify zfib fib :dom (omega) :ran (omega))
 })

 <p>Now ACL2 accepts the following events.  The first illustrates that
 evaluation can be carried out, as explained further below.</p>

 @({
 (thmz (equal (map (zfib) '(0 1 2 3 4 5 6 7))
              '(0 1 1 2 3 5 8 13))
       :props (zify-prop zfib$prop))

 (defun map-fib (lst)
   (declare (xargs :guard (nat-listp lst)))
   (cond ((endp lst) nil)
         (t (cons (fib (car lst))
                  (map-fib (cdr lst))))))

 (defthmz map-zfib
   (implies (nat-listp lst)
            (equal (map (zfib) lst)
                   (map-fib lst)))
   :props (zify-prop zfib$prop))
 })

 <p>The following lemma is generated by the @('zify') call above, and is used
 by the ACL2 rewriter to replace an application of @('(zfib)') by a
 corresponding call of @('fib').  That, in particular, supports the use of
 evaluation in the proof of the first event in the display just above.</p>

 @({
 (defthmz zfib-is-fib
   (implies (natp n)
            (equal (apply (zfib) n)
                   (fib n)))
   :props (zfc prod2$prop zfib$prop domain$prop))
 })

 <p>Here is the definition of a version of another common higher-order
 function, @('foldr').</p>

 @({
 (defun foldr (lst fn init)
   (declare (xargs :guard (true-listp lst)))
   (if (endp lst)
       init
     (apply fn
            (list (car lst)
                  (foldr (cdr lst) fn init)))))
 })

 <p>That definition may be found in the book @('foldr.lisp'), which also
 contains the following events.  The function @('zcons-when-fn*') is produced
 by an analogue of @('zify'), namely @('zify*'), which is suitable for
 functions of more than one argument.</p>

 @({
 (defun filter (fn lst)
   (declare (xargs :guard (true-listp lst)))
   (cond ((endp lst) nil)
         ((apply fn (car lst))
          (cons (car lst) (filter fn (cdr lst))))
         (t (filter fn (cdr lst)))))

 (defun cons-when-fn (x y fn)
   (declare (xargs :guard t))
   (if (apply fn x)
       (cons x y)
     y))

 (zify* zcons-when-fn* cons-when-fn
        2 ; arity

 ; A function from A to B is a set of ordered pairs <a,b> where a is in A
 ; and b is in B, hence a subset of A X B.  The domain is thus specified
 ; just below by the Cartesian product of (acl2) with itself, where (acl2)
 ; is the set of good ACL2 objects as described in the next section.

        :dom (prodn (acl2) (acl2))
        :params (fn)
        :props (v$prop acl2$prop))

 (thmz (equal (foldr '(1 4 9 16 25 36 100)
                      (zcons-when-fn* (zevenp))
                      nil)
              '(4 16 36 100))
       :props (foldr-prop zcons-when-fn*$prop zevenp$prop))

 (thmz (implies (and (zcons-when-fn*$prop)
                     (acl2p lst) ; defined in the next section
                     )
                (equal (foldr lst (zcons-when-fn* f) nil)
                       (filter f lst)))
       :props (foldr-prop zcons-fn*$prop))

 ; A computation example.

 (zify zevenp evenp)

 (thmz (equal (foldr '(1 4 9 16 25 36 100)
                      (zcons-when-fn* (zevenp))
                      nil)
              '(4 16 36 100))
       :props (foldr-prop zcons-when-fn*$prop zevenp$prop))
 })

 <h3>The set of &rdquo;good&rdquo; ACL2 objects</h3>

 <p>A <i>good</i> ACL2 object is one that is built from the usual
 atoms (numbers, symbols, characters, and strings) by closing under
 @('cons').</p>

 @({
 (defun acl2p (x)
   (declare (xargs :guard t))
   (cond ((consp x) (and (acl2p (car x))
                         (acl2p (cdr x))))
         ((bad-atom x) nil)
         (t t)))
 })

 <p>The set @('(v-omega)'), introduced above, is a set containing every good
 ACL2 object.</p>

 @({
 (defthmz v-omega-contains-acl2p
   (implies (acl2p x)
            (in x (v-omega)))
   :props (zfc v$prop domain$prop prod2$prop inverse$prop)
   :hints ((\"Goal\" :in-theory (enable bad-atom))))
 })

 <p>By Comprehension we may define the set of good ACL2 objects.</p>

 @({
 (zsub acl2 ()    ; name, args
       x          ; x
       (v-omega)  ; s
       (acl2p x)  ; u
       )
 })

 <p>The book @('prove-acl2p.lisp') defines a macro, @('prove-acl2p'), to prove
 that a given ACL2 function returns a good ACL2 object on good ACL2 inputs.
 For example, the call @('(prove-acl2p len)') generates and proves the
 following theorem.</p>

 @({
 (defthm acl2p-len
   (implies (acl2p x) (acl2p (len x)))
   :hints ((\"Goal\" :in-theory (enable len))))
 })

 <p>That book then proves such a theorem for most ACL2 primitives.</p>

 <p>It is useful that there is a set of all good ACL2 objects.  An example is
 given by the call @('(zify* zcons-when-fn* cons-when-fn ...)') above.</p>

 <h3>Further remarks and results</h3>

 <p>A design goal in this project was for ACL2 to be a useful set-theory
 prover.  A system like <a
 href='https://isabelle.in.tum.de/dist/Isabelle2024/doc/logics-ZF.pdf'>Isabelle
 ZF</a> may be more foundational.  For example, we took the shortcut of
 introducing @('(omega)') rather than a more traditional formulation of the
 Axiom of Infinity, so that membership in @('(omega)') would be represented by
 @('natp').</p>

 @({
 (defthmz infinity
   (equal (in n (omega))
          (natp n)))
 })

 <p>Of course ZF proves that the ordinal &omega; exists, which justifies the
 introduction of the constant @('(omega)') with the property displayed
 above.</p>

 <p>More significantly perhaps, we took the shortcut of using @(tsee cons) for
 ordered pairs and @(tsee consp) to recognize them.  So for example, destructor
 elimination may be used automatically in proofs about ordered pairs.  We also
 identified finite ordinals with natural numbers, about which there are vast
 libraries of rules and built-in linear arithmetic procedures, and of course
 efficient evaluation may be performed in ACL2.</p>

 <p>Much of the content of the books in @('projects/set-theory/'), and even
 content in the key book @('base.lisp') in that directory, is not discussed
 here.  You are invited to browse those books, which may well be developed
 further over time.</p>")

(defxdoc zfc-model

; Apparently Zermelo set theory with global choice, which omits the Replacement
; Axiom Scheme from ZFC, is not conservative over Zermelo set theory: see
; "Global choice is not conservative over local choice for Zermelo set theory"
; by Elliot Glazer, https://arxiv.org/abs/2312.11902.  But since our foundation
; is ZFC, that observation does not affect us; for ZFC, conservativity of
; global choice is proved in "Comparison of the axioms of local and universal
; choice" by Ulrich Felgner in Fundamenta Mathematicae (1971) Volume: 71,
; Issue: 1, page 43-62 (http://matwbn.icm.edu.pl/ksiazki/fm/fm71/fm7113.pdf).

  :parents (zfc)
  :short "Justification for integrating set theory with ACL2"
  :long "<p>See @(see zfc) for an introduction to the integration of set theory
 with ACL2.  The present topic provides intuition and sketches a foundation for
 that integration.</p>

 <p>This documentation topic displays events as though the @(see
 current-package) is @('\"ZF\"').</p>

 <h3>Our first-order set theory</h3>

 <p>Before we get to the question of how set theory and ACL2 are integrated,
 let's discuss the relevant set theory.</p>

 <p>Our formalization of set theory starts with <a
 href='https://en.wikipedia.org/wiki/Zermelo-Fraenkel_set_theory'>Zermelo-Fraenkel
 set theory</a>, typically known as ZF.  It is a first-order theory that
 formalizes familiar properties of sets: given @('x') and @('y') there is a
 <i>pair set</i> @('{x,y}') (i.e., unordered pairs exist), there is an infinite
 set, and so on.  Our foundation is actually ZFG, which is ZF extended by the
 axiom of <a href='https://en.wikipedia.org/wiki/Axiom_of_global_choice'>global
 choice</a>.  ZFG adds a function symbol, say @('G'), to the language of ZF and
 adds the axiom that @('G(x)') is an element of @('x') for every non-empty
 @('x').  (Our formalization actually uses the name @('min-in') rather than
 @('G'); see @(see zfc).)</p>

 <p>ZF captures the notion of set provided by the so-called <i>cumulative
 hierarchy</i>: start with the empty set, and then iterate the powerset (set of
 all subsets) operation.  Iteration is through the <i>ordinals</i>, which can
 be viewed as follows.  The least ordinal is 0, which is the empty set.  More
 generally, each natural number @('n') is an ordinal, namely, the set of
 natural numbers less than @('n').  Thus, the less-than relation (@('<')) on
 natural numbers is simply set membership.  Yet more generally, an
 <i>ordinal</i> is any set that is <i>transitive</i> &mdash; every element of
 an element is an element &mdash; and is linearly ordered by set membership.
 The first infinite ordinal, <i>&omega;</i>, is the set of all natural numbers;
 next is &omega;+1, which is the union of &omega; and {&omega;}, next,
 &omega;+2, and so on, with &omega;+n+1 equal to the union of &omega;+n and
 {&omega;+n}.  The union of all these &omega;+i is &omega;+&omega;, also known
 as &omega;*2; and so on.  See @(see o-p) for more about ordinals.</p>

 <p>In ZF, every object is a set that is contained in a member of the
 <i>cumulative hierarchy</i> V_0, V_1, V_2, ..., V_&omega;, V_{&omega;+1}, ...,
 V_{&omega;*2}, ....  In general V_{&alpha;+1} is the powerset of V_&alpha;,
 and for a <i>limit ordinal</i> &alpha; &mdash; one that is not an immediate
 successor, such as &omega; &mdash; V_&alpha; is the union of {V_&beta;: &beta;
 \\in &alpha;}.</p>

 <h3>Defining ACL2 objects in set theory</h3>

 <p>Recall (see @(see zfc)) the notion of a <i>hypothesis function</i>: a
 zero-ary function constrained by an @('encapsulate') event that serves as a
 hypothesis for most of the theorems exported from that @('encapsulate') event.
 Thus, @('zfc'), as well as hypothesis functions introduced by calls of
 @('zsub') and @('zfn'), may appear in @(':props') arguments of @('defthmz')
 events.  Those arguments generate hypotheses that are necessary for
 provability, but we would like a logical basis for ignoring them.  The rest of
 this documentation topic gives that logical basis.</p>

 <p>In a nutshell, that logical basis is provided by showing how ACL2 data and
 functions can be defined in the ZFG universe of sets, with all hypothesis
 function calls being true.  Then assuming ZF is consistent &mdash; hence, as
 is well-known, so are ZFC and also ZFG &mdash; every defaxiom-free ACL2 theory
 extended by all @(':props') calls, including @('(zfc)'), is consistent by
 virtue of being true in that universe.  We give more details in the next
 section, but for now we simply explain how ACL2 objects are defined in set
 theory.</p>

 <p>The first step is to identify each ACL2 natural number with the
 corresponding finite ordinal.  We next define the other usual atoms &mdash;
 integers, rationals, complex rationals, characters, strings, and symbols
 &mdash; by encoding them as sets.  By treating @(tsee cons) as the
 set-theoretic ordered-pair constructor as explained below, we are able to
 identify all <i>good</i> ACL2 objects &mdash; those built up from those atoms
 using @('cons') &mdash; as sets, hence, those ACL2 objects that are definable
 in ZFG.  Here is the recognizer for the good ACL2 objects.</p>

 @({
 (defun acl2p (x)
   (declare (xargs :guard t))
   (cond ((consp x) (and (acl2p (car x))
                         (acl2p (cdr x))))
         ((bad-atom x) nil)
         (t t)))
 })

 <p>Every good ACL2 object, when interpreted as a set as described below, is in
 a finite stage of the cumulative hierarchy.</p>

 @({
 (defthmz v-omega-contains-acl2p
   (implies (acl2p x)
            (in x (v-omega)))
   :props (zfc v$prop domain$prop prod2$prop inverse$prop)
   :hints ...)
 })

 <p>The @('encapsulate') event introducing @('zfc') exports many basic
 theorems.  Many of those are noted in the documentation topic, @(see zfc), but
 not mentioned there are those exported theorems pertaining to the encoding of
 good ACL2 objects as sets.  A key property, alluded to above, is to interpret
 @('(cons x y)') as the set-theoretic ordered pair.  That is traditionally the
 set @('{{x},{x,y}}'), formalized as follows.</p>

 @({
 (defthmdz cons-as-ordered-pair
   (equal (cons x y)
          (pair (singleton x)
                (pair x y))))
 })

 <p>Note that a cons is never a natural number, because @('(cons x y)') =
 @('{{x},{x,y}}') is always a non-empty set that does not contain 0 (the empty
 set), but no finite ordinal has that property.  Also note that a cons always
 has at most two elements.</p>

 <p>We encode the other atoms as sets of the form @('(zf::ztriple y z)') =
 @('{0,y,z}'), where @('y') is a positive natural number and @('z') is not a
 natural number &mdash; in fact @('z') will always be a cons.  Thus each such
 set is a three-element set, hence is not a cons.  It is also not a natural
 number (finite ordinal) since its element @('z') is not a natural number.  And
 finally, these are clearly distinct for different natural numbers @('y').  The
 interpretations are as follows, where @('make-listp0') creates a list
 terminated with @('0') rather than @('nil'), to avoid potential circularity in
 the encoding of the symbol, @('nil').</p>

 @({
 (defun negative-int-as-ztriple (x)
   (declare (xargs :guard (and (integerp x)
                               (< x 0))))
   (ztriple 1 (cons (- x) 0)))

 (defun integer-as-ztriple (x)
   (declare (xargs :guard (integerp x)))
   (if (< x 0)
       (negative-int-as-ztriple x)
     x))

 (defun numerator-as-ztriple (x)
   (declare (xargs :guard (rationalp x)))
   (integer-as-ztriple (numerator x)))

 (defun ratio-as-ztriple (x)
   (declare (xargs :guard (and (rationalp x)
                               (not (integerp x)))))
   (ztriple 2 (cons (numerator-as-ztriple x) (denominator x))))

 (defun complex-as-ztriple (x)
   (declare (xargs :guard (and (complex-rationalp x)
                               (not (rationalp x)))))
   (ztriple 3 (cons (realpart x) (imagpart x))))

 (defun character-as-ztriple (x)
   (declare (xargs :guard (characterp x)))
   (ztriple 4 (cons (char-code x) 0)))

 (defun string-as-ztriple (x)
   (declare (xargs :guard (stringp x)))
   (ztriple 5 (cons (make-listp0 (coerce x 'list)) 0)))

 (defun symbol-as-ztriple (x)
   (declare (xargs :guard (symbolp x)))
   (ztriple 6 (cons (string-as-ztriple (symbol-package-name x))
                    (string-as-ztriple (symbol-name x)))))
 })

 <p>These functions are then asserted to define the encodings, as follows.</p>

 @({
 (defthmz negative-int-as-ztriple-identity
   (implies (and (integerp x)
                 (< x 0))
            (equal (negative-int-as-ztriple x)
                   x)))

 (defthmz integer-as-ztriple-identity
   (implies (integerp x)
            (equal (integer-as-ztriple x)
                   x)))

 (defthmz ratio-as-ztriple-identity
   (implies (and (rationalp x)
                 (not (integerp x)))
            (equal (ratio-as-ztriple x)
                   x)))

 (defthmz complex-as-ztriple-identity
   (implies (and (complex-rationalp x)
                 (not (rationalp x)))
            (equal (complex-as-ztriple x)
                   x)))

 (defthmz character-as-ztriple-identity
   (implies (characterp x)
            (equal (character-as-ztriple x)
                   x)))

 (defthmz string-as-ztriple-identity
   (implies (stringp x)
            (equal (string-as-ztriple x)
                   x)))

 (defthmz symbol-as-ztriple-identity
   (implies (symbolp x)
            (equal (symbol-as-ztriple x)
                   x)))
 })

 <p>The ACL2 primitives (function symbols without definitions, such as @(tsee
 char-code) and @(tsee denominator) can easily be defined in set theory so that
 the ACL2 axioms hold.  For example, for a character @('c') =
 @('{0,4,{{n},{n,0}}}'), @('(char-code c)') = @('n'), and for any set @('s')
 not of that form, @('(char-code s)') = @('0').  Terminating recursive
 definitions present no problem, since in ZFG, they are equivalent to explicit
 definitions.  Even @('acl2-count') can easily be interpreted that way,
 notwithstanding its lack of a direct termination argument in ACL2, because the
 <a href='https://en.wikipedia.org/wiki/Von_Neumann_universe'>set-theoretic
 rank</a> decreases when taking the @('car') or @('cdr') of a cons
 @('{{x},{x,y}}'), namely @('x') and @('y') respectively.</p>

 <h3>Interpreting ACL2 theories in set theory</h3>

 <p>We have seen how the good ACL2 objects and ACL2 primitives can be defined
 in ZF.  We have also discussed our formalization of ZFG; see @(see zfc).  In
 this section we sketch an argument for how to interpret an ACL2 theory in ZFG
 so that all hypothesis function calls are true.</p>

 <p>We start with the following definitions.</p>

 <blockquote>

 <p>(a) An ACL2 <i>session</i> is a sequence of @(see events) where every
 axiomatic event is admissible and every alleged theorem TH is indeed a theorem
 of the axiomatic events present at the introduction of TH.  Note that @(tsee
 include-book) events are not part of a session; we essentially consider them
 to be &ldquo;@(see puff)ed&rdquo; away.</p>

 <p>(b) Let EZ be the @(tsee encapsulate) event that introduces the function,
 @('zfc').  An <i>EZ session</i> is a defaxiom-free ACL2 session that includes
 EZ.</p>

 <p>(c) The <i>zfc props</i> of an EZ session are its hypothesis function
 calls.  These are as defined above, i.e., they include @('(zfc)') and calls of
 zero-ary hypothesis functions generated by invocations of @('zsub') and
 @('zfn').  As noted elsewhere (see @(see zfc)), the hypothesis functions are
 exactly the keys of the table, @('zfc-table').</p>

 <p>(d) The <i>ZFG theory</i> of an EZ session is the extension of ZFG by all
 of the following:

 <ul>

 <li>the axiomatic events of the session;</li>

 <li>the comprehension and replacement schemes for the extension of the
 language of ZFG by the function symbols introduced in those axiomatic events;
 and</li>

 <li>all zfc props of the session.</li>

 </ul></p>

 </blockquote>

 <p>Then we claim the following.</p>

 <blockquote>

 <p>(1) The ZFG theory of an EZ session is consistent, assuming that ZF is
 consistent.</p>

 <p>(2) For every theorem event in an EZ session, if we remove all zfc props
 from its hypotheses then the result is a theorem of the ZFG theory of the
 session.</p>

 </blockquote>

 <p>In fact (2) is trivial by (d) above.  The import of (1) is that (2) is not
 vacuous: it is about a consistent theory.  Note that (2) allows us to ignore
 all @(':props') arguments of @('defthmz'), @('defthmdz'), and @('thmz') forms,
 when considering whether one has a theorem of the ZFG theory of the
 session.</p>

 <p>The proof of (1) is based on the following notion.  The <i>puffing
 procedure</i> modifies an ACL2 session by eliminating all @('encapsulate')
 events and exposing all @(see local) events, renaming as necessary.  Note that
 the result is still an ACL2 session: in particular, there is no concern about
 functional instantiation, because the notion of ACL2 session is about
 theoremhood, not provability with ACL2.  The <i>ZFG puffing procedure</i> is
 similar, except that every key of the zfc table is witnessed with the constant
 function, t.  The <i>initial ZFG session</i> is the extension of the
 boot-strap by EZ.  Note that every EZ session has the same theory as one
 extending the initial ZFG session: simply move the EZ event to be the first
 after the boot-strap.</p>

 <p>Claim.  Given an EZ session s1 extending the initial ZFG session, let
 s2 be the result of applying the ZFG puffing procedure to s1.  Then s2
 is consistent.</p>

 <p>The proof is by induction on sessions.  The initial EZ session is no
 problem, as the definitions in EZ are made explicit in zf plus global choice.
 As we puff, we can replace each definition with an explicit definition in ZFG;
 this is true even for (mutually) recursive definitions because of the measure
 theorem.  Each defchoose can be replaced by an explicit definition too, using
 global choice.  The result consists entirely of extensions using explicit
 definitions, hence preserves consistency, comprehension, and replacement.</p>

 <h3>Final remarks</h3>

 <p>Note that we have not worked out such an argument for ACL2(r) (see @(see
 real)).</p>

 <p>When one uses trust tags (see @(see defttag)) in a session, then as usual,
 this carries is a responsibility to ensure soundness.  In particular, if a
 @(tsee partial-encapsulate) event is accompanied by raw Lisp definitions, then
 there is a responsibility to guarantee that the implicit exported theorems
 hold in the ZFG theory of the session.</p>")

(defpointer set-theory zfc)

#|
 The boot-strap theory is a
 consequence of ZF



 Those theorems are

that an @(tsee encapsulate) event introduces a
 zero-ary function, @('zfc'), that serves as a hypothesis for most of the
 theorems exported from that @('encapsulate') event.  Those theorems are
 provable because the @(see local) witness for @('zfc') is defined to return
 @('nil').  There are also zero-ary-

 <p>The following predicate recognizes the ACL2 objects that one could, at
 least in principle, encounter during evaluation.</p>



 <p>
|#
