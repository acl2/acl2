; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

; core.lisp - fundamental operations, e.g., ubddp, eval-bdd, q-not, and q-ite.

(in-package "ACL2")
(include-book "misc/definline" :dir :system)
(include-book "../misc/memory-mgmt-logic")
(include-book "misc/computed-hint-rewrite" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc ubdds
  :parents (boolean-reasoning)
  :short "A @(see hons)-based, unlabeled <a
href='http://en.wikipedia.org/wiki/Binary_decision_diagram'>Binary Decision
Diagram</a> (bdd) representation of Boolean functions."

  :long "<p>UBDDs (\"unlabeled bdds\") are a concise and efficient
implementation of binary decision diagrams.  Unlike most BDD packages, our
internal nodes are not labelled; instead, each node's depth from the root
determines its variable.</p>

<p>The valid UBDDs are recognized by @(see ubddp).  Structurally, UBDDs are a
subset of purely Boolean cons-trees, i.e., trees where all the tips are @('t')
or @('nil').  For instance, the valid one-variable UBDDs are:</p>

<ul>
<li>@('t') or @('nil')  for \"var is irrelevant to this decision\", or</li>
<li>@('(t . nil)')      for \"if var then @('t') else @('nil'), or</li>
<li>@('(nil . t)')      for \"if var then @('nil') else @('t')</li>
</ul>

<p>But @('(t . t)') and @('(nil . nil)') are not permitted&mdash;we reduce them
to @('t') and @('nil'), respectively.  This restriction leads to a key property
of UBDDs, viz. two UBDDs are semantically equivalent exactly when they are
structurally @(see equal).</p>

<p>The semantics of a UBDD are given by the interpreter function @(see
eval-bdd).  Operations that construct UBDDs, such as @(see q-not) and @(see
q-and), are proven correct w.r.t. this interpreter.  We also provide various
theorems to reason about UBDD operations, including the important theorem @(see
equal-by-eval-bdds), and implement some @(see computed-hints) for automating
the use of this theorem.</p>

<p>Our UBDD implementation is made efficient via @(see hons-and-memoization).
We construct UBDDs with @(see hons) and @(see memoize) UBDD constructors such
as @(see q-not) and @(see q-and).</p>")

;;; THE CORE UBDD OPERATIONS

(defsection ubddp
  :parents (ubdds)
  :short "Recognizer for well-formed @(see ubdds)."
  :long "<p>Note: memoized for efficiency.</p>"

  (defund ubddp (x)
    (declare (xargs :guard t))
    (mbe :logic (if (atom x)
                    (booleanp x)
                  (and (ubddp (car x))
                       (ubddp (cdr x))
                       (if (atom (car x))
                           (not (equal (car x) (cdr x)))
                         t)))
         :exec (cond ((eq x t) t)
                     ((eq x nil) t)
                     ((atom x) nil)
                     (t (let ((a (car x))
                              (d (cdr x)))
                          (cond ((eq a t)
                                 (cond ((eq d nil) t)
                                       ((eq d t) nil)
                                       (t (ubddp d))))
                                ((eq a nil)
                                 (cond ((eq d nil) nil)
                                       ((eq d t) t)
                                       (t (ubddp d))))
                                (t (and (ubddp a) (ubddp d)))))))))

  (memoize 'ubddp :condition '(consp x))

  (defthm ubddp-compound-recognizer
    (implies (ubddp x)
             (or (consp x)
                 (booleanp x)))
    :hints(("Goal" :in-theory (enable ubddp)))
    :rule-classes :compound-recognizer))


(defsection ubdd-listp
  :parents (ubdds)
  :short "Recognizer for a list of @(see ubdds)."

  (defund ubdd-listp (l)
    (declare (xargs :guard t))
    (if (atom l)
        (null l)
      (and (ubddp (car l))
           (ubdd-listp (cdr l)))))

  (local (in-theory (enable ubdd-listp)))

  (defthm ubdd-listp-when-atom
    (implies (atom x)
             (equal (ubdd-listp x)
                    (not x))))

  (defthm ubdd-listp-of-cons
    (equal (ubdd-listp (cons a x))
           (and (ubddp a)
                (ubdd-listp x)))))



(defsection eval-bdd
  :parents (ubdds)
  :short "Sematics of a UBDD."
  :long "<p>@(call eval-bdd) evaluates the UBDD @('x') with respect to a list
of Boolean @('values'), returning a Boolean value which we think of as the
<i>interpretation</i> of @('x') for this particular set of values.</p>

<p>Typically @('x') should be a @(see ubddp) and @('values') should be a @(see
boolean-listp), but we do not enforce this in our @(see guard).</p>

<p>When @('x') is @('t') or @('nil'), it represents a constant function and
always evaluates to itself no matter what @('values') are given for the
variables.</p>

<p>When @('x') is any other tree, we use @('(car values)') to guide us down the
@('car') (the \"true branch\") or @('cdr') (the \"false branch\") of @('x').
In case we run out of @('values'), we pretend that @('values') contains an
infinite list of @('nil')s at the end and just follow the false branches of
@('x') all the way down.</p>"

  (defund eval-bdd (x values)
    (declare (xargs :guard t))
    (cond ((atom x)
           ;; This "if" fixes the result to a Boolean.
           (if x t nil))
          ((atom values)
           (eval-bdd (cdr x) nil))
          ((car values)
           (eval-bdd (car x) (cdr values)))
          (t
           (eval-bdd (cdr x) (cdr values))))))


(defsection qcar
  :parents (ubdds)
  :short "The \"true branch\" of a UBDD."
  :long "<p>@(call qcar) returns the true branch of the UBDD @('x').</p>

<p>For a compound UBDD, i.e., @('(a . b)'), we simply return @('a').  But for
the atomic UBDDs @('t') and @('nil'), which represent the constant functions
@('t') and @('nil'), this is the identity function.</p>"

  (definline qcar (x)
    (declare (xargs :guard t))
    (if (consp x)
        (car x)
      x)))

(defsection qcdr
  :parents (ubdds)
  :short "The \"false branch\" of a UBDD."
  :long "<p>@(call qcdr) returns the false branch of the UBDD @('x').</p>

<p>For a compound UBDD, i.e., @('a . b)'), we simply return @('b').  But for
the atomic UBDDs @('t') and @('nil'), which represent the constant functions
@('t') and @('nil'), this is the identity function.</p>"

  (definline qcdr (x)
    (declare (xargs :guard t))
    (if (consp x)
        (cdr x)
      x)))

(defsection qcons
  :parents (ubdds)
  :short "Raw construtor for UBDDs."
  :long "<p>@(call qcons) constructs the UBDD whose true branch is @('x') and
whose false branch is @('y').  It handles any collapsing which needs to
occur.</p>"

  (definline qcons (x y)
    (declare (xargs :guard t))
    (if (if (eq x t)
            (eq y t)
          (and (eq x nil) (eq y nil)))
        x
      (hons x y))))


(defsection ubdd-constructors
  :parents (ubdds)
  :short "Basic functions for constructing UBDDs.")

(defsection q-not
  :parents (ubdd-constructors)
  :short "Negate a UBDD."
  :long "<p>@(call q-not) builds a new UBDD representing @('(not x)').  That
is, the the following is a theorem:</p>

@({
 (equal (eval-bdd (q-not x) values)
        (not (eval-bdd x values)))
})

<p>Note: memoized for efficiency.</p>"

  (defun q-not (x)
    (declare (xargs :guard t))
    (if (atom x)
        (if x nil t)
      (hons (q-not (car x))
            (q-not (cdr x)))))

  (memoize 'q-not :condition
           '(and (consp x)
                 (or (consp (car x))
                     (consp (cdr x))))))


(defsection q-ite-fn
  :parents (ubdd-constructors)
  :short "Basic way to construct a new if-then-else UBDD."

  :long "<p>@(call q-ite-fn) builds a new UBDD representing @('(if x y z)').
That is, the following is a theorem:</p>

@({
 (equal (eval-bdd (q-ite-fn x y z) values)
        (if (eval-bdd x values)
            (eval-bdd y values)
          (eval-bdd z values)))
})

<p>Normally you will want to use @(see q-ite) instead, which is a macro that is
logically the same as @('q-ite-fn'), but expands into a lazy call of
@('q-ite-fn') and can sometimes avoid the need to evaluate y and z.</p>

<p>Note: memoized for efficiency.</p>"

  (defun q-ite-fn (x y z)
    (declare (xargs :guard t))
    (cond ((null x) z)
          ((atom x) y)
          (t (let ((y (if (hons-equal x y) t y))
                   (z (if (hons-equal x z) nil z)))
               (cond ((hons-equal y z) y)
                     ((and (eq y t) (eq z nil)) x)
                     ;; Calling Q-NOT is meant to improve efficiency.
                     ((and (eq y nil) (eq z t)) (q-not x))
                     (t (qcons (q-ite-fn (car x) (qcar y) (qcar z))
                               (q-ite-fn (cdr x) (qcdr y) (qcdr z)))))))))

#||
 (memoize 'q-ite-fn :condition
          '(and (consp x)
                (consp (car x))
                (consp (cdr x))
                (or (and (consp y) (consp (car y)) (consp (cdr y)))
                    (and (consp z) (consp (car z)) (consp (cdr z))))))
||#

; The above condition doesn't memoize Q-ITE-FN calls that could have
; an enormous test structure, but with the test structure being
; (HONS <atom> <huge-structure>) or (HONS <huge-structure> <atom>).

  (memoize 'q-ite-fn :condition  ;; Changed to this on 9 July 2009
           '(and (consp x)
                 (or (consp (car x))
                     (consp (cdr x))))))


(defsection q-ite
  :parents (ubdd-constructors)
  :short "Optimized way to construct a new if-then-else UBDD."

  :long "<p>@(call q-ite) is a macro that is logically equal to @(call
q-ite-fn).  But in the execution, special measures are taken so that we can
sometimes avoid evaluating @('y') or @('z').</p>

<p>At a first approximation, @(call q-ite) expands into</p>

@({
 (let ((<x> x))
   (cond ((null <x>) z)
         ((atom <x>) y)
         (t
          (let* ((<y> y)
                 (<z> z))
            (q-ite-fn <x> <y> <z>)))))
})

<p>The advantage of this over a raw call of @(see q-ite-fn) is that when the
expression for @('x') evaluates to an atom, then we can avoid evaluating @('y')
or @('z').  Hence, when @('y') or @('z') is expensive to evaluate (e.g.,
perhaps they are terms involving calls to UBDD-building operations like @(see
q-not)), we can save some time.</p>

<p>Of course, if neither @('y') nor @('z') is expensive to evaluate, then the
above just adds some minor overhead to each call of @(see q-ite-fn).  Sometimes
we can avoid this overhead by recognizing that they are cheap to evaluate.  In
particular, we claim that constants and variable symbols are always cheap to
evaluate, and so, if both @('y') and @('z') are either constants or variables,
then we do not bother to introduce the @(see let) statement above and instead
we just lay down a raw call of @(see q-ite-fn).</p>"

  (defmacro q-ite (x y z)
    (cond ((and (or (quotep y) (atom y))
                (or (quotep z) (atom z)))
           `(q-ite-fn ,x ,y ,z))
          (t
           `(mbe :logic (q-ite-fn ,x ,y ,z)
                 :exec (let ((q-ite-x-do-not-use-elsewhere ,x))
                         (cond
                          ((null q-ite-x-do-not-use-elsewhere) ,z)
                          ((atom q-ite-x-do-not-use-elsewhere) ,y)
                          (t
                           (let* ((q-ite-y-do-not-use-elsewhere ,y)
                                  (q-ite-z-do-not-use-elsewhere ,z))
                             (prog2$
                              (last-chance-wash-memory)
                              (q-ite-fn q-ite-x-do-not-use-elsewhere
                                        q-ite-y-do-not-use-elsewhere
                                        q-ite-z-do-not-use-elsewhere)))))))))))


;;; REASONING ABOUT THE CORE OPERATIONS




(defthm equal-of-booleans-rewrite    ; !!! Why is this rule here?
  (implies (and (booleanp x)
                (booleanp y))
           (equal (equal x y)
                  (iff x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))


(defsection eval-bdd
  :extension eval-bdd

  (local (in-theory (enable eval-bdd)))

  (defthm eval-bdd-when-not-consp
    (implies (not (consp x))
             (equal (eval-bdd x values)
                    (if x t nil))))

  (defthm eval-bdd-of-non-consp-cheap
    ;; BOZO rescued from below, blah, bad to have both...?
    (implies (not (consp x))
             (equal (eval-bdd x vals)
                    (if x t nil)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm eval-bdd-of-nil
    (equal (eval-bdd nil values)
           nil))

  (defthm eval-bdd-of-t
    (equal (eval-bdd t values)
           t))

  (defthm eval-bdd-when-non-consp-values
    ;; !!! Could probably be better expressed as a congruence
    ;; rule for a LIST-EQUIV operation.
    (implies (and (syntaxp (not (equal vals *nil*)))
                  (atom vals))
             (equal (eval-bdd x vals)
                    (eval-bdd x nil)))))


(defsection max-depth
  :parents (equal-by-eval-bdds) ;; bozo this is very general...
  :short "Depth of a cons tree."

  (defund max-depth (x)
    (declare (xargs :guard t))
    (if (atom x)
        0
      (1+ (max (max-depth (car x))
               (max-depth (cdr x))))))

  (memoize 'max-depth :condition '(consp x)))


(defsection equal-by-eval-bdds
  :parents (ubdds)
  :short "Reasoning strategy: reduce equality of @(see ubdds) to equality of an
arbitrary evaluation."

  :long "<p>Suppose we know that @('x') and @('y') are @(see ubddp) objects,
and we are trying to prove they are equal.  The @('equal-by-eval-bdds')
approach involves trying to establish this equality by proving the equivalent
fact, roughly:</p>

@({
 (forall values
         (equal (eval-bdd x values)
                (eval-bdd y values)))
})

<p>Actually, we can even assume that @('values') has a certain length and
contains only Booleans, but usually these extra facts are not needed.</p>

<p>It is somewhat tricky to implement this sort of reduction in ACL2.  Our
approach is very similar to the \"pick a point\" strategy for proving that sets
are equal, described in the following paper:</p>

<p>Jared Davis. <a
href='http://www.cs.utexas.edu/~jared/publications/2004-acl2-osets/set-theory.pdf'>
Finite Set Theory based on Fully Ordered Lists.</a> In <a
href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2004/'>ACL2 2004</a>.
November, 2004, Austin, TX, USA.</p>

<p>The computed hint @(see equal-by-eval-bdds-hint) automates the strategy.
That is, when this hint is active, ACL2 will automatically try to use
@('equal-by-eval-bdds') to prove equalities when we can determine (with
rewriting) that @('x') and @('y') are @(see ubddp)s.</p>

<p>At any rate, if you want to prove that @('(foo ...)') and @('(bar ...)') are
equal BDDs, you might start by proving the rules:</p>

@({
 (equal (eval-bdd (foo ...) values)
        (... expression 1 ...))

 (equal (eval-bdd (bar ...) values)
        (... expression 2 ...))
})

<p>Then you will be able to prove @('(equal (foo ...) (bar ...))') by arguing
that expression 1 and expression 2 are equal.</p>"

  ;; We want to write the rule:
  ;;
  ;;    (ubddp x)
  ;;    (ubddp y)
  ;;   -------------
  ;;    (equal x y) = (forall values
  ;;                          (equal (eval-bdd x values)
  ;;                                 (eval-bdd y values)))
  ;;
  ;; But this is not possible to do with a regular rewrite rule due to the
  ;; nested quantifier.  So we instead we begin by expressing our hypotheses as
  ;; a constraint about uninterpreted function symbols.

  (encapsulate
   (((bdd-hyps) => *)
    ((bdd-lhs)  => *)
    ((bdd-rhs)  => *))

   (local (defun bdd-hyps () nil))
   (local (defun bdd-lhs  () nil))
   (local (defun bdd-rhs  () nil))

   (defthmd bdd-equivalence-constraint
     (implies (and (bdd-hyps)
                   (equal (len arbitrary-values)
                          (max (max-depth (bdd-lhs))
                               (max-depth (bdd-rhs))))
                   (boolean-listp arbitrary-values)
                   (ubddp (bdd-lhs))
                   (ubddp (bdd-rhs)))
              (equal (eval-bdd (bdd-lhs) arbitrary-values)
                     (eval-bdd (bdd-rhs) arbitrary-values)))))


  ;; Now we use this constraint to prove a generic theorem that says (bdd-lhs)
  ;; and (bdd-rhs) are equal when the (bdd-hyps) hold.  This takes a bit of
  ;; work because of the weaker constraint we chose above.

  (local (defund find-conflicting-values (x y)
           (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
           (if (or (consp x)
                   (consp y))
               ;; At least one of them is a cons.  We descend both trees and try
               ;; to discover a path that will break their equality.
               (mv-let (car-successp car-path)
                 (find-conflicting-values (qcar x) (qcar y))
                 (if car-successp
                     ;; We took the "true" branch.
                     (mv t (cons t car-path))
                   (mv-let (cdr-successp cdr-path)
                     (find-conflicting-values (qcdr x) (qcdr y))
                     (if cdr-successp
                         (mv t (cons nil cdr-path))
                       (mv nil nil)))))
             ;; Otherwise, both are atoms.  If they are equal, then we have failed to
             ;; find a conflicting path.  But if they are not equal, then this path
             ;; violates their success.
             (mv (not (equal x y)) nil))))

  (local (defthm mv-nth-1
           (equal (mv-nth 1 x)
                  (cadr x))
           :hints(("Goal" :in-theory (enable mv-nth)))))

  (local (defthm lemma1
           (implies (and (ubddp x)
                         (ubddp y)
                         (car (find-conflicting-values x y)))
                    (equal (equal (eval-bdd x (cadr (find-conflicting-values x y)))
                                  (eval-bdd y (cadr (find-conflicting-values x y))))
                           nil))
           :hints(("Goal" :in-theory (enable (:induction find-conflicting-values)
                                             eval-bdd ubddp)
                   :induct (find-conflicting-values x y)
                   :expand ((find-conflicting-values x y))))))

  (local (defthm lemma2
           (implies (and (ubddp x)
                         (ubddp y))
                    (equal (car (find-conflicting-values x y))
                           (not (equal x y))))
           :hints(("Goal" :in-theory (enable (:induction find-conflicting-values)
                                              ubddp)
                   :induct (find-conflicting-values x y)
                   :expand ((find-conflicting-values x y))))))

  (local (defthm lemma3
           (<= (len (cadr (find-conflicting-values x y)))
               (max (max-depth x) (max-depth y)))
           :hints(("Goal" :in-theory (enable (:induction find-conflicting-values)
                                              ubddp)
                   :induct (find-conflicting-values x y)
                   :expand ((find-conflicting-values x y)
                            (max-depth x) (max-depth y))))
           :rule-classes (:linear :rewrite)))

  (local (defthm lemma4
           (boolean-listp (cadr (find-conflicting-values x y)))
           :hints(("Goal" :in-theory (enable find-conflicting-values)))))

  (local (defun extend-to-len (lst n)
           (declare (xargs :guard t))
           (if (zp (nfix n))
               lst
             (if (atom lst)
                 (cons nil (extend-to-len lst (1- n)))
               (cons (car lst) (extend-to-len (cdr lst) (1- n)))))))

  (local (defthm extend-to-len-of-cons
           (equal (extend-to-len (cons a b) n)
                  (cons a (extend-to-len b (1- n))))))

  (local (defun eval-extend-induct (x lst n)
           (if (zp (nfix n))
               (cons lst x)
             (if (atom lst)
                 (list (eval-extend-induct (car x) lst (1- n))
                       (eval-extend-induct (cdr x) lst (1- n)))
               (list (eval-extend-induct (car x) (cdr lst) (1- n))
                     (eval-extend-induct (cdr x) (cdr lst) (1- n)))))))

  (local (defthm eval-bdd-of-extend
           (equal (eval-bdd x (extend-to-len lst n))
                  (eval-bdd x lst))
           :hints (("goal" :in-theory (enable eval-bdd)
                    :induct (eval-extend-induct x lst n)))))

  (local (defthm len-of-extend
           (equal (len (extend-to-len lst n))
                  (max (len lst) (nfix n)))))

  (local (defthm boolean-listp-of-extend
           (implies (boolean-listp lst)
                    (boolean-listp (extend-to-len lst n)))))

  ;; Finally, here is the theorem we are going to functionally instantiate.

  (defthm equal-by-eval-bdds
    (implies (and (bdd-hyps)
                  (ubddp (bdd-lhs))
                  (ubddp (bdd-rhs)))
             (equal (equal (bdd-lhs) (bdd-rhs))
                    t))
    :hints(("Goal"
            :use ((:instance bdd-equivalence-constraint
                             (arbitrary-values (extend-to-len
                                                (cadr (find-conflicting-values
                                                       (bdd-lhs) (bdd-rhs)))
                                                (max (max-depth (bdd-lhs))
                                                     (max-depth (bdd-rhs)))))))))))




(defsection term-is-bdd
  :parents (equal-by-eval-bdds)
  :short "Heuristic for deciding which terms are UBDDs."

  :long "<p>The computed hint @(see equal-by-eval-bdds-hint) is supposed to
automatically apply @(see equal-by-eval-bdds) when we are trying to prove that
two @(see ubdds) are @(see equal).  But a basic prerequisite to being able to
do this is to determine whether the terms on either side of an equality are
actually UBDDs or not.</p>

<p>We use the function @('term-is-bdd') to decide if a particular term is a
BDD.  For variables, we ask the rewriter if the variable is known to be a
@('ubddp').  For quoted constants, we just run @('ubddp') to see if it's a
UBDD.</p>

<p>For function calls, we set up a @('bdd-fns') table that lists functions that
produce BDDs, and we just check whether the function being called is mentioned
in this table.  This is a pretty dumb heuristic, and we may eventually want a
more flexible notion here that allows us to pattern match against @(see
mv-nth)s and so on.</p>

<p>When you add your own BDD producing functions, you may wish to use @(call
add-bdd-fn) to add them to the @('bdd-fns') table.</p>"

  (defmacro bdd-fns ()
    '(cdr (assoc 'bdd-fns (table-alist 'bdd-fns world))))

  (defmacro set-bdd-fns (val)
    `(table bdd-fns 'bdd-fns ,val))

  (defmacro add-bdd-fn (fnname)
    `(set-bdd-fns (cons ',fnname (bdd-fns))))

  (defmacro add-bdd-fns (fnnames)
    `(set-bdd-fns (append ',fnnames (bdd-fns))))

  (set-bdd-fns nil)

  ;; What follows is nasty ACL2 magic.  You probably don't want to try to
  ;; understand it unless you need to.

  (defun term-is-bdd (term hyps whole hist pspv world ctx state)
    ;; This function decides whether we think that TERM is a ubddp.  If it is a
    ;; variable, we ask the rewriter if it's known to be a ubddp.  If it's a
    ;; quoted constant, we see if its value is a ubddp.  And if it's a function
    ;; call, we see if it is one of the functions we explicitly mentioned in
    ;; bdd-fns.
    (declare (xargs :mode :program :stobjs state))
    (cond ((atom term)
           (let ((term-and-ttree
                  (computed-hint-rewrite
                   `(ubddp ,term) hyps t whole hist pspv world ctx state)))
             (equal (car term-and-ttree) *t*)))
          ((eq (car term) 'quote)
           ;; !!! Note to Sol: Jared changed this to ubddp from booleanp.
           (ubddp (cadr term)))
          (t
           (member-eq (car term) (bdd-fns))))))


(defsection equal-by-eval-bdds-hint
  :parents (equal-by-eval-bdds)
  :short "Basic automation of @(see equal-by-eval-bdds)."

  :long "<p>This is a computed hint in the spirits of the ordered sets
library's pick-a-point automation.  It reduces questions of BDD equality to
questions of BDD evaluation.</p>"

  (defun equal-by-eval-bdds-hint-fn (id clause hist pspv ctx stable world state)
    (declare (xargs :mode :program :stobjs state)
             (ignorable id))
    (if (not stable)
        ;; Don't suggest anything until the goal is stable.  This gives other
        ;; rules a chance to fire.
        nil
      (let* ((rcnst (access prove-spec-var pspv :rewrite-constant))
             (ens   (access rewrite-constant rcnst :current-enabled-structure)))
        (if (not (enabled-numep (fnume '(:rewrite equal-by-eval-bdds) world) ens))
            ;; Don't suggest anything if equal-by-eval-bdds is
            ;; disabled.  This gives the user an easy way to turn off
            ;; the strategy.
            nil
          (let ((conclusion (car (last clause))))
            (if (not (and (consp conclusion)
                          (or (eq (car conclusion) 'equal)
                              (eq (car conclusion) 'not))))
                nil
              ;; We look for conclusions of the form (equal lhs rhs)
              ;; or (not lhs).  We think of (not lhs) as the same as
              ;; (equal lhs nil).
              (let ((lhs  (second conclusion))
                    (rhs  (or (third conclusion) *nil*))
                    (hyps (dumb-negate-lit-lst (butlast clause 1))))
                ;; We only want to apply the hint if we believe lhs
                ;; and rhs are ubddp objects.
                (let ((lhs-okp
                       (term-is-bdd lhs hyps clause hist pspv world ctx state)))
                  (if (not lhs-okp)
                      nil
                    (let ((rhs-okp
                           (term-is-bdd rhs hyps clause hist pspv world ctx state)))
                      (if (not rhs-okp)
                          nil
                        ;; We think LHS and RHS are ubddp's.  Go ahead
                        ;; and give the hint.
                        (let ((hint `(:use (:functional-instance
                                            equal-by-eval-bdds
                                            (bdd-hyps (lambda () (and ,@hyps)))
                                            (bdd-lhs  (lambda () ,lhs))
                                            (bdd-rhs  (lambda () ,rhs))))))
                          (prog2$
                           ;; And tell the user what's happening.
                           (cw "~|~%We now appeal to ~s3 in an ~
                                attempt to show that ~x0 and ~x1 ~
                                are equal because all of their ~
                                evaluations under ~s2 are the ~
                                same.  (You can disable ~s3 to ~
                                avoid this.  See :doc ~s3 for more ~
                                details.)~|~%"
                               (untranslate lhs nil world)
                               (untranslate rhs nil world)
                               'eval-bdd
                               'equal-by-eval-bdds)
                           hint)))))))))))))

  (defmacro equal-by-eval-bdds-hint ()
    `(equal-by-eval-bdds-hint-fn id clause hist pspv ctx
                                 stable-under-simplificationp world state))

  (add-default-hints!
   '((equal-by-eval-bdds-hint))))



(defsection equal-by-eval-bdds-hint-heavy
  :parents (equal-by-eval-bdds)
  :short "Experimental \"heavyweight\" hint."

  :long "<p>Sometimes it is difficult to make use of equalities between BDDs
when carrying out the pick-a-point proof.  QS-SUBSET-MODE is one way to
approach this.  And the HEAVY hint below is another.  The idea is to replace
other equalities between BDDs with what they mean in terms of the
arbitrary-values which have just been picked.</p>

<p>BOZO this was a precursor to the defwitness stuff, right?  Should we port
this to use defwitness, etc.?</p>"

  (defun lit-find-equality (lit)
    (case-match lit
      (('not ('ubddp . &) . &)
       (mv nil nil nil))
      (('ubddp . &)
       (mv nil nil nil))
      (('not ('equal a b . &) . &)
       (mv 'ineq a b))
      (('not a . &)
       (mv 'eq a *nil*))
      (('equal a b . &)
       (mv 'eq a b))
      (& (mv 'ineq lit *nil*))))

  (defun collect-ubddp-eq-and-ineqs (clause whole hyps hist pspv ctx world state)
    (declare (xargs :mode :program :stobjs state))
    (if (atom clause)
        (mv nil nil nil state)
      (mv-let (eqs ineqs remhyps state)
        (collect-ubddp-eq-and-ineqs (cdr clause) whole hyps hist pspv ctx world
                                    state)
        (let ((conclusion (car clause)))
          (mv-let (sense lhs rhs)
            (lit-find-equality conclusion)
            (let ((lhs-okp
                   (term-is-bdd lhs hyps whole hist pspv world ctx state)))
              (if (not lhs-okp)
                  (mv eqs ineqs (cons (dumb-negate-lit conclusion) remhyps) state)
                (let ((rhs-okp
                       (term-is-bdd rhs hyps whole hist pspv world ctx state)))
                 (if (not rhs-okp)
                     (mv eqs ineqs (cons (dumb-negate-lit conclusion) remhyps) state)
                   (case sense
                     (eq    (mv (cons (cons lhs rhs) eqs) ineqs
                                (cons (dumb-negate-lit conclusion) remhyps)
                                state))
                     (ineq  (mv eqs (cons (cons lhs rhs) ineqs) remhyps state))
                     (t     (mv eqs ineqs
                                (cons (dumb-negate-lit conclusion) remhyps)
                                state))))))))))))


  (defun collect-eq-hyps (eq-hyps acc)
    (declare (xargs :mode :program))
    (if (atom eq-hyps)
        acc
      (collect-eq-hyps
       (cdr eq-hyps)
       (cons `(equal (eval-bdd ,(caar eq-hyps) arbitrary-values)
                     (eval-bdd ,(cdar eq-hyps) arbitrary-values))
             acc))))

  (defun collect-hints (eqs hyps)
    (declare (xargs :mode :program))
    (if (atom eqs)
        nil
      (cons `(:use (:functional-instance equal-by-eval-bdds
                                         (bdd-hyps (lambda () (and . ,hyps)))
                                         (bdd-lhs  (lambda () ,(caar eqs)))
                                         (bdd-rhs  (lambda () ,(cdar eqs)))))
            (collect-hints (cdr eqs) hyps))))

  (defun equal-by-eval-bdds-hint-heavy-fn (id clause hist pspv ctx stable world state)
    (declare (xargs :mode :program :stobjs state)
             (ignorable id))
    (if (not stable)
        ;; Don't suggest anything until the goal is stable.  This
        ;; gives other rules a chance to fire.
        (value nil)
      (let* ((rcnst (access prove-spec-var pspv :rewrite-constant))
             (ens   (access rewrite-constant rcnst :current-enabled-structure)))
        (if (not (enabled-numep (fnume '(:rewrite equal-by-eval-bdds) world) ens))
            ;; Don't suggest anything if equal-by-eval-bdds is
            ;; disabled.  This gives the user an easy way to turn off
            ;; the strategy.
            (value nil)
          (let ((hyps (dumb-negate-lit-lst clause)))
            (mv-let (eqs ineqs new-hyps state)
              (collect-ubddp-eq-and-ineqs clause clause hyps
                                          hist pspv ctx world state)
              (if (not eqs)
                  (value nil)
                (let* ((new-hyps (collect-eq-hyps ineqs new-hyps))
                       (hints (collect-hints eqs new-hyps)))
                  (prog2$ nil ;; (cw "hyps: ~x0~%hints: ~x1~%" hyps hints)
                          (value (list :or hints)))))))))))

  (defmacro equal-by-eval-bdds-hint-heavy ()
    `(equal-by-eval-bdds-hint-heavy-fn
      id clause hist pspv ctx stable-under-simplificationp world state))


  (defun equal-by-eval-bdds-inst-fn (lhs rhs concl add-hyps
                                         instantiate-hyps clause hist pspv ctx
                                         world state)
    (declare (xargs :mode :program :stobjs state))
    (let ((clhyps (dumb-negate-lit-lst clause)))
      (mv-let (cleqs clineqs cl-new-hyps state)
        (collect-ubddp-eq-and-ineqs
         clause clause clhyps hist pspv ctx world state)
        (mv-let (lhs rhs state)
          (cond ((and lhs rhs)
                 (mv (car lhs) (car rhs) state))
                (concl
                 (er-let* ((concl (translate (car concl) t t t
                                             'equal-by-eval-bdds-inst world state)))
                   (mv-let (sense lhs rhs)
                     (lit-find-equality (car concl))
                     (declare (ignore sense))
                     (mv lhs rhs state))))
                (t (mv (caar (last cleqs)) (cdar (last cleqs)) state)))
          (let* ((hyps
                  (if (and instantiate-hyps (car instantiate-hyps))
                      (collect-eq-hyps clineqs cl-new-hyps)
                    clhyps))
                 (hyps
                  (if add-hyps
                      (append (car add-hyps) hyps)
                    hyps)))
            (let ((res `(:use (:functional-instance
                           equal-by-eval-bdds
                           (bdd-hyps (lambda () (and . ,hyps)))
                           (bdd-lhs  (lambda () ,lhs))
                           (bdd-rhs  (lambda () ,rhs))))))
              (prog2$ (cw "res: ~x0~%" res)
                      (value res))))))))

  (defmacro equal-by-eval-bdds-inst (&key (lhs 'nil lhsp)
                                          (rhs 'nil rhsp)
                                          (concl 'nil conclp)
                                          (add-hyps 'nil add-hypsp)
                                          (instantiate-hyps 'nil instantiate-hypsp))
    `(equal-by-eval-bdds-inst-fn ,(and lhsp `(list ,lhs))
                                 ,(and rhsp `(list ,rhs))
                                 ,(and conclp `(list ,concl))
                                 ,(and add-hypsp `(list ,add-hyps))
                                 ,(and instantiate-hypsp `(list ,instantiate-hyps))
                                 clause hist pspv ctx world state)))


(defsection q-not
  :extension q-not

  (add-bdd-fn q-not)

  (local (in-theory (enable q-not)))

  (defthm consp-of-q-not
    (equal (consp (q-not x))
           (consp x))
    :hints(("Goal" :in-theory (enable q-not))))

  (defthm equal-t-and-q-not
    (equal (equal t (q-not x))
           (not x)))

  (defthm equal-nil-and-q-not
    (equal (equal nil (q-not x))
           (and (atom x)
                (if x t nil))))

  (defthm q-not-under-iff
    (iff (q-not x)
         (if (consp x)
             t
           (if x nil t))))

  (defthm ubddp-of-q-not
    (implies (force (ubddp x))
             (equal (ubddp (q-not x))
                    t))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-q-not
    (equal (eval-bdd (q-not x) values)
           (not (eval-bdd x values)))
    :hints(("Goal" :in-theory (enable eval-bdd)))))



(defsection q-ite
  :extension q-ite

  (add-bdd-fn q-ite-fn)
  (add-macro-alias q-ite q-ite-fn)

  (local (in-theory (disable (:type-prescription q-ite-fn)
                             equal-of-booleans-rewrite
                             eval-bdd-when-not-consp
                             eval-bdd-when-non-consp-values)))

  (local (defun q-ite-induct (x y z)
           (declare (ignorable y z))
           (cond ((null x) nil)
                 ((atom x) nil)
                 (t (let ((y (if (equal x y) t y))
                          (z (if (equal x z) nil z)))
                      (list (q-ite-induct (car x) (qcar y) (qcar z))
                            (q-ite-induct (cdr x) (qcdr y) (qcdr z))))))))

  (defthm ubddp-of-q-ite
    (implies (and (force (ubddp x))
                  (force (ubddp y))
                  (force (ubddp z)))
             (equal (ubddp (q-ite x y z))
                    t))
    :hints(("Goal"
            :in-theory (e/d (ubddp) (default-car default-cdr))
            :induct (q-ite-induct x y z)
            :expand ((:free (y z) (q-ite-fn x y z))
                     (:free (y z) (q-ite-fn nil y z))
                     (:free (y z) (q-ite-fn t y z))))))

  (local (defun q-ite-induct-vals (x y z vals)
           (declare (ignorable y z))
           (cond ((null x) nil)
                 ((atom x) nil)
                 (t (let ((y (if (equal x y) t y))
                          (z (if (equal x z) nil z)))
                      (cond ((car vals)
                             (q-ite-induct-vals (car x) (qcar y) (qcar z) (cdr vals)))
                            (t
                             (q-ite-induct-vals (cdr x) (qcdr y) (qcdr z) (cdr vals)))))))))

  (with-output
   :off prove
   (defthm eval-bdd-of-q-ite
     (equal (eval-bdd (q-ite x y z) values)
            (if (eval-bdd x values)
                (eval-bdd y values)
              (eval-bdd z values)))
     :hints(("Goal"
             :in-theory (enable eval-bdd)
             :induct (q-ite-induct-vals x y z values)
             :expand ((:free (y z) (q-ite-fn x y z))
                      (:free (y z) (q-ite-fn nil y z))
                      (:free (y z) (q-ite-fn t y z))))))))



(defsection canonicalize-q-not
  :extension q-not

  (defthm canonicalize-q-not
    (implies (force (ubddp x))
             (equal (q-not x)
                    (q-ite x nil t)))
    :rule-classes :definition))


(defsection canonicalize-to-q-ite
  :parents (ubdds q-ite)
  :short "Reasoning strategy: rewrite all BDD-building functions into calls of
  @(see q-ite)."

  :long "<p>This isn't an especially good reasoning strategy, and we generally
prefer @(see equal-by-eval-bdds) instead.</p>

<p>@('canonicalize-to-q-ite') is a <see topic='@(url rulesets)'>ruleset</see>
that holds theorems for rewriting other BDD-constructing functions into
@('q-ite') form.</p>"

  (def-ruleset canonicalize-to-q-ite '(canonicalize-q-not)))




(defsection q-ite-reductions
  :parents (q-ite)
  :short "Basic rewriting of @(see q-ite) expressions."
  :long "<p>When using the @(see canonicalize-to-q-ite) strategy, you generally
end up with big nests of @(see q-ite) calls.  Afterward, these basic sorts of
reductions can be useful.</p>"

  ;; !!! I think we should maybe be able to get some more of these
  ;; hypothesis free if we change q-ite-fn around a bit so that it
  ;; coerces atoms into booleans.  Would performance be okay?

  (defthm |(q-ite x (q-ite y nil t) z)|
    (implies (and (syntaxp (not (equal z ''t))) ;; Prevents loops (see next rule)
                  (force (ubddp x))
                  (force (ubddp y))
                  (force (ubddp z)))
             (equal (q-ite x (q-ite y nil t) z)
                    (q-ite y
                           (q-ite x nil z)
                           (q-ite x t z)))))

  (defthm |(q-ite x (q-ite y nil t) t)|
    ;; ACL2's loop-stopper works.
    (implies (and (force (ubddp x))
                  (force (ubddp y))
                  (force (ubddp z)))
             (equal (q-ite x (q-ite y nil t) t)
                    (q-ite y (q-ite x nil t) t))))

  (defthm |(q-ite (q-ite a b c) x y)|
    (implies (and (force (ubddp a))
                  (force (ubddp b))
                  (force (ubddp c))
                  (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-ite (q-ite a b c) x y)
                    (q-ite a
                           (q-ite b x y)
                           (q-ite c x y)))))

  (defthm |(q-ite x y y)|
    (equal (q-ite x y y)
           y)
    :hints(("Goal" :in-theory (enable q-ite))))

  (defthm |(q-ite x x y)|
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-ite x x y)
                    (q-ite x t y))))

  (defthm |(q-ite x y x)|
    (equal (q-ite x y x)
           (q-ite x y nil))
    :hints(("Goal" :in-theory (e/d (q-ite) ((force))))))

  (defthm |(q-ite x t nil)|
    (implies (force (ubddp x))
             (equal (q-ite x t nil)
                    x)))

  (defthm |(q-ite non-nil y z)|
    (implies (and (atom x)
                  x)
             (equal (q-ite x y z)
                    y))
    :hints(("Goal" :in-theory (enable q-ite))))

  (defthm |(q-ite t x y)|
    (equal (q-ite t x y)
           x)
  :hints(("Goal" :in-theory (enable q-ite))))

  (defthm |(q-ite nil x y)|
    (equal (q-ite nil x y)
           y)
    :hints(("Goal" :in-theory (enable q-ite)))))



