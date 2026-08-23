; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; top.lisp
;;;
;;;
;;; This book collects all the other books together in one place,
;;; establishes a couple of useful theory collections, and sets up
;;; a default starting point.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc moore-mods-to-arithmetic-5
  :parents (arithmetic-5)
  :short "motivation of Moore's mods to Krug's amazing arithmetic-5"
  :long "
  <p>Arithmetic-5 sometimes gets into ``loops'' (where certain terms, under
  certain hypotheses, rewrite to themselves through a sequence of 2 or more
  rules).  This can produce an error like this:</p>

  @({
  HARD ACL2 ERROR [Call depth] in REWRITE: The call depth limit of 1000 has
  been exceeded in the ACL2 rewriter. ...
  })

  <p>In 2026, J Moore modified some of the rules in @('arithmetic-5') and added
  a few new rules with the sole objective of preventing some such loops.  The
  loop-stopping modifications to @('arithmetic-5') restrict certain lemmas from
  firing in circumstances that could cause loops.  But because
  @('arithmetic-5') had been in use for 17 years before the first of these
  changes were made -- and because it is possible that the unrestricted use of
  Robert's rules might sometimes fire without causing a loop -- it was decided
  to give the @('arithmetic-5') user the option of using the original rules or
  the new (modified) rules.</p>

  <p>Aside: Moore attached his name to these modification because they're a
  hack glued onto a magnificent piece of engineering by Robert Krug.  The
  modifications weaken @('arithmetic-5').  Furthermore, Moore only stopped the
  loops he encountered; more may be lurking.  Robert should not be blamed for
  these inadequacies.</p>

  <p>The modified and newly added rules are active only if the
  executable-counterpart of the dummy function @('use-new-arith-5-rules') is
  enabled.  The rune in question can be written (:e use-new-arith-5-rules).  As
  of August, 2026, that rune is DISABLED by default and so @('arithmetic-5')
  behaves as it always has, by default.</p>

  <p>To allow the modified and newly added rules to fire (in addition to the
  unmodified versions of Robert's rules), enable that rune, as with</p>

  @({
  (in-theory (enable (:e use-new-arith-5-rules)))
  })

  <p>You may wish to limit the new rules only to subgoals on which the original
  rules looped in an earlier proof attempt.  This can be done with a
  subgoal-specific hint to the prover, e.g.,</p>

  @({
  :hints ((\"Subgoal *1/2.3\"
           :in-theory (enable (:e use-new-arith-5-rules))))
  })

  <p>Below is a script that illustrates two rewrite loops under the original
  @('arithmetic-5') rules.</p>

  @({
  ; --- begin script ---

  (include-book \"arithmetic-5/top\" :dir :system)

  ; The following causes a hard error under the original rules:

  (thm
   (implies (natp n)
            (equal (/ (expt 3 n) (expt 2 n))
                   (expt 3/2 n))))

  ; But under the new rules the theorem is proved:

  (thm
   (implies (natp n)
            (equal (/ (expt 3 n) (expt 2 n))
                   (expt 3/2 n)))
   :hints ((\"Goal\" :in-theory (enable (:e use-new-arith-5-rules)))))

  ; If we enable non-linear reasoning with

  (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                                hist pspv)))

  ; this causes a hard error under the original rules:

  (thm (implies (natp n)
                (<= (* (expt 3 n) (expt 10 (- n))) 1)))

  ; But succeeds under the new rules:

  (thm (implies (natp n)
                (<= (* (expt 3 n) (expt 10 (- n))) 1))
       :hints ((\"Goal\" :in-theory (enable (:e use-new-arith-5-rules)))))

  ; --- end script ---
  })

  <p>The ``cause'' of many such loops come from a very clever trick carried out
  by Robert's original rules: heuristically select a term, @('x'), and multiply
  other terms by @('x') in order to cancel out certain subterms.  An example
  such rule is</p>

  @({
  (defthm simplify-products-gather-exponents-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (syntaxp (in-term-order-* lhs mfc state))
                  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free (find-matching-factors-gather-exponents-wrapper
                              lhs rhs mfc state)
                             (x))
                  (syntaxp (not (equal x ''1)))
                  (syntaxp (not (equal x ''-1)))
                  (case-split (acl2-numberp x))
                  (case-split (not (equal x 0))))
             (equal (equal lhs rhs)
                    (equal (* x lhs) (* x rhs)))))
  })

  <p>The @(tsee bind-free) hypothesis attempts to find a suitable @('x') by
  inspection of @('lhs') and @('rhs'), which are generally expected to be nests
  of products.  Note that the conclusion rewrites @('(equal lhs rhs)') to the
  larger @('(equal (* x lhs) (* x rhs))').  However, other rules in
  @('arithmetic-5') are designed to ``bubble @('x') down'' through the
  successive factors of @('lhs') and @('rhs'), find the subterms that the
  @('bind-free') hypothesis used to justify the choice of @('x'), and perform a
  cancellation to produce a smaller equation.</p>

  <p>Note: The ``examples'' sketched below are meant to suggest how some loops
  are formed.  Each example corresponds to behavior Moore has witnessed but
  failed to record the actual terms involved.  Thus, these ``examples'' are
  just suggestive of more complicated loops.</p>

  <p>For example, suppose @('lhs') is @('(* a (/ z b) (foo c))') and the
  @('bind-free') hypothesis chooses to multiply by @('b').  The bubble down
  process is designed to consider the factors @('a'), @('(/ z b)'), and @('(foo
  c)'), in that order, and find the one used by the bind-free hypothesis to
  justify the choice of @('b').  If @('b') bubbles down to @('(/ z b)') then
  all is well, <i>provided</i> there's a rule like @('(* b (/ z b))') @('=')
  @('z') (under appropriate conditions).  But if such a cancellation rule is
  missing the equation gets bigger.  Another possibility is that some earlier
  subterm, e.g., @('a') in this example, somehow absorbs @('b') before bubbling
  gets to the intended target.  Indeed, one loop witnessed in the original
  system repeatedly multiplied by @('3'), intending to cancel @('(/ z 3)'), but
  it was ``intercepted'' by a subterm like @('(expt 3 n)') and produced the new
  subterm @('(expt 3 (+ n 1))').  Then the rule fired again and, since @('(/ z
  3)') was still in the formula, chose to multiply by @('3') again, and
  produced the new subterm (expt 3 (+ n 2)), etc.  Sometimes loops created ever
  larger numbers, e.g., @('3'), @('9'), @('27'), @('81'), ..., without using
  any rules besides ground evaluation.</p>

  <p>Below are all the rules in @('arithmetic-5') that find a factor and
  transform a term by multiplying subterms by that factor.</p>

  @({
  simplify-products-gather-exponents-equal            *
  simplify-products-gather-exponents-<                *
  simplify-products-scatter-exponents-equal
  simplify-products-scatter-exponents-<
  prefer-positive-exponents-scatter-exponents-equal
  prefer-positive-exponents-scatter-exponents-<
  prefer-positive-exponents-scatter-exponents-<-2
  normalize-factors-gather-exponents
  normalize-factors-scatter-exponents                 *
  arith-normalize-factors-scatter-exponents
  reduce-rationalp-*
  |(floor (* x (/ y)) z) not rewriting-goal-literal|
  |(floor (* x (/ y)) z) rewriting-goal-literal|
  |(floor x (* y (/ z))) not rewriting-goal-literal|
  |(floor x (* y (/ z))) rewriting-goal-literal|
  |(mod (* x (/ y)) z) not rewriting-goal-literal|
  |(mod (* x (/ y)) z) rewriting-goal-literal|
  |(mod x (* y (/ z))) not rewriting-goal-literal|
  |(mod x (* y (/ z))) rewriting-goal-literal|
  floor-cancel-*-not-rewriting-goal-literal           *
  floor-cancel-*-rewriting-goal-literal               *
  mod-cancel-*-not-rewriting-goal-literal             *
  mod-cancel-*-rewriting-goal-literal                 *
  floor-cancel-*-const
  mod-cancel-*-const
  })

  <p>All of these appear to raise the possibility of the sort of loops
  described above, but only the ones marked with `@('*')' above have been
  modified because Moore never encountered loops involving the others.</p>

  <p>You can find all the modification to @('arithmetic-5') books made by Moore
  by recursively searching through the @('arithmetic-5') directory looking for
  the string `@('; Moore Modification')'.</p>

  <p>At the time that these modifications were first pushed to GitHub (in
  August, 2026), it was possible to process the standard
  @('regression-everything') with @('(:e use-new-arith-5-rules)') enabled by
  default in @('arithmetic-5/top').  But, of course, the regression did not
  contain any books that caused rewrite stack overflows.  So this data point
  does improve our confidence in the modifications' ability to avoid loops, but
  it does indicate that the modifications don't weaken @('arithmetic-5/top')
  too much.  Note however that if you want to try to do a full regression with
  a modified @('arithmetic-5/top') in which the rune is enabled, you must do so
  the first time with @('ACL2_USELESS_RUNES=write') since the modifications
  require the participation of some rules not used by the original book.  See
  @(tsee useless-runes).</p>

  <p>If you find loops in @('arithmetic-5/top') while @('(:e
  use-new-arith-5-rules)') is enabled, please try to make a simple script that
  reproduces the loop and send it to Moore.</p>")

(defxdoc arithmetic-5-overflow-advice
  :parents (arithmetic-5)
  :short "advice on avoiding stack overflow"
  :long "<p>If you get a @('HARD ACL2 ERROR [Call depth] in REWRITE:') while
  using @('arithmetic-5') and you see that the rune @('(:E
  ACL2::USE-NEW-ARITH-5-RULES)') is disabled, you might try enabling it and
  re-trying the proof.  See @(see moore-mods-to-arithmetic-5) for
  background.</p>

  <p>The rune in question denotes the @(see executable-counterpart) of the
  function @('use-new-arith-5-rules').  That function's only purpose is to
  provide this rune.  The enabled status of the rune controls whether certain
  modifications to the original @('arithmetic-5') rules are active.</p>

  <p>When the rune is <i>dis</i>abled, @('arithmetic-5/top') should behave
  exactly as it did before the rune was added.  The rune is disabled by default
  when @('arithmetic-5/top') is included.</p>

  <p>When the rune is <i>en</i>abled, @('arithmetic-5/top') avoids some loops
  by restricting about half-a-dozen of the book's original rules, leaving all
  the other rules unchanged, and adding a few new rules.</p>

  <p><b>Note</b>: The above comments are thought to be accurate in the default
  configuration of @('arithmetic-5/top') and in isolation from other books and
  user-supplied arithmetic rules.  For example, the modifications have not been
  tested thoroughly if @('(scatter-exponents)') has been executed (as opposed
  to the default setting of @('(gather-exponents)'), or when
  @('(do-not-prefer-positive-addends)') has been executed (as opposed to the
  default @('(prefer-positive-addends)')) or when normally-enabled rules in the
  original @('arithmetic-5/top') are selectively disabled by the user.</p>

  <p>You can determine whether @('(:e use-new-arith-5-rules)') is disabled at
  the top-level by evaluating the following form at the top-level of the ACL2
  read-eval-print loop:</p>

  @({
  (disabledp '(:e use-new-arith-5-rules))
  })

  <p>You can enable it globally with the event</p>

  @({
  (in-theory (enable (:e use-new-arith-5-rules)))
  })

  <p>Note that what really matters is the enabled status of the rune while the
  rewriter is working on the subgoal that caused the stack overflow.  So, even
  if the rune is enabled at the top-level &mdash; suggesting you are trying to
  avoid loops &mdash; you might also check that your hints haven't disabled the
  rune for that subgoal.</p>

  <p>Of course, the rewriter behaves differently when the rune is enabled: some
  loops are avoided!  But a possible side-effet is that a goal that was proved
  when the rune was disabled fails to be proved when the rune is enabled. This
  is not surprising to us.  But if you still get a stack overflow while @('(:e
  use-new-arith-5-rules)') is enabled &mdash; and you know that your own
  rewrite rules about arithmetic or your adjustments to the default enabled
  status of @('arithmetic-5') rules don't play a part in the overflow &mdash;
  we would like to be able to reproduce it and may be able to improve
  @('arithmetic-5').  Please send the simplest example of the loop that you can
  find to Moore.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "build/ground-zero-theory.certdep" :dir :system)

(deftheory-static arithmetic-5-current-base
  ;; Presumably the same as 'ground-zero
  (current-theory :here))

(deftheory-static arithmetic-5-universal-base
  (universal-theory :here))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This book defines some theories we will use below.
(include-book "lib/basic-ops/top")

(include-book "lib/floor-mod/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory-static arithmetic-5-current-full
  (current-theory :here))

(deftheory-static arithmetic-5-universal-full
  (universal-theory :here))

;;; Now, let us build our theories piece by piece.  This could be done
;;; more efficiently, but slow and simple wins the race.

(deftheory minimal-arithmetic-5-base
  ;; We want ACL2's base here.
  (theory 'arithmetic-5-current-base))

(deftheory default-arithmetic-5-base
  ;; Rules from the base (whether or not enabled at that time) that are enabled
  ;; in the full
  (intersection-theories (theory 'arithmetic-5-universal-base)
			 (theory 'arithmetic-5-current-full)))

(deftheory-static minimal-arithmetic-5
  ;; Using theories defined in lib/basic-ops/top.lisp
  (union-theories
   (set-difference-theories (theory 'arithmetic-5-minimal-end-a)
			    (theory 'arithmetic-5-minimal-start-a))
   (set-difference-theories (theory 'arithmetic-5-minimal-end-b)
			    (theory 'arithmetic-5-minimal-start-b))))

(deftheory default-arithmetic-5
  (set-difference-theories (theory 'arithmetic-5-current-full)
			   (theory 'arithmetic-5-current-base)))

(defmacro intersection-theories-3 (x y z)
  `(intersection-theories ,x
			  (intersection-theories ,y ,z)))

(defmacro union-theories-3 (x y z)
  `(union-theories ,x
		   (union-theories ,y ,z)))

(defmacro set-minimal-arithmetic-5-theory ()
  ;; 1. ground-zero less anything disabled by either arithmetic-5 or the user,
  ;;    i.e., those rules enabled in ground-zero that are enabled both by
  ;;    arithmetic-5 and by the user
  ;; 2. the minimal arithmetic theory
  ;; 3. whatever enabled rules the user has added (i.e. not in arithmetic-5 or
  ;;    ground-zero)
  `(in-theory (union-theories-3
               (intersection-theories-3 (theory 'minimal-arithmetic-5-base)
                                        (theory 'arithmetic-5-current-full)
                                        (current-theory :here))
	       (theory 'minimal-arithmetic-5)
	       (set-difference-theories (current-theory :here)
					(theory 'arithmetic-5-universal-full)))))

(defmacro set-default-arithmetic-5-theory ()
  `(in-theory (union-theories-3
	       (intersection-theories-3 (theory 'default-arithmetic-5-base)
                                        (theory 'arithmetic-5-current-full)
                                        (current-theory :here))
	       (theory 'default-arithmetic-5)
	       (set-difference-theories (current-theory :here)
					(theory 'arithmetic-5-universal-full)))))

(set-call-depth-overflow-advice
 "If the rune (:E ACL2::USE-NEW-ARITH-5-RULES) is disabled, you might try ~
  enabling it and re-trying the proof.  See :DOC arithmetic-5-overflow-advice.")
