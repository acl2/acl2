; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "std/util/define" :dir :system)


(define unequiv (x y)
  :enabled t
  :ignore-ok t
  :irrelevant-formals-ok t
  :parents (fgl-testbenches)
  :short "The universal equivalence relation, true of every pair of objects.  Used
          in FGL to program testbenches."
  :long "

<p>@('Unequiv') takes two arguments and always returns @('T').  It is an
equivalence relation; in fact, it is the equivalence relation for which every
other equivalence relation is a refinement.</p>

<p>In FGL, if the rewriter enters an @('unequiv') equivalence context, there
are several tools that can be used that can't be used under other equivalence
contexts.  These tools include extralogical forms such as @('syntax-interp'),
@('fgl-interp-obj'), and @('assume').  The rewriter can also apply rules whose
equivalence relation is @('unequiv'), meaning the LHS and RHS don't actually
need to be related at all.  When the rewriter is under an @('unequiv') context
it essentially means that whatever it computes there can't be relevant to the
truth or falsity of the theorem under consideration, so it can do whatever the
user asks it to do.</p>
"
  t ;; Always true!
  ///
  (defequiv unequiv))

(define binder (val)
  :parents (fgl-rewrite-rules)
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  :short "Form that can bind a free variable to the result of some (possibly
nondeterministic) computation."
  :long "<p>Logically, @('(binder val)') just returns @('val').  However, in
FGL, the intended use is to bind a free variable in a rewrite rule to the
result of some computation with some particular properties.  The @('val')
argument must be a function--say @('bindingfn')--whose first argument is a
variable @('var') and which has either a binder rule of the following form:
@({
 (implies (and ... hyps ...
               (equiv2 var (binding-impl-term ...)))
          (equiv1 (bindingfn var arg1 ... argn) var))
 })
or else a binder metafunction associated with it.  In the first case (and assuming we
are in an @('equiv1') equiv context),
@({
 (binder (bindingfn var val1 ... valn))
 })
results in @('var') being bound to the result of symbolically interpreting
@('(binding-impl-term ...)') under the substitution binding @('argi') to
@('vali') and in the @('equiv2') context.  In the second case, the binder
metafunction is applied to the symbolic values @('val1 ... valn'), resulting in
a term, bindings, and equivalence context; @('var') is bound to the result of
symbolically interpreting the term under the bindings in the equivalence
context.</p>

<p>An example application is to check whether the symbolic value of some term
is syntactically an integer.  We define @('(check-integerp var x)') to be
@('(and (integerp x) var)') and associate this with a binding metafunction that
returns T if @('x') is syntactically an integer.  Another application is to
perform a SAT check and return the result (@(':unsat'), @(':sat'), or
@(':failed')).</p>" val)

(define bind-var (ans form)
  :parents (fgl-rewrite-rules)
  :short "Form that can bind a free variable to the result of an arbitrary computation."
  :long "<p>Logically, @('(bind-var var form)') just returns @('var').
However, in FGL, the intended use is to bind a free variable in a rewrite rule
to the result of some arbitrary computation.  The @('form') argument is
rewritten under an @('unequiv') congruence so it can do extralogical things
like examining the interpreter state and term syntax. The @('var') argument
must be a variable that hasn't yet been bound during the application of the
current rewrite rule.</p>"
  
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  ans
  ///
  (defcong unequiv equal (bind-var ans form) 2)
  
  (defthmd bind-var-binder-rule
    (implies (equal ans form)
             (equal (bind-var ans form)
                    ans))))

(defxdoc syntax-interp
  :parents (fgl-rewrite-rules)
  :short "Interpret a form on the syntactic representations of variables."
  :long "<p>Logically, this always returns NIL.  In FGL, this can be used when
under an @('unequiv') congruence to examine the syntactic representation of
certain values and also to access and update the ACL2 state and FGL interpreter
state.</p>")

(define syntax-interp-fn (form untrans-form)
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  nil)

(define assume (test val)
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  :parents (fgl-rewrite-rules)
  :short "FGL testbench function to assume some condition while interpreting a term."
  :long "<p>Logically, @('(assume test val)') just returns NIL.  When it is
encountered by the FGL interpreter under an @('unequiv') congruence, it
causes the interpreter to assume that @('test') is true while interpreting
@('val'), returning the symbolic result from @('val').</p>
"
  nil)

(define narrow-equiv (equiv val)
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  :parents (fgl-rewrite-rules)
  :short "FGL testbench function to interpret a term under a narrower (stricter) equivalence context."
  :long "<p>Logically, @('(narrow-equiv equiv val)') just returns @('val').
When it is encountered by the FGL interpreter and @('equiv') evaluates to an
@('equiv-contexts-p') object that is a more granular equivalence than the
current equivalence context, then it interprets @('val') under an @('equiv')
congruence.  The most relevant @('equiv-contexts') objects:</p>

<ul>
<li>@('nil') means rewrite under @('equal'), that is, an object is only equivalent to itself</li>
<li>@('(iff)') means rewrite under @('iff')</li>
<li>@('(unequiv)') means rewrite under @('unequiv'), that is, all objects are equivalent.</li>
</ul>
"
  val)


(define fgl-time-fn (time-val x)
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  :parents (fgl-rewrite-rules)
  x)

(defmacro fgl-time (x &key
                      (mintime '0 mintime-p)
                      (real-mintime 'nil real-mintime-p)
                      run-mintime minalloc msg args)

; Warning: Keep this in sync with the generation of time$ calls by untranslate1.

  (declare (xargs :guard t))
  (cond
   ((and real-mintime-p mintime-p)
    (er hard 'fgl-time
        "It is illegal for a ~x0 form to specify both :real-mintime and ~
         :mintime."
        'time$))
   (t
    (let ((real-mintime (or real-mintime mintime)))
      `(fgl-time-fn (list ,real-mintime ,run-mintime ,minalloc ,msg ,args)
                    ,x)))))

(defxdoc fgl-time
  :parents (fgl-rewrite-rules)
  :short "FGL alternative to time$ that does not get elided by rewrite rule storage."
  :long "<p>The FGL interpreter recognizes time$ forms and prints timing
information for the symbolic interpretation of the subterm.  However, since FGL
is programmed mainly with rewrite rules and time$ forms are usually stripped
out of stored rewrite rules, we provide this alternative that has the same
effect in FGL symbolic interpretation.  It has no effect in actual execution,
so it should just be used in rewrite rules, not in executable function
definitions.</p>")

(define fgl-prog2 (x y)
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  :parents (fgl-rewrite-rules)
  :short "In the FGL interpreter, run the first form for side effects and
return the result from the second form."
  :long "<p>Logically, returns the second argument.  In FGL, the first argument
is interpreted under the @('unequiv') equivalence context, then the second is
interpreted normally and returned.</p>"
  y
  ///
  (defcong unequiv equal (fgl-prog2 x y) 1))

(defmacro fgl-progn (&rest args)
  (xxxjoin 'fgl-prog2 args))

(define fgl-interp-obj (term)
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  :parents (fgl-rewrite-rules)
  :short "FGL testbench function to interpret a term that is the result of evaluating some form."
  :long "<p>Logically, @('(fgl-interp-obj term)') just returns NIL.  When it is
encountered by the FGL interpreter under an @('unequiv') congruence, it
recursively interprets the object that @('term') evaluates to.  That is, it
first interprets @('term'), then if this results in a constant object whose
value is a pseudo-term, it interprets that and returns its result.</p>
"
  nil)

(defmacro syntax-interp (form)
  `(syntax-interp-fn ,form ',form))

(defxdoc syntax-bind
  :parents (fgl-rewrite-rules)
  :short "Form that can bind a free variable to a value computed from examining
the syntax of other bound variables in the RHS of an FGL rewrite rule."
  :long "<p>The basic syntax of a syntax-bind form is:</p>

@({
 (syntax-bind fresh-variable binding-form)
 })

<p>where fresh-variable must be a variable not previously bound and
binding-form is a term that may mention previously bound variables.  See @(see
fgl-rewrite-rules) for further discussion.</p>

<p>The above syntax-bind form is actually a macro which expands to:</p>
@({
 (bind-var fresh-variable (syntax-interp binding-form))
 })

")

;; (defun syntax-bind-fn (form untrans-form dummy-var)
;;   (declare (ignorable form untrans-form)
;;            (xargs :guard t))
;;   dummy-var)

;; note: probably need to put this somewhere else
(defmacro syntax-bind (dummy-var form)
  `(bind-var ,dummy-var (syntax-interp ,form)))

(defxdoc abort-rewrite
  :parents (fgl-rewrite-rules)
  :short "Form that aborts the application of an FGL rewrite rule when encountered
          while processing the RHS of the rule."
  :long "<p>The basic syntax of an abort-rewrite form is:</p>

@({
 (abort-rewrite value-term)
 })

<p>where value-term can be anything.  Usually value-term is selected so that
the rewrite rule is easy to prove -- e.g., it may just be the LHS of the
rule.</p>")


;; For lack of a better place to put this.
(defun abort-rewrite (x)
  x)

(define if! (x y z)
  :parents (fgl-rewrite-rules)
  :short "Function implementing IF that under FGL interpretation makes a
@(':g-ite') object instead of doing the usual merging process."
  (if x y z))

;; (defevaluator synbind-ev synbind-ev-list ((syntax-bind-fn x y z)) :namedp t)

;; (local (acl2::def-ev-pseudo-term-fty-support synbind-ev synbind-ev-list))

;; (local (defthm assoc-when-key
;;          (implies k
;;                   (equal (assoc k a)
;;                          (hons-assoc-equal k a)))))

;; (define match-syntax-bind ((x pseudo-termp))
;;   :returns (mv (dummy-var symbolp
;;                           ;; note: not pseudo-var-p because we indicate no match by returning nil
;;                           :rule-classes :type-prescription)
;;                (form pseudo-termp))
;;   (b* (((mv ok alist)
;;         (cmr::pseudo-term-unify '(syntax-bind-fn trans-form untrans-form dummy-var)
;;                            x nil))
;;        ((unless ok) (mv nil nil))
;;        (untrans-form (cdr (assoc 'untrans-form alist)))
;;        (trans-form (cdr (assoc 'trans-form alist)))
;;        (dummy-var (cdr (assoc 'dummy-var alist)))
;;        ((unless (And (pseudo-term-case dummy-var :var)
;;                      (pseudo-term-case untrans-form :quote)))
;;         (mv nil nil)))
;;     (mv (acl2::pseudo-term-var->name dummy-var) trans-form))
;;   ///
;;   (std::defretd eval-when-<fn>
;;     (implies dummy-var
;;              (equal (synbind-ev x a)
;;                     (cdr (hons-assoc-equal dummy-var a))))
;;     :hints(("Goal" :expand ((:free (pat x alist) (cmr::pseudo-term-unify pat x alist))
;;                             (:free (pat x alist) (cmr::pseudo-term-list-unify pat x alist))))))

;;   (fty::deffixequiv match-syntax-bind)

;;   (local
;;    (make-event
;;     (b* (((mv err val state) (acl2::translate '(syntax-bind foo (and x y z)) t t nil 'match-syntax-bind-works
;;                                         (w state) state))
;;          ((when err) (mv err val state)))
;;       (value `(defthm match-syntax-bind-works
;;                 (b* (((mv dummy-var form) (match-syntax-bind ',val)))
;;                   (and (equal dummy-var 'foo)
;;                        (equal form '(if x (if y z 'nil) 'nil))))))))))

