; Make-flag -- Introduce induction scheme for mutually recursive functions.
; Copyright (C) 2008-2010 Centaur Technology
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
; Original authors: Sol Swords and Jared Davis
;                   {sswords,jared}@centtech.com

; Matt Kaufmann added the :last-body argument of make-flag, May 2018, but
; replaced it by the more general :body argument in March 2021.  The formal
; parameter last-body in some functions below was deliberately left as is
; during the change from :last-body to :body, just to make that argument easy
; to locate textually.

; Matt Kaufmann modified the syntax for :flag-mapping to be a list of doublets,
; as requested by Alessandro Coglio and Eric Smith; but after considering an
; email from Sol Swords, we also allow dotted pairs for backward compatibility,
; He also modified the syntax for undocumented feature :formals-subst to be a
; list of doublets.

#||  for interactive development, you'll need to ld the package first:

(ld ;; fool dependency scanner
 "flag.acl2")

||#

(in-package "FLAG")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/support" :dir :system)

; Matt K. mod: Needed for #+acl2-devel build.  This could probably be made
; conditional using #+acl2-devel.
#!acl2
(encapsulate
  ()
  (local (include-book "system/termp" :dir :system))
  (verify-termination plist-worldp-with-formals)
  (verify-guards plist-worldp-with-formals)
  (verify-termination arity)
  (verify-guards arity)
  (verify-termination arities-okp)
  (verify-guards arities-okp)
  (verify-termination legal-variable-or-constant-namep)
  (verify-guards legal-variable-or-constant-namep)
  (verify-termination legal-variablep)
  (verify-guards legal-variablep)
  (verify-termination arglistp1)
  (verify-guards arglistp1)
  (verify-termination arglistp)
  (verify-guards arglistp)
  (verify-termination termp)
  (verify-guards termp)
  (verify-termination term-listp)
  (verify-guards term-listp)
  (verify-termination term-list-listp)
  (verify-guards term-list-listp)
  (verify-termination logic-fns-listp)
  (verify-guards logic-fns-listp)
  (verify-termination logic-fns-list-listp)
  (verify-guards logic-fns-list-listp)
  (verify-termination logic-term-listp)
  (verify-guards logic-term-listp)
  (verify-termination logic-term-list-listp)
  (verify-guards logic-term-list-listp))

(defxdoc make-flag
  :parents (mutual-recursion)
  :short "Create a flag-based @(see acl2::induction) scheme for a @(see
mutual-recursion)."

  :long "<p>The @('make-flag') macro lets you quickly introduce:</p>

<ul>

<li>a \"flag function\" that mimics a @(see mutual-recursion), and</li>

<li>a theorem proving that the appropriate invocations of the flag function are
equivalent to the original mutually-recursive functions,</li>

<li>a macro for proving properties by induction according to the flag
function.</li>

</ul>

<p>Generally speaking, writing a corresponding flag function is the first step
toward proving any inductive property about mutually recursive definitions;
more discussion below.</p>

<h3>Using @('make-flag')</h3>

<p>Example:</p>

@({
    (make-flag flag-pseudo-termp               ; flag function name (optional)
               pseudo-termp                    ; any member of the clique
               ;; optional arguments:
               :flag-mapping ((pseudo-termp      term)
                              (pseudo-term-listp list))
               :defthm-macro-name defthm-pseudo-termp
               :flag-var flag
               :body :last                     ; use last body, not original
               :hints ((\"Goal\" ...))         ; for the measure theorem
                                               ; usually not necessary
               )
})

<p>Here @('pseudo-termp') is the name of a function in a mutually recursive
clique.  In this case, the clique has two functions, @('pseudo-termp') and
@('pseudo-term-listp').  The name of the newly generated flag function can be
provided explicitly, or else will be formed by sticking @('flag-') on the front
of the clique member's name.</p>

<p>The other arguments are optional:</p>

<ul>

<li>@(':flag-mapping') specifies short names to identify with each of the
functions of the clique.  By default we just use the function names themselves,
but it's usually nice to pick shorter names since you'll have to mention them
in the theorems you prove.  The argument, if supplied and non-@('nil'), should
be a list that specifies a short name for every function in the clique.  Each
member of that list should be of the form @('(old new)') where (of course)
@('old') and @('new') are symbols, except that for backward compatibility the
form @('(old . new)') is allowed (but deprecated after March, 2021, ultimately
to be eliminated).</li>

<li>@(':defthm-macro-name') lets you name the new macro that will be generated
for proving theorems by inducting with the flag function.  By default it is
named @('defthm-[flag-function-name]'), i.e., for the above example, it would
be called @('defthm-flag-pseudo-termp').</li>

<li>@(':flag-var') specifies the name of the variable to use for the flag.  By
default it is just called @('flag'), and we rarely change it.  To be more
precise, it is @('pkg::flag') where @('pkg') is the package of the new flag
function's name; usually this means you don't have to think about the
package.</li>

<li>@(':ruler-extenders') lets you give a value for the @(see
acl2::ruler-extenders) of the new flag function.</li>

<li>@(':body') is @('nil') by default, specifying that the original definition
is used when extracting the body of each function.  The most recent definition
rule is used if @(':body') is @(':last').  Otherwise @(':body') should be a
list with members of the form @('(fn1 fn2)'), indicating that the definition
associated with a rule named @('fn2'), if there is one, should be used as the
definition for the function symbol, @('fn1').  See the community book
@('books/tools/flag-tests.lisp') for an example of using such a alist for
@(':body'), in particular for the purpose of using definitions installed with
@(tsee acl2::install-not-normalized).</li>

</ul>


<h3>Proving Theorems with @('make-flag')</h3>

<p>To prove an inductive theorem about a mutually-recursive function, you
usually have to effectively prove a single, big, ugly formula that has a
different case about each function in the clique.</p>

<p>Normally, even with the flag function written for you, this would be a
tedious process.  Here is an example of how you might prove by induction that
@('pseudo-termp') and @('pseudo-term-listp') return Booleans:</p>

@({
    ;; ACL2 can prove these are Booleans even without induction due to
    ;; type reasoning, so for illustration we'll turn these off so that
    ;; induction is required:

    (in-theory (disable (:type-prescription pseudo-termp)
                        (:type-prescription pseudo-term-listp)
                        (:executable-counterpart tau-system)))

    ;; Main part of the proof, ugly lemma with cases.  Note that we
    ;; have to use :rule-classes nil here because this isn't a valid
    ;; rewrite rule.

    (local (defthm crux
             (cond ((equal flag 'term)
                    (booleanp (pseudo-termp x)))
                   ((equal flag 'list)
                    (booleanp (pseudo-term-listp lst)))
                   (t
                    t))
             :rule-classes nil
             :hints((\"Goal\" :induct (flag-pseudo-termp flag x lst)))))

    ;; Now we have to re-prove each part of the lemma so that we can use
    ;; it as a proper rule.

    (defthm type-of-pseudo-termp
      (booleanp (pseudo-termp x))
      :rule-classes :type-prescription
      :hints((\"Goal\" :use ((:instance crux (flag 'term))))))

    (defthm type-of-pseudo-term-listp
      (booleanp (pseudo-term-listp lst))
      :rule-classes :type-prescription
      :hints((\"Goal\" :use ((:instance crux (flag 'list))))))
})

<p>Obviously this is tedious and makes you say everything twice.  Since the
steps are so standard, @('make-flag') automatically gives you a macro to
automate the process.  Here's the same proof, done with the new macro:</p>

@({
    (defthm-pseudo-termp
      (defthm type-of-pseudo-termp
        (booleanp (pseudo-termp x))
        :rule-classes :type-prescription
        :flag term)
      (defthm type-of-pseudo-term-listp
        (booleanp (pseudo-term-listp lst))
        :rule-classes :type-prescription
        :flag list))
})

<p>It's worth understanding some of the details of what's going on here.</p>

<p>The macro automatically tries to induct using the induction scheme.  But
<color rgb=\"#ff0000\">this only works if you're using the formals of the
flag function as the variable names in the theorems.</color>  In the case of
@('pseudo-termp'), this is pretty subtle: ACL2's definition uses different
variables for the term/list cases, i.e.,</p>

@({
    (mutual-recursion
     (defun pseudo-termp (x) ...)
     (defun pseudo-term-listp (lst) ...))
})

<p>So the theorem above only works without hints because we happened to choose
@('x') and @('lst') as our variables.  If, instead, we wanted to use different
variable names in our theorems, we'd have to give an explicit induction hint.
For example:</p>

@({
    (defthm-pseudo-termp
      (defthm type-of-pseudo-termp
        (booleanp (pseudo-termp term))
        :rule-classes :type-prescription
        :flag term)
      (defthm type-of-pseudo-term-listp
        (booleanp (pseudo-term-listp termlist))
        :rule-classes :type-prescription
        :flag list)
      :hints((\"Goal\" :induct (flag-pseudo-termp flag term termlist))))
})


<h3>Bells and Whistles</h3>

<p><color rgb='#ff0000'>New!</color> <b>Proof Templates</b>.  You can submit,
e.g., @('(defthm-pseudo-termp)'), with no arguments, to print a ``template''
that is similar to the above form.  This can be a convenient starting place for
writing down a new theorem.</p>


<p><b>Localizing Theorems</b>.  Sometimes you may only want to export one of
the theorems.  For instance, if we only want to add a rule about the term case,
but no the list case, we could do this:</p>

@({
    (defthm-pseudo-termp
      (defthm type-of-pseudo-termp
        (booleanp (pseudo-termp x))
        :rule-classes :type-prescription
        :flag term)
      (defthm type-of-pseudo-term-listp
        (booleanp (pseudo-term-listp lst))
        :flag list
        :skip t))
})

<p><b>Irrelevant Cases</b>. Sometimes the theorem you want is inductive in such
a way that some functions are irrelevant; nothing needs to be proved about them
in order to prove the desired theorem about the others.  The :skip keyword can
be used with a theorem of T to do this:</p>

@({
 (defthm-pseudo-termp
   (defthm type-of-pseudo-termp
     (booleanp (pseudo-termp x))
     :rule-classes :type-prescription
     :flag term)
   (defthm type-of-pseudo-term-listp
     t
     :flag list
     :skip t))
})

<p>Alternatively, you can provide the :skip-others keyword to the top-level
macro and simply leave out the trivial parts:</p>

@({
 (defthm-pseudo-termp
   (defthm type-of-pseudo-termp
     (booleanp (pseudo-termp x))
     :rule-classes :type-prescription
     :flag term)
   :skip-others t)
})

<p><b>Multiple Theorems</b>. You may have more than one defthm form for a given
flag.  For the main inductive proof, these are all simply conjoined
together (and their hints are simply appended together), but they are exported
as separate theorems and may have different @(':rule-classes').</p>

<p><b>Legacy Syntax</b>. There is an older, alternate syntax for @('make-flag')
that is still available.  To encourage transitioning to the new syntax, the old
syntax is not documented and should not be used.  Support for the old syntax
will eventually be removed.  If you are maintaining legacy code that still uses
the old syntax, see the comments in @('flag.lisp') for some details.</p>

<h3>Advanced Hints</h3>

<p>For advanced users, note that each individual \"theorem\" can have its own
computed hints.  For instance we can write:</p>

@({
    (defthm-pseudo-termp
      (defthm type-of-pseudo-termp
        (booleanp (pseudo-termp term))
        :rule-classes :type-prescription
        :flag term
        :hints ('(:expand ((pseudo-termp x)))))
      (defthm type-of-pseudo-term-listp
        (booleanp (pseudo-term-listp termlist))
        :rule-classes :type-prescription
        :flag list
        :hints ('(:expand ((pseudo-term-listp lst)))))
      :hints((\"Goal\" :induct (flag-pseudo-termp flag term termlist))))
})

<p>These hints are used <b>during the mutually inductive proof</b>.  Under the
top-level induction, we check the clause for the current subgoal to determine
the hypothesized setting of the flag variable, and provide the computed hints
for the appropriate case.</p>

<p>If you provide both a top-level hints form and hints on some or all of the
separate theorems, both sets of hints have an effect; try @(':trans1') on such
a defthm-flag-fn form to see what you get.</p>

<p>You may use subgoal hints as well as computed hints, but they will not have
any effect if the particular subgoal does not occur when those hints are in
effect.  We simply translate subgoal hints to computed hints:</p>

@({
    (\"Subgoal *1/5.2\" :in-theory (theory 'foo))
      --->
    (and (equal id (parse-clause-id \"Subgoal *1/5.2\"))
         '(:in-theory (theory 'foo)))
})

<p>As mentioned above, if there is more than one defthm form for a given flag,
the hints for all such forms are simply appended together; the hints given to
one such form may affect what you might think of as the proof of another.</p>
")

;; see flag-tests.lisp for examples

(defthmd expand-all-hides
  (equal (hide x) x)
  :hints (("goal" :expand ((hide x)))))


(defun acl2::flag-is (x)
  (declare (ignore x))
  t)

(in-theory (disable acl2::flag-is (acl2::flag-is) (:type-prescription acl2::flag-is)))

(defevaluator flag-is-cp-ev flag-is-cp-ev-lst ((if a b c) (acl2::flag-is x) (not x)))

(defun flag-is-cp (clause name)
  (declare (xargs :guard t))
  (list (cons `(not (acl2::flag-is ',name))
              clause)))


(defthm flag-is-cp-wellformed
  (implies (and (logic-term-listp clause w)
                (arities-okp '((not . 1)
                               (acl2::flag-is . 1))
                             w))
           (logic-term-list-listp (flag-is-cp clause name) w)))

(defthm flag-is-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp al)
                (flag-is-cp-ev (acl2::conjoin-clauses
                                (flag-is-cp clause name))
                               al))
           (flag-is-cp-ev (acl2::disjoin clause) al))
  :hints (("goal" :expand ((:free (a b) (acl2::disjoin (cons a b))))
           :in-theory (enable acl2::disjoin2 acl2::flag-is)
           :do-not-induct t))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee flag-is-cp-wellformed)))

(defun identity-cp (clause)
  (declare (xargs :guard t))
  (list clause))

(defthm identity-cp-wellformed
  (implies (logic-term-listp clause w)
           (logic-term-list-listp (identity-cp clause) w))
  :rule-classes nil)


(defthm identity-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp al)
                (flag-is-cp-ev (acl2::conjoin-clauses
                                (identity-cp clause))
                               al))
           (flag-is-cp-ev (acl2::disjoin clause) al))
  :hints (("goal" :expand ((:free (a b) (acl2::disjoin (cons a b))))
           :in-theory (enable acl2::disjoin2 acl2::flag-is)
           :do-not-induct t))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee identity-cp-wellformed)))

(program)


(defmacro id (form) form)

(defun get-clique-members (fn world)
  (or (getprop fn 'recursivep nil 'current-acl2-world world)
      (er hard 'get-clique-members
          "Expected ~s0 to be in a mutually-recursive nest.~%" fn)))

(defun get-formals (fn world)
  (getprop fn 'formals :none 'current-acl2-world world))

(defun get-body (fn last-body world)
  ;; If latest-def is nil (the default for make-flag), this gets the original,
  ;; normalized or non-normalized body based on what the user typed for the
  ;; :normalize xarg.  The use of "last" skips past any other :definition rules
  ;; that have been added since then.
  (let* ((bodies (getprop fn 'def-bodies nil 'current-acl2-world world))
         (body (cond ((eq last-body :last)
                      (car bodies))
                     ((let ((pair (assoc-eq fn last-body)))
                        (and pair
                             (or (acl2::original-def-body1 (cadr pair) bodies)
                                 (er hard 'get-body
                                     "The symbol ~x0 is associated with ~
                                      function symbol ~x1 in the :BODY ~
                                      argument of a call of ~x2.  But ~x0 is ~
                                      not the name of a :DEFINITION rule for ~
                                      ~x1."
                                     (cadr pair)
                                     fn
                                     'make-flag)))))
                     (t (car (last bodies))))))
    (if (access def-body body :hyp)
        (er hard 'get-body
            "Attempt to call get-body on a body with a non-nil hypothesis, ~x0"
            (access def-body body :hyp))
      (if (not (eq (access def-body body :equiv)
                   'equal))
          (er hard 'get-body
              "Attempt to call get-body for an equivalence relation other ~
               than equal, ~x0"
              (access def-body body :equiv))
        (access def-body body :concl)))))

(defun get-measure (fn world)
  (access justification
          (getprop fn 'justification nil 'current-acl2-world world)
          :measure))

(defun get-wfr (fn world)
  (access justification
          (getprop fn 'justification nil 'current-acl2-world world)
          :rel))

(defun make-flag-measure-aux (alist ; binds function name -> flag symbol
                              world)
  (cond ((and (consp alist)
              (consp (cdr alist)))
         (cons `(,(cdar alist) ,(get-measure (caar alist) world))
               (make-flag-measure-aux (cdr alist) world)))
        ((consp alist)
         (list `(otherwise ,(get-measure (caar alist) world))))
        (t
         (er hard 'make-flag-measure-aux "Never get here."))))

(defun make-flag-measure (flag-var  ; e.g., 'flag
                          alist     ; binds function name -> flag symbol
                          world)
  (declare (xargs :guard (symbolp flag-var)
                  :mode :program))
  `(case ,flag-var
     . ,(make-flag-measure-aux alist world)))

(defun merge-formals (alist ; flag symbol -> corresponding function
                      world)
  ;; To create the formals for the flag function, union together the formals
  ;; for all of the sub-functions (and then, separately, add the flag
  ;; variable itself.)
  (if (consp alist)
      (union-eq (get-formals (caar alist) world)
                (merge-formals (cdr alist) world))
    nil))

(defun merge-actuals (alist formals)
  ;; This is used when rewriting original function bodies so that calls of
  ;; clique members instead become calls of the flag function.
  ;;
  ;; The alist here has in it (orig-formal . actual) pairs.  We walk through
  ;; the formals and replace any orig-formal with its actual; replace any
  ;; unbound new formals with nil.
  (if (consp formals)
      (cons (cdr (assoc-eq (car formals) alist))
            (merge-actuals alist (cdr formals)))
    nil))

(mutual-recursion

 (defun mangle-body (body fn-name alist formals world)
   (cond ((atom body)
          body)
         ((eq (car body) 'quote)
          body)
         ((symbolp (car body))
          (let ((lookup   (assoc-eq (car body) alist))
                (new-args (mangle-body-list (cdr body) fn-name alist formals world)))
            (if lookup
                (let* ((orig-formals (get-formals (car lookup) world))
                       (new-actuals (merge-actuals (pairlis$ orig-formals new-args) formals)))
                  `(,fn-name ',(cdr lookup) . ,new-actuals))
              (cons (car body) new-args))))
         (t
          (let ((lformals (cadar body))
                (lbody    (caddar body))
                (largs    (cdr body)))
            (cons (list 'lambda
                        lformals
                        (mangle-body lbody  fn-name alist formals world))
                  (mangle-body-list largs fn-name alist formals world))))))

 (defun mangle-body-list (list fn-name alist formals world)
   (if (consp list)
       (cons (mangle-body (car list) fn-name alist formals world)
             (mangle-body-list (cdr list) fn-name alist formals world))
     nil)))


(defun make-flag-body-aux (flag-var fn-name formals alist full-alist last-body world)
  (if (consp alist)
      (let* ((orig-body (get-body (caar alist) last-body world))
             (new-body (mangle-body orig-body fn-name full-alist formals world)))
        (cond ((consp (cdr alist))
               (cons `((equal ,flag-var ',(cdar alist)) ,new-body)
                     (make-flag-body-aux flag-var fn-name formals (cdr alist) full-alist last-body world)))
              (t
               (list `(t ,new-body)))))
    (er hard 'make-flag-body-aux "Never get here.")))

(defun make-flag-body (fn-name flag-var alist hints ruler-extenders last-body world)
  (let ((formals (merge-formals alist world)))
    (cond
     ((or (null last-body) ; optimization
          (eq last-body :last)
          (and (symbol-doublet-listp last-body)
               (symbol-listp (acl2::strip-cadrs last-body))
               (subsetp-eq (strip-cars last-body) (strip-cars alist))))
      `(defun-nx ,fn-name (,flag-var . ,formals)
         (declare (xargs :verify-guards nil
                         :normalize nil
                         :measure ,(make-flag-measure flag-var alist world)
                         :hints ,hints
                         ,@(and ruler-extenders
                                `(:ruler-extenders ,ruler-extenders))
                         :well-founded-relation ,(get-wfr (caar alist) world)
                         :mode :logic)
                  (ignorable . ,formals))
         (cond
          .
          ,(make-flag-body-aux flag-var fn-name formals alist alist last-body world))))
     (t (er hard 'make-flag
            "The :BODY argument of ~x0 must be either ~x1, :LAST, or a list ~
             whose members have the form (sym1 sym2) where sym1 is a function ~
             symbol in the specified mutually recursive clique and sym2 is the ~
             name of a definition rule for sym1.  The value ~x2 for :LAST is ~
             therefore illegal~@3."
            'make-flag nil last-body
            (if (and (symbol-doublet-listp last-body)
                     (symbol-listp (acl2::strip-cadrs last-body)))
                (let ((clique (strip-cars alist)))
                  (msg " because the symbol~#0~[ ~&0 is~/s ~&0 are~] not in ~
                        the specified mutually recursive clique, ~x1."
                       (set-difference-eq (strip-cars last-body) clique)
                       clique))
              ""))))))

(defun extract-keyword-from-args (kwd args)
  (if (consp args)
      (if (eq (car args) kwd)
          (if (consp (cdr args))
              (cadr args)
            (er hard "Expected something to follow ~s0.~%" kwd))
        (extract-keyword-from-args kwd (cdr args)))
    nil))

(defun throw-away-keyword-parts (args)
  (if (consp args)
      (if (keywordp (car args))
          nil
        (cons (car args)
              (throw-away-keyword-parts (cdr args))))
    nil))





(defun translate-subgoal-to-computed-hints (hints)
  (declare (xargs :mode :program))
  (if (atom hints)
      nil
    (cons (if (and (consp (car hints))
                   (stringp (caar hints)))
              (let ((id (acl2::parse-clause-id (caar hints))))
                `(and (equal id ',id)
                      ',(cdar hints)))
            (car hints))
          (translate-subgoal-to-computed-hints (cdr hints)))))

(defun find-flag-hyps (flagname clause)
  (declare (xargs :mode :program))
  (if (atom clause)
      (mv nil nil)
    (let ((lit (car clause)))
      (flet ((eql-hyp-case
              (a b flagname clause)
              (cond ((and (equal a flagname) (quotep b))
                     (mv b nil))
                    ((and (equal b flagname) (quotep a))
                     (mv a nil))
                    (t (find-flag-hyps flagname (cdr clause)))))
             (uneql-hyp-case
              (a b flagname clause)
              (mv-let (equiv rest)
                (find-flag-hyps flagname (cdr clause))
                (if equiv
                    (mv equiv nil)
                  (cond ((and (equal a flagname) (quotep b))
                         (mv nil (cons b rest)))
                        ((and (equal b flagname) (quotep a))
                         (mv nil (cons a rest)))
                        (t (mv nil rest)))))))
      (case-match lit
        (('not ('equal a b))
         (eql-hyp-case a b flagname clause))
        (('not ('eql a b))
         (eql-hyp-case a b flagname clause))
        (('equal a b)
         (uneql-hyp-case a b flagname clause))
        (('eql a b)
         (uneql-hyp-case a b flagname clause))
        (& (find-flag-hyps flagname (cdr clause))))))))

(defun flag-is-hint (flagname all-names clause)
  (declare (xargs :mode :program))
  (mv-let (equiv inequivs)
    (find-flag-hyps flagname clause)
    (let ((flagval (or equiv
                       (let* ((not-ruled-out
                               (set-difference-eq all-names
                                                  (acl2::strip-cadrs inequivs))))
                         (and (eql (len not-ruled-out) 1)
                              (list 'quote (car not-ruled-out)))))))
      (and flagval
           `(:clause-processor (flag-is-cp clause ,flagval))))))

(defun find-flag-is-hyp (clause)
  (if (atom clause)
      nil
    (let ((lit (car clause)))
      (case-match lit
        (('not ('acl2::flag-is ('quote val))) val)
        (& (find-flag-is-hyp (cdr clause)))))))



(defun flag-hint-cases-fn (cases clause)
  (declare (xargs :mode :program))
  (let ((flagval (find-flag-is-hyp clause)))
    (and flagval
         (let* ((first (extract-keyword-from-args :first cases))
                (cases (throw-away-keyword-parts cases))
                (hints (cdr (assoc flagval cases))))
           (and (or first hints)
                `(:computed-hint-replacement
                  (,@first . ,(translate-subgoal-to-computed-hints hints))
                  ;; hack to say "just apply the hints from the computed-hint-replacement immediately"
                  ;; BOZO maybe there's a better way to do this?
                  :no-thanks t :clause-processor identity-cp))))))

(defmacro flag-hint-cases (&rest cases)
  `(flag-hint-cases-fn ',cases clause))



; Definition: thmpart.
;
; Each thmpart is an thing like _either_
;
; For backwards compatibility with a very old version of make-flag.  Please
; don't use this in new developments.  Maybe some day we can get rid of this.
;
;   (flag <thm-body> :name ... :rule-classes ... :doc ...)
;
;  -or-
;
;   (defthm[d] <thmname> <thm-body> :flag ... :rule-classes ...)

(defun flag-from-thmpart (thmpart)
  (if (member (car thmpart) '(defthm defthmd))
      (extract-keyword-from-args :flag thmpart)
    (car thmpart)))

(defun body-from-thmpart (thmpart)
  (cond ((not thmpart) t)
        ((member (car thmpart) '(defthm defthmd))
         ;; (defthm[d] name body ...)
         (caddr thmpart))
        (t ;; (flag body ...)
         (cadr thmpart))))

(defun collect-thmparts-for-flag (flag thmparts)
  (cond ((atom thmparts)
         nil)
        ((eq (flag-from-thmpart (car thmparts)) flag)
         (cons (car thmparts)
               (collect-thmparts-for-flag flag (cdr thmparts))))
        (t
         (collect-thmparts-for-flag flag (cdr thmparts)))))

(defun thmparts-collect-bodies (thmparts)
  (if (atom thmparts)
      nil
    (cons (body-from-thmpart (car thmparts))
          (thmparts-collect-bodies (cdr thmparts)))))

(defun thmparts-collect-hints (thmparts)
  (if (atom thmparts)
      nil
    (append (extract-keyword-from-args :hints (car thmparts))
            (thmparts-collect-hints (cdr thmparts)))))

(defun pair-up-cases-with-thmparts (flag-var alist thmparts skip-ok)
  (b* (((when (atom alist))
        (er hard 'pair-up-cases-with-thmparts
            "Never get here."))
       (flag          (cdar alist))
       (flag-thmparts (collect-thmparts-for-flag flag thmparts))
       ((when (and (not flag-thmparts)
                   (not skip-ok)))
        (er hard 'pair-up-cases-with-thmparts
            "Expected there to be a case for the flag ~s0.~%" flag))
       (bodies (thmparts-collect-bodies flag-thmparts))
       (body (if (eql (len bodies) 1)
                 (car bodies)
               `(and . ,bodies)))
       ((when (consp (cdr alist)))
        (cons `((equal ,flag-var ',flag) ,body)
              (pair-up-cases-with-thmparts flag-var (cdr alist) thmparts skip-ok))))
    (list `(t ,body))))

(defun pair-up-cases-with-hints (alist thmparts skip-ok)
  (b* (((when (atom alist))
        nil)
       (flag   (cdar alist))
       (flag-thmparts (collect-thmparts-for-flag flag thmparts))
       ((unless flag-thmparts)
        (if skip-ok
            (cons (cons flag nil)
                  (pair-up-cases-with-hints (cdr alist) thmparts skip-ok))
          (er hard 'pair-up-cases-with-hints
              "Expected there to be a case for the flag ~s0.~%" flag)))
       (hints (thmparts-collect-hints flag-thmparts)))
    (cons (cons flag hints)
          (pair-up-cases-with-hints (cdr alist) thmparts skip-ok))))

(defun flag-thm-entry-thmname (explicit-name flag entry)
  (if (member (car entry) '(defthm defthmd))
      (cadr entry)
    (or (extract-keyword-from-args :name (cddr entry))
        (if explicit-name
            (intern-in-package-of-symbol
             (concatenate 'string
                          (symbol-name explicit-name)
                          "-"
                          (symbol-name flag))
             explicit-name)
          (er hard 'flag-thm-entry-thmname
              "Expected an explicit name for each theorem, since no general ~
               name was given.  The following theorem does not have a name: ~
               ~x0~%" entry)))))

(defun flag-defthm-corollaries (lemma-name explicit-name flag-var thmparts)
  (b* (((when (atom thmparts))
        nil)
       ((when (extract-keyword-from-args :skip (car thmparts)))
        (flag-defthm-corollaries lemma-name explicit-name flag-var (cdr thmparts)))
       (thmpart (car thmparts))
       (flag    (flag-from-thmpart thmpart))
       ;; note: this can sometimes cause name conflicts when names are
       ;; generated from the flags
       (defthm[d]         (if (eq (car thmpart) 'defthmd)
                              'defthmd
                            'defthm))
       (thmname           (flag-thm-entry-thmname explicit-name flag thmpart))
       (body              (body-from-thmpart thmpart))
       (rule-classes-look (member :rule-classes thmpart))
; Commented out by Matt K. for post-v-7.1 removal of :doc for defthm:
       ;;(doc               (extract-keyword-from-args :doc thmpart))
       )
    (cons `(with-output :stack :pop
             (,defthm[d] ,thmname
               ,body
               ,@(and rule-classes-look
                      `(:rule-classes ,(cadr rule-classes-look)))
               ;; :doc ,doc ; Removed by Matt K.; see comment above
               :hints(("Goal"
                       :in-theory (theory 'minimal-theory)
                       :use ((:instance ,lemma-name (,flag-var ',flag)))))))
          (flag-defthm-corollaries lemma-name explicit-name flag-var (cdr thmparts)))))

(defun find-first-thm-name (thmparts)
  (cond ((atom thmparts)
         (er hard? 'find-first-thm-name
             "No explicit name given, and no theorems are given names?"))
        ((extract-keyword-from-args :skip (cddr (car thmparts)))
         (find-first-thm-name (cdr thmparts)))
        (t
         (flag-thm-entry-thmname
          nil (flag-from-thmpart (car thmparts)) (car thmparts)))))


;; [Jared] we previously just looked for a user-supplied Goal hint as the first
;; item in the hints list.  But this didn't work at all and led to really weird
;; failures when using unconventional hint orders like
;;
;;   :hints(("Subgoal *1/3" ...)
;;          ("Goal" ...))
;;
;; So, now work harder to find hints that are targeting Goal.

(defun find-first-goal-hint (user-hints)
  (cond ((atom user-hints)
         nil)
        ((atom (car user-hints))
         (er hard? 'find-first-goal-hint "Malformed entry in hints: ~x0.~%" (car user-hints)))
        ((and (stringp (caar user-hints))
              (equal (acl2::string-upcase (caar user-hints)) "GOAL"))
         (car user-hints))
        (t
         (find-first-goal-hint (cdr user-hints)))))

(defun make-flag-template-cases (alist ; binds function name -> flag symbol
                                 world)
  (b* (((when (atom alist))
        nil)
       ((cons fnname flag-symbol) (car alist))
       (thmname (intern-in-package-of-symbol
                 (concatenate 'string "THEOREM-FOR-" (symbol-name fnname))
                 fnname))
       (hyp1 (intern-in-package-of-symbol "HYP1" fnname))
       (hyp2 (intern-in-package-of-symbol "HYP2" fnname))
       (prop (intern-in-package-of-symbol "PROP" fnname))
       (fnargs  (get-formals fnname world))
       (mock-thm `(defthm ,thmname
                    (implies (and ,hyp1 ,hyp2)
                             (,prop (,fnname . ,fnargs)))
                    :flag ,flag-symbol)))
    (cons mock-thm
          (make-flag-template-cases (cdr alist) world))))

(defun make-flag-template (real-macro-name ; e.g., 'defthm-pseudo-termp
                           alist           ; binds function name -> flag symbol
                           world)
  (b* ((template-cases (make-flag-template-cases alist world))
       (template       (cons real-macro-name template-cases)))
    (cw "~|Here's a template for using ~s0:~%~%~p1"
        real-macro-name template)
    (cw "~|~%You'll probably want to adjust the names, hyps, and conclusion ~
         terms above.  Note also that you can use :skip, :rule-classes, etc.; ~
         for more information see :doc make-flag.~%")
    nil))

(defun flag-defthm-fn (args            ; user supplied args
                       real-macro-name ; e.g., 'defthm-pseudo-termp
                       alist           ; binds function name -> flag symbol
                       flag-var        ; e.g., 'flag
                       flag-fncall     ; e.g., (flag-foo flag ...)
                       )
  (b* (((unless args)
        `(make-event
          (b* ((- (make-flag-template ',real-macro-name ',alist (w state))))
            (value `(value-triple :invisible)))))
       (explicit-name (and (symbolp (car args)) (car args)))
       (args (if explicit-name (cdr args) args))
       (thmparts (throw-away-keyword-parts args))
       (name (if explicit-name
                 (intern-in-package-of-symbol
                  (concatenate 'string "FLAG-LEMMA-FOR-"
                               (symbol-name explicit-name))
                  explicit-name)
               (intern-in-package-of-symbol
                (concatenate 'string "FLAG-LEMMA-FOR-"
                             (symbol-name
                              (find-first-thm-name thmparts)))
                (car flag-fncall))))
       (instructions (extract-keyword-from-args :instructions args))
       (user-hints (extract-keyword-from-args :hints args))
       (no-induction-hint (extract-keyword-from-args :no-induction-hint args))
       (skip-ok (extract-keyword-from-args :skip-others args))
       (user-goal-hint (find-first-goal-hint user-hints))
       (user-other-hints (remove1-equal user-goal-hint user-hints))
       (hints (and (not instructions)
                   (append
                    (cond (no-induction-hint user-hints)
                          (user-goal-hint
                           ;; First hint is for goal.
                           (if (extract-keyword-from-args :induct user-goal-hint)
                               ;; Explicit induct hint is provided; do not override.
                               user-hints
                             ;; Provide our induct hint in addition to the hints
                             ;; provided in goal.
                             (cons `("Goal" :induct ,flag-fncall . ,(cdr user-goal-hint))
                                   user-other-hints)))
                          ;; No goal hint; cons our induction hint onto the rest.
                          (t (cons `("Goal" :induct ,flag-fncall)
                                   user-hints)))
                    (list
                     `(flag-is-hint ',flag-var ',(strip-cdrs alist) clause)
                     `(flag-hint-cases
                       . ,(pair-up-cases-with-hints alist thmparts skip-ok)))))))

    `(with-output :off :all :on (error) :stack :push
       (progn
         (encapsulate
           ()
           (local
            (with-output :stack :pop
              (defthm ,name
                (cond . ,(pair-up-cases-with-thmparts
                          flag-var alist thmparts skip-ok))
                :rule-classes nil
                :hints ,hints
                :instructions ,instructions
                :otf-flg ,(extract-keyword-from-args :otf-flg args))))

           . ,(flag-defthm-corollaries name explicit-name flag-var thmparts))
         (with-output :stack :pop (value-triple ',name))))))

(defun make-defthm-macro (real-macro-name ; e.g., defthm-pseudo-termp
                          alist           ; binds function name -> flag symbol
                          flag-var        ; e.g., 'flag
                          flag-fncall     ; call of the flag function
                          )
  `(defmacro ,real-macro-name (&rest args) ;; was (name &rest args)
     `(make-event
       (flag-defthm-fn ',args
                       ',',real-macro-name
                       ',',alist
                       ',',flag-var
                       ',',flag-fncall))))


(defun make-cases-for-equiv (alist world)
  (if (consp alist)
      (let* ((fn   (caar alist))
             (flag (cdar alist))
             (fn-formals (get-formals fn world)))
        (if (consp (cdr alist))
            (cons `(,flag (,fn . ,fn-formals))
                  (make-cases-for-equiv (cdr alist) world))
          (list `(otherwise (,fn . ,fn-formals)))))
    nil))


(defun equiv-theorem-cases (flag-fn formals alist world)
  (if (consp alist)
      (let* ((fn   (caar alist))
             (flag (cdar alist))
             (fn-formals (get-formals fn world)))
        (cons `(equal (,flag-fn ',flag . ,formals)
                      (,fn . ,fn-formals))
              (equiv-theorem-cases flag-fn formals (cdr alist) world)))
    nil))



; NOTE: Expand-calls-computed-hint moved to std/util/support.

; NEW HINT: this more limited hint seems to be better.

(defun flag-expand-computed-hint (stable-under-simplificationp clause fns)
  (and stable-under-simplificationp
       (let ((conclusion (car (last clause))))
         (case-match conclusion
           (('equal lhs rhs)
            (let* ((expands (if (and (consp lhs)
                                     (member (car lhs) fns))
                                (list lhs)
                              nil))
                   (expands (if (and (consp rhs)
                                     (member (car rhs) fns))
                                (cons rhs expands)
                              expands)))
              (and expands
                   `(:expand (:lambdas . ,expands)))))
           (&
            nil)))))

(defun flag-table-events (alist entry)
  (if (atom alist)
      nil
    (cons `(table flag-fns ',(caar alist) ',entry)
          (flag-table-events (cdr alist) entry))))

(defun apply-formals-subst (formals subst)
  (b* (((when (atom formals))
        nil)
       (look (assoc (car formals) subst))
       ((when (and look
                   (not (and (true-listp look)
                             (= (length look) 2)
                             (symbolp (cadr look))))))
        (er hard 'make-flag
            "The :formals-subst argument of a call of ~x0 must be a list ~
             whose members each have the form (name1 name2), where name1 and ~
             name2 are symbols.  That list has the illegal element ~x1."
            'make-flag look))
       ((when look)
        (cons (cadr look) (apply-formals-subst (cdr formals) subst))))
    (cons (car formals) (apply-formals-subst (cdr formals) subst))))

(defun thm-macro-name (flag-fn-name)
  (intern-in-package-of-symbol
   (concatenate 'string "DEFTHM-" (symbol-name flag-fn-name))
   flag-fn-name))

(defun equivalences-name (flag-fn-name)

; This function was introduced by Matt K. in order to be able to call it
; elsewhere.  Such functions could be introduced for other such symbol
; constructors in this file.

  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name flag-fn-name) "-EQUIVALENCES")
   flag-fn-name))

(defun convert-flag-mapping (x x-original)
  (let ((str "The :flag-mapping argument of make-flag should be a true-list, ~
              each of whose members is ideally of the forms (name1 name2).  ~
              The value ~x0 is thus illegal."))
    (cond ((null x) nil)
          ((atom x) (er hard 'make-flag str x-original))
          (t (b* ((old (car x))
                  (new (case-match old
                         ((s1 s2) (and (symbolp s1)
                                       (symbolp s2)
                                       (cons s1 s2)))
                         ((s1 . s2) (and (symbolp s1)
                                         (symbolp s2)
                                         old))
                         (& (er hard 'make-flag str x-original)))))
               (cons new
                     (convert-flag-mapping (cdr x) x-original)))))))

(defun make-flag-fn (flag-fn-name clique-member-name flag-var flag-mapping hints
                                  defthm-macro-name
                                  formals-subst
                                  local ruler-extenders last-body world)
  (let* ((flag-var (or flag-var
                       (intern-in-package-of-symbol "FLAG" flag-fn-name)))
         (alist (if flag-mapping
                    (convert-flag-mapping flag-mapping flag-mapping)
                  (pairlis$ (get-clique-members clique-member-name world)
                            (get-clique-members clique-member-name world))))
         (defthm-macro-name (or defthm-macro-name
                                (thm-macro-name flag-fn-name)))
         (equiv-thm-name (equivalences-name flag-fn-name))
         (formals        (merge-formals alist world)))
    `(,@(if local '(progn) '(encapsulate nil))
      ;; use encapsulate instead of progn so set-ignore-ok is local to this
      (logic)
      (set-ignore-ok t) ;; can't wrap this in local --- fubar!

      (,(if local 'local 'id)
       ,(make-flag-body flag-fn-name flag-var alist hints ruler-extenders last-body world))
      ,(make-defthm-macro defthm-macro-name alist flag-var
                          `(,flag-fn-name ,flag-var
                                          . ,(apply-formals-subst formals formals-subst)))

      (,(if local 'local 'id)
       (with-output
        :off (prove event) ;; hides induction scheme, too
        (encapsulate nil
          (logic)
          (local (defthm flag-equiv-lemma
                   (equal (,flag-fn-name ,flag-var . ,formals)
                          (case ,flag-var
                            ,@(make-cases-for-equiv alist world)))
                   :hints (("Goal"
                            :induct
                            (,flag-fn-name ,flag-var . ,formals)
                            :in-theory

; Matt K. mod, March 2021: Formerly only the induction rune below was in the
; theory, but now we include guard-holders, following a suggested approach from
; Eric Smith.  A slight variant of his example is below.  Before adding
; guard-holders to the theory here, the call of make-flag in that example
; failed because of a disconnect between the body of evenlp, which has a call
; of guard-holder THE-CHECK due to its xargs declaration, and the induction
; scheme of the flag function, which (like all induction schemes) has had
; guard-holders removed.  I considered going further and adding in (theory
; 'minimal-theory), but the comment below suggested that this has already been
; attempted and there were performance issues.  Here is the example promised
; above.
;
;   (include-book "tools/flag" :dir :system)
;   (mutual-recursion
;    (defun evenlp (x)
;      (declare (xargs :guard t :normalize nil))
;      (if (consp x) (oddlp (cdr (the cons x))) t))
;    (defun oddlp (x)
;      (declare (xargs :guard t))
;      (if (consp x) (evenlp (cdr x)) nil)))
;   (make-flag evenlp)

; However, existing comments just below suggest that such a change has been
; considered previously.  I am incorporating the suggestions that they made and
; preserving the comments, except that I am commenting out expand-all-hides
; because I don't know whether it is currently beneficial here.

                            (union-theories
                             '((:induction ,flag-fn-name))
                             ;; see remove-guard-holders1 and comment above
                             '(return-last mv-list cons-with-hint the-check))
                            ;; (set-difference-theories
                            ;;  (union-theories (theory 'minimal-theory)
                            ;;                  '((:induction ,flag-fn-name)
                            ;;                    (:rewrite expand-all-hides)))
                            ;;  '(;; Jared found mv-nth to be slowing down a couple of flag
                            ;;    ;; function admissions.  Take it out of the minimal theory.
                            ;;    (:definition mv-nth)
                            ;;    ;; Jared found a case where "linear" forced some goals
                            ;;    ;; from an equality, which were unprovable.  So, turn
                            ;;    ;; off forcing.
                            ;;    (:executable-counterpart force)
                            ;;    ;; Turn of NOT to prevent case-splitting and
                            ;;    ))
                            )
                           (flag-expand-computed-hint stable-under-simplificationp
                                                      ACL2::clause
                                                      ',(cons flag-fn-name
                                                              (strip-cars
                                                               alist))))))
          (defthm ,equiv-thm-name
            (and . ,(equiv-theorem-cases flag-fn-name formals alist world))
            :hints(("Goal" :in-theory (union-theories
                                       '(flag-equiv-lemma)
                                       (theory 'acl2::minimal-theory))))))))

      (progn . ,(flag-table-events alist `(,flag-fn-name
                                           ,alist
                                           ,defthm-macro-name
                                           ,equiv-thm-name)))
      (,(if local 'local 'id)
       (in-theory (disable (:definition ,flag-fn-name)))))))

(defconst *make-flag-keywords*
  '(:flag-var
    :flag-mapping
    :formals-subst
    :hints
    :defthm-macro-name
    :local
    :ruler-extenders
    :body))

(defun make-flag-dwim (args world)
  ;; Stupid wrapper so that you don't have to explicitly name the flag var
  (b* (((mv names kwd/args) (acl2::split-at-first-keyword args))
       ((unless (consp names))
        (er hard? 'make-flag "No name given"))
       ((unless (symbolp (first names)))
        (er hard? 'make-flag "Name is not a symbol: ~x0" (first names)))

       ((unless (or (eql 1 (len names))
                    (eql 2 (len names))))
        (er hard? 'make-flag "Too many names: ~x0~%" names))
       ((unless (symbolp (second names)))
        (er hard? 'make-flag "Clique member name is not a symbol: ~x0" (second names)))

       ((mv flag-name clique-member-name)
        (if (eql 2 (len names))
            (mv (first names) (second names))
          ;; Just one name, so it should be a clique-member name and we will
          ;; name the flag function flag-foo.
          (mv (intern-in-package-of-symbol
               (concatenate 'string "FLAG-" (symbol-name (first names)))
               (first names))
              (first names))))
       ((mv kwd-alist other-args)
        (std::extract-keywords `(make-flag ,(first names)) *make-flag-keywords* kwd/args nil))
       ((unless (atom other-args))
        (er hard? 'make-flag "Spurious arguments: ~x0" other-args)))
    (make-flag-fn flag-name clique-member-name
                  (cdr (assoc :flag-var kwd-alist))
                  (cdr (assoc :flag-mapping kwd-alist))
                  (cdr (assoc :hints kwd-alist))
                  (cdr (assoc :defthm-macro-name kwd-alist))
                  (cdr (assoc :formals-subst kwd-alist))
                  (cdr (assoc :local kwd-alist))
                  (cdr (assoc :ruler-extenders kwd-alist))
                  (cdr (assoc :body kwd-alist))
                  world)))

(defmacro make-flag (&rest args)
  `(make-event (make-flag-dwim ',args (w state))))


;; Accessors for the records stored in the flag-fns table
(defun flag-present (fn world)
  (consp (assoc-eq fn (table-alist 'flag::flag-fns world))))

(defun flag-fn-name (fn world)
  (nth 0 (cdr (assoc-eq fn (table-alist 'flag::flag-fns world)))))

(defun flag-alist (fn world)
  (nth 1 (cdr (assoc-eq fn (table-alist 'flag::flag-fns world)))))

(defun flag-defthm-macro (fn world)
  (nth 2 (cdr (assoc-eq fn (table-alist 'flag::flag-fns world)))))

(defun flag-equivs-name (fn world)
  (nth 3 (cdr (assoc-eq fn (table-alist 'flag::flag-fns world)))))




(defxdoc def-doublevar-induction
  :parents (mutual-recursion)
  :short "Create an induction scheme that adds a duplicate variable to the substitution."
  :long "<p>Certain types of proofs require inductions that are rather simple
modifications of existing induction schemes.  For example, to prove a
congruence on some recursive function, typically you want to induct
<em>almost</em> on that function, but with the simple modification that for
each substitution in the induction scheme, you want to basically copy the
substitution of an existing variable into a new variable.</p>

<p>For example, consider our attempt to prove that sum-pairs-list is nat-list congruent:</p>
@({
 (defun nat-list-equiv (x y)
   (if (atom x)
       (atom y)
     (and (consp y)
          (equal (nfix (car x)) (nfix (car y)))
          (nat-list-equiv (cdr x) (cdr y)))))

 (defun sum-pairs-list (x)
   (if (atom x)
       nil
     (if (atom (cdr x))
         (list (nfix (car x)))
       (cons (+ (nfix (car x)) (nfix (cadr x)))
             (sum-pairs-list (cddr x))))))

 (defequiv nat-list-equiv)

 (defthm sum-pairs-list-nat-list-equiv-congruence
   (implies (nat-list-equiv x y)
            (equal (sum-pairs-list x) (sum-pairs-list y)))
   :rule-classes :congruence)
})

<p>The proof of the congruence rule fails with no hint, and neither of the
following induction hints don't help either:</p>

@({
  :hints ((\"goal\" :induct (nat-list-equiv x y))))
  :hints ((\"goal\" :induct (list (sum-pairs-list x)
                                  (sum-pairs-list y))))
})

<p>What we really want is an induction scheme that inducts as sum-pairs-list
on (say) x, but does a similar substitution on y, e.g.,</p>

@({
 (defun sum-pairs-list-double-manual (x y)
   (declare (ignorable y))
   (if (atom x)
       nil
     (if (atom (cdr x))
         (list (nfix (car x)))
       (cons (+ (nfix (car x)) (nfix (cadr x)))
             (sum-pairs-list-double-manual (cddr x) (cddr y))))))

 (defthm sum-pairs-list-nat-list-equiv-congruence ;; sum-pairs-list-double-manual works
   (implies (nat-list-equiv x y)
            (equal (sum-pairs-list x) (sum-pairs-list y)))
   :hints ((\"goal\" :induct (sum-pairs-list-double-manual x y)))
   :rule-classes :congruence)
})

<p>Def-doublevar-ind automatically generates a function like this, e.g.:</p>

@({
 (def-doublevar-induction sum-pairs-list-double
   :orig-fn sum-pairs-list
   :old-var x :new-var y)

 (defthm sum-pairs-list-nat-list-equiv-congruence ;; sum-pairs-list-double works
   (implies (nat-list-equiv x y)
            (equal (sum-pairs-list x) (sum-pairs-list y)))
   :hints ((\"goal\" :induct (sum-pairs-list-double x y)))
   :rule-classes :congruence)
})

<p>This can be used with flag functions and their defthm macros (see @(see make-flag)): use def-doublevar-ind to define a new induction scheme based on the flag function, and give a hint to the flag defthm macro to use that induction scheme. For example,</p>
@({
 (flag::make-flag foo-flag foo-mutualrec ...)

 (flag::def-doublevar-ind foo-doublevar-ind
   :orig-fn foo-flag
   :old-var x :new-var y)

 (defthm-foo-flag
  (defthm foo1-thm ...)
  (defthm foo2-thm ...)
  :hints ((\"goal\" :induct (foo-doublevar-ind flag x a b y))))
})
")


(defun doublevar-transform-calls (calls fnname old-var-index old-var new-var)
  (if (atom calls)
      nil
    (let ((actuals (cdr (car calls))))
      (cons (cons fnname (append actuals
                                 (list
                                  (acl2::subst-var new-var old-var (nth old-var-index actuals)))))
            (doublevar-transform-calls (cdr calls) fnname old-var-index old-var new-var)))))

(defun doublevar-different-equals-p (test1 test2)
  (and (consp test1)
       (consp test2)
       (eq (car test1) 'equal)
       (eq (car test2) 'equal)
       (let* ((quote1 (if (quotep (cadr test1))
                          (cadr test1)
                        (and (quotep (caddr test1))
                             (caddr test1))))
              (quote2 (if (quotep (cadr test2))
                          (cadr test2)
                        (and (quotep (caddr test2))
                             (caddr test2)))))
         (and quote1
              quote2
              (not (equal quote1 quote2))
              (or (equal (cadr test1) (cadr test2))
                  (equal (cadr test1) (caddr test2))
                  (equal (caddr test1) (cadr test2))
                  (equal (caddr test1) (caddr test2)))))))

(defun do-both (x y)
  (declare (xargs :mode :logic))
  (list x y))

(defmacro do-all (&rest args)
  (cond ((atom args) nil)
        ((atom (cdr args)) (car args))
        (t (xxxjoin 'do-both args))))

(defun doublevar-make-simple-tests/calls (tests calls)
  (declare (xargs :mode :program))
  (if (atom tests)
      calls
    (let* ((negp (and (consp (car tests))
                      (eq (caar tests) 'not)))
           (test-term (if negp (cadar tests) (car tests)))
           (rest (doublevar-make-simple-tests/calls (cdr tests) calls)))
      (if negp
          `(if ,test-term nil (do-all ,rest))
        `(if ,test-term (do-all ,rest) nil)))))



(mutual-recursion
 (defun doublevar-place-calls-in-body (tests calls-term term)
   (declare (xargs :measure (make-ord 1 (+ 1 (acl2-count term))
                                      (acl2-count tests))
                   :mode :program))
   ;; The existing term is of type DOTERM in the following schema:
   ;;  DOTERM ::= (DO-ALL IFTERM ... IFTERM) | NIL
   ;;  IFTERM  ::=  (if TEST DOTERM DOTERM)
   ;;               | recursive-call

   ;; The simplest way to write this function would be:
   ;; `(do-both (and ,@tests ,calls-term) ,term)
   ;; But this would replicate a lot of the IF structure in a lot of different
   ;; places and make a mess.  We instead try to reuse the same IF structure as
   ;; much as possible.

  ;; For a given DOTERM, we look through the various subterms for an IF whose
  ;; test is compatible with the first one in TESTS.  That is, it's the same
  ;; condition modulo negation, or is checking equality of the same term with
  ;; different constants.
   (if (atom term)
       `(do-all ,(doublevar-make-simple-tests/calls tests calls-term))
     ;; term is (do-all . ,subterms)
     (cons 'do-all (doublevar-find-if-to-place-calls tests calls-term (cdr term)))))

 (defun doublevar-find-if-to-place-calls (tests calls-term subterms)
   ;; Returns a list of IFTERMs, including the existing subterms and the tests/calls.
   (if (atom subterms)
       (list (doublevar-make-simple-tests/calls tests calls-term))
     (if (not (eq (caar subterms) 'if))
         (cons (car subterms)
               (doublevar-find-if-to-place-calls tests calls-term (cdr subterms)))
       (let* ((negp (and (consp (car tests))
                         (eq (caar tests) 'not)))
              (test-term (if negp (cadar tests) (car tests)))

              (subterm-test (second (car subterms)))

              (diff-equals (and (not negp)
                                (doublevar-different-equals-p test-term subterm-test)))
              (compatible (or (equal test-term subterm-test)
                              diff-equals)))
         (if (not compatible)
             (cons (car subterms)
                   (doublevar-find-if-to-place-calls tests calls-term (cdr subterms)))
           (let* ((then-branchp (and (not diff-equals) (not negp)))
                  (rest-tests (if diff-equals tests (cdr tests)))
                  (sub-branch
                   (doublevar-place-calls-in-body
                    rest-tests calls-term
                    (if then-branchp
                        (third (car subterms))
                      (fourth (car subterms))))))
             (cons (if then-branchp
                       `(if ,subterm-test
                            ,sub-branch
                          ,(fourth (car subterms)))
                     `(if ,subterm-test
                          ,(third (car subterms))
                        ,sub-branch))
                   (cdr subterms)))))))))


(defun doublevar-ind-body (ind-machine fnname old-var-index old-var new-var term)
  (declare (xargs :mode :program))
  (if (atom ind-machine)
      term
    (let* ((tests (access acl2::tests-and-calls (car ind-machine) :tests))
           (calls (access acl2::tests-and-calls (car ind-machine) :calls))
           (calls-term `(list ,(len ind-machine)
                              . ,(doublevar-transform-calls
                                  calls fnname old-var-index old-var new-var)))
           (new-term (doublevar-place-calls-in-body tests calls-term term)))
      (doublevar-ind-body (cdr ind-machine) fnname old-var-index old-var new-var new-term))))


(defun def-doublevar-induction-fn (name f old-var new-var hints take w)
  (declare (xargs :mode :program))
  (let* ((formals (get-formals f w))
         (ind-machine (getprop f 'acl2::induction-machine :none 'current-acl2-world w)))
    (cond ((eq formals :none)
           (er hard? 'def-doublevar-induction-fn
               "~x0 is not a function -- no formals~%" f))
          ((not (member-eq old-var formals))
           (er hard? 'def-doublevar-induction-fn
               "~x0 is not an existing formal of ~x1~%" old-var f))
          ((eq ind-machine :none)
           (er hard? 'def-doublevar-induction-fn
               "~x0 has no induction machine -- not singly recursive?~%" f))
          (t
           (let* ((measure (get-measure f w))
                  (wfr (get-wfr f w))
                  (old-var-index (search (list old-var) formals))
                  (all-formals (append formals (list new-var))))
             `(defun-nx ,name ,all-formals
                (declare (xargs :verify-guards nil
                                :measure ,measure
                                :hints ,hints
                                :well-founded-relation ,wfr
                                :ruler-extenders (do-both mv-list return-last)
                                :mode :logic)
                         (ignorable . ,all-formals))
                ,(doublevar-ind-body (if take
                                         (take take ind-machine)
                                       ind-machine)
                                     name old-var-index old-var new-var nil)))))))

(defmacro def-doublevar-induction (name &key orig-fn old-var new-var hints take)
  `(make-event
    (def-doublevar-induction-fn ',name ',orig-fn ',old-var ',new-var ',hints ',take (w state))))
