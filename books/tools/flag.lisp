; Make-flag -- Introduce induction scheme for mutually recursive functions.
; Copyright (C) 2008-2010 Centaur Technology
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
; Original authors: Sol Swords and Jared Davis
;                   {sswords,jared}@centtech.com

#||  for interactive development, you'll need to ld the package first:

(ld ;; fool dependency scanner
 "flag-package.lsp")

||#

(in-package "FLAG")
(include-book "xdoc/top" :dir :system)

(defxdoc make-flag
  :parents (mutual-recursion)
  :short "Create a flag-based @(see induction) scheme for a @(see
mutual-recursion)."

  :long "<p>The @('make-flag') macro lets you quickly introduce:</p>

<ul>

<li>a \"flag function\" that mimics a @(see mutual-recursion), and</li>

<li>a macro for proving properties by induction according to the flag
function.</li>

</ul>

<p>Generally speaking, writing a corresponding flag function is the first step
toward proving any inductive property about mutually recursive definitions;
more discussion below.</p>

<h3>Using @('make-flag')</h3>

<p>Example:</p>

@({
 (make-flag flag-pseudo-termp               ; flag function name
            pseudo-termp                    ; any member of the clique
            ;; optional arguments:
            :flag-mapping ((pseudo-termp      . term)
                           (pseudo-term-listp . list))
            :defthm-macro-name defthm-pseudo-termp
            :flag-var flag
            :hints ((\"Goal\" ...))         ; for the measure theorem
                                          ; usually not necessary
            )
})

<p>Here @('pseudo-termp') is the name of a function in a mutually recursive
clique.  In this case, the clique has two functions, @('pseudo-termp') and
@('pseudo-term-listp').  name of the newly generated flag function will be
@('flag-pseudo-termp').</p>

<p>The other arguments are optional:</p>

<ul>

<li>@(':flag-mapping') specifies short names to identify with each of the
functions of the clique.  By default we just use the function names themselves,
but it's usually nice to pick shorter names since you'll have to mention them
in the theorems you prove.</li>

<li>@(':defthm-macro-name') lets you name the new macro that will be generated
for proving theorems by inducting with the flag function.  By default it is
named @('defthm-[flag-function-name]'), i.e., for the above example, it would
be called @('defthm-flag-psuedo-termp').</li>

<li>@(':flag-var') specifies the name of the variable to use for the flag.  By
default it is just called @('flag'), and we rarely change it.  To be more
precise, it is @('pkg::flag') where @('pkg') is the package of the new flag
function's name; usually this means you don't have to think about the
package.</li>

</ul>


<h3>Proving Theorems with @('make-flag')</h3>

<p>To prove an inductive theorem about a mutually-recursive function, usually
one has to effectively prove a big ugly formula that has a different case for
different theorem about each function in the clique.</p>

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

<p>Sometimes you may only want to export one of the theorems.  For instance, if
we only want to add a rule about the term case, but no the list case, we could
do this:</p>

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

<p>Sometimes the theorem you want is inductive in such a way that some
functions are irrelevant; nothing needs to be proved about them in order to
prove the desired theorem about the others.  The :skip keyword can be used with
a theorem of T to do this:</p>
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


<p>There is an older, alternate syntax for @('make-flag') that is still
available.  To encourage transitioning to the new syntax, the old syntax is not
documented and should usually not be used.</p>

<h3>Advanced Hints</h3>

<p>For advanced users, note that each individual \"theorem\" can have its own
computed hints.  For instance we can write:</p>

@({
 (defthm-pseudo-termp
   (defthm type-of-pseudo-termp
     (booleanp (pseudo-termp term))
     :rule-classes :type-prescription
     :flag term
     :hints ('(:expand ((pseudo-termp x))))
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
})")

; Examples
#|
(include-book  ;; this newline is so that this is ignored in dependency scanning
 "tools/flag" :dir :system)

(FLAG::make-flag flag-pseudo-termp
                 pseudo-termp
                 :flag-var flag
                 :flag-mapping ((pseudo-termp . term)
                                (pseudo-term-listp . list))
                 ;; :hints {for the measure theorem}
                 :defthm-macro-name defthm-pseudo-termp
                 ;; make everything local but the defthm macro
                 :local t
                 )

; This introduces (flag-pseudo-termp flag x lst)
; Theorems equating it with pseudo-termp and pseudo-term-listp
; And the macro shown below.

(in-theory (disable (:type-prescription pseudo-termp)
                    (:type-prescription pseudo-term-listp)))

(defthm-pseudo-termp type-of-pseudo-termp
  (term (booleanp (pseudo-termp x))
        :rule-classes :rewrite
        :doc nil)
  (list (booleanp (pseudo-term-listp lst))
        )
  :hints(("Goal"
          :induct (flag-pseudo-termp flag x lst))))


(defstobj term-bucket
  (terms))

(mutual-recursion

 (defun terms-into-bucket (x term-bucket)
   ;; Returns (mv number of terms added, term-bucket)
   (declare (xargs :stobjs (term-bucket)
                   :verify-guards nil))
   (cond ((or (atom x)
              (quotep x))
          (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
            (mv 1 term-bucket)))
         (t
          (mv-let (numterms term-bucket)
                  (terms-into-bucket-list (cdr x) term-bucket)
                  (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
                    (mv (+ numterms 1) term-bucket))))))

 (defun terms-into-bucket-list (x term-bucket)
   (declare (xargs :stobjs (term-bucket)))
   (if (atom x)
       (mv 0 term-bucket)
     (mv-let (num-car term-bucket)
             (terms-into-bucket (car x) term-bucket)
             (mv-let (num-cdr term-bucket)
                     (terms-into-bucket-list (cdr x) term-bucket)
                     (mv (+ num-car num-cdr) term-bucket))))))

(terms-into-bucket '(f x y z) term-bucket)

(FLAG::make-flag flag-terms-into-bucket
                 terms-into-bucket)
|#


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
  :rule-classes :clause-processor)




(program)





(defmacro id (form) form)

(defun get-clique-members (fn world)
  (or (getprop fn 'recursivep nil 'current-acl2-world world)
      (er hard 'get-clique-members "Expected ~s0 to be in a mutually-recursive nest.~%"
          fn)))

(defun get-formals (fn world)
  (getprop fn 'formals nil 'current-acl2-world world))

(defun get-body (fn world)
  ;; This gets the original, normalized or non-normalized body based on what
  ;; the user typed for the :normalize xarg.  The use of "last" skips past
  ;; any other :definition rules that have been added since then.
  (access def-body
          (car (last (getprop fn 'def-bodies nil 'current-acl2-world world)))
          :concl))

(defun get-measure (fn world)
  (access justification
          (getprop fn 'justification nil 'current-acl2-world world)
          :measure))

(defun get-wfr (fn world)
  (access justification
          (getprop fn 'justification nil 'current-acl2-world world)
          :rel))

(defun make-flag-measure-aux (alist world)
  (cond ((and (consp alist)
              (consp (cdr alist)))
         (cons `(,(cdar alist) ,(get-measure (caar alist) world))
               (make-flag-measure-aux (cdr alist) world)))
        ((consp alist)
         (list `(otherwise ,(get-measure (caar alist) world))))
        (t
         (er hard 'make-flag-measure-aux "Never get here."))))

(defun make-flag-measure (flag-var alist world)
  (declare (xargs :guard (symbolp flag-var)
                  :mode :program))
  `(case ,flag-var
     . ,(make-flag-measure-aux alist world)))

(defun merge-formals (alist world)
  (if (consp alist)
      (union-eq (get-formals (caar alist) world)
                (merge-formals (cdr alist) world))
    nil))

(defun merge-actuals (alist formals)
  ;; The alist has in it (orig-formal . actual) pairs.  Walk through formals
  ;; and replace any orig-formal with its actual; replace any unbound new
  ;; formals with nil.
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


(defun make-flag-body-aux (fn-name formals alist full-alist world)
  (if (consp alist)
      (let* ((orig-body (get-body (caar alist) world))
             (new-body (mangle-body orig-body fn-name full-alist formals world)))
        (cond ((consp (cdr alist))
               (cons `(,(cdar alist) ,new-body)
                     (make-flag-body-aux fn-name formals (cdr alist) full-alist world)))
              (t
               (list `(otherwise ,new-body)))))
    (er hard 'make-flag-body-aux "Never get here.")))

(defun make-flag-body (fn-name flag-var alist hints world)
  (let ((formals (merge-formals alist world)))
  `(defun-nx ,fn-name (,flag-var . ,formals)
     (declare (xargs :verify-guards nil
                     :normalize nil
                     :measure ,(make-flag-measure flag-var alist world)
                     :hints ,hints
                     :well-founded-relation ,(get-wfr (caar alist)
                                                      world)
                     :mode :logic)
              (ignorable . ,formals))
     (case ,flag-var
       .
       ,(make-flag-body-aux fn-name formals alist alist world)))))

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

(defun flag-hint-cases-fn (flagname cases clause)
  (declare (xargs :mode :program))
  (mv-let (equiv inequivs)
    (find-flag-hyps flagname clause)
    (let ((flagval (or equiv
                       (let* ((possibilities (strip-cars cases))
                              (not-ruled-out
                               (set-difference-eq possibilities
                                                  (acl2::strip-cadrs inequivs))))
                         (and (eql (len not-ruled-out) 1)
                              (list 'quote (car not-ruled-out)))))))
      (and flagval
           (let ((hints (cdr (assoc (cadr flagval) cases))))
             `(:computed-hint-replacement
               ,(translate-subgoal-to-computed-hints hints)
               :clause-processor (flag-is-cp clause ,flagval)))))))

(defmacro flag-hint-cases (flagname &rest cases)
  `(flag-hint-cases-fn ',flagname ',cases clause))




(defun flag-from-thmpart (thmpart)
  (if (eq (car thmpart) 'defthm)
      (extract-keyword-from-args :flag thmpart)
    (car thmpart)))

(defun assoc-flag-in-thmparts (flag thmparts)
  (if (atom thmparts)
      nil
    (if (eq (flag-from-thmpart (car thmparts)) flag)
        (car thmparts)
      (assoc-flag-in-thmparts flag (cdr thmparts)))))







(defun pair-up-cases-with-thmparts (alist thmparts skip-ok)
  ;; Each thmpart is an thing like
  ;; _either_ (flag <thm-body> :name ... :rule-classes ... :doc ...)
  ;;;    (for backwards compatibility)
  ;; _or_  (defthm <thmname> <thm-body> :flag ... :rule-classes ... :doc ...)

  (if (consp alist)
      (let* ((flag   (cdar alist))
             (lookup (assoc-flag-in-thmparts flag thmparts)))
        (if (and (not lookup) (not skip-ok))
            (er hard 'pair-up-cases-with-thmparts
                "Expected there to be a case for the flag ~s0.~%" flag)
          (let ((body (cond ((not lookup) t)
                            ((eq (car lookup) 'defthm)
                             ;; (defthm name body ...)
                             (caddr lookup))
                            (t ;; (flag body ...)
                             (cadr lookup)))))
            (if (consp (cdr alist))
                (cons `(,flag ,body)
                      (pair-up-cases-with-thmparts (cdr alist) thmparts skip-ok))
              (list `(otherwise ,body))))))
    (er hard 'pair-up-cases-with-thmparts
        "Never get here.")))


(defun pair-up-cases-with-hints (alist thmparts skip-ok)
  ;; Each thmpart is an thing like
  ;; _either_ (flag <thm-body> :name ... :rule-classes ... :doc ...)
  ;;;    (for backwards compatibility)
  ;; _or_  (defthm <thmname> <thm-body> :flag ... :rule-classes ... :doc ...)

  (if (consp alist)
      (let* ((flag   (cdar alist))
             (lookup (assoc-flag-in-thmparts flag thmparts)))
        (if (not lookup)
            (if skip-ok
                (cons (cons flag nil)
                      (pair-up-cases-with-hints (cdr alist) thmparts skip-ok))
              (er hard 'pair-up-cases-with-hints
                  "Expected there to be a case for the flag ~s0.~%" flag))
          (let ((hints (extract-keyword-from-args :hints lookup)))
            (cons (cons flag hints)
                  (pair-up-cases-with-hints (cdr alist) thmparts skip-ok)))))
    nil))

(defun flag-thm-entry-thmname (explicit-name flag entry)
  (if (eq (car entry) 'defthm)
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
              "~
Expected an explicit name for each theorem, since no general name was
given.  The following theorem does not have a name: ~x0~%" entry)))))


(defun make-defthm-macro-fn-aux (lemma-name explicit-name flag-var alist thmparts)
  ;; We have just proven the lemma and it's time to instantiate it to
  ;; give us each thm.
  (if (consp alist)
      (let* ((flag (cdar alist))
             (lookup (assoc-flag-in-thmparts flag thmparts)))
        (if (or (not lookup)
                (extract-keyword-from-args :skip (cddr lookup)))
            (make-defthm-macro-fn-aux
             lemma-name explicit-name flag-var (cdr alist) thmparts)
          ;; Not checking for lookup, already did it when we did cases.
          (let ((this-name
                 (flag-thm-entry-thmname explicit-name flag lookup))
                (body (if (eq (car lookup) 'defthm)
                          (caddr lookup)
                        (cadr lookup)))
                (rule-classes (let ((mem (member :rule-classes (cddr lookup))))
                                (if mem (cadr mem) :rewrite)))
                (doc          (extract-keyword-from-args :doc (cddr lookup))))
            (cons `(defthm ,this-name
                     ,body
                     :rule-classes ,rule-classes
                     :doc ,doc
                     :hints(("Goal"
                             :in-theory (theory 'minimal-theory)
                             :use ((:instance ,lemma-name (,flag-var ',flag))))))
                  (make-defthm-macro-fn-aux
                   lemma-name explicit-name flag-var (cdr alist) thmparts)))))
    nil))



(defun make-defthm-macro-fn (args alist flag-var flag-fncall)
  (let* ((explicit-name (and (symbolp (car args)) (car args)))
         (args (if explicit-name (cdr args) args))
         (thmparts (throw-away-keyword-parts args))
         (name (if explicit-name
                   (intern-in-package-of-symbol
                    (concatenate 'string "FLAG-LEMMA-FOR-"
                                 (symbol-name explicit-name))
                    explicit-name)
                 (intern-in-package-of-symbol
                  (concatenate 'string "FLAG-LEMMA-FOR-"
                               (symbol-name (car flag-fncall)))
                  (car flag-fncall))))
         (instructions (extract-keyword-from-args :instructions args))
         (user-hints (extract-keyword-from-args :hints args))
         (skip-ok (extract-keyword-from-args :skip-others args))
         (hints (and (not instructions)
                     (append
                      (if (and (consp (car user-hints))
                               (stringp (caar user-hints))
                               (equal (string-upcase (caar user-hints))
                                      "GOAL"))
                          ;; First hint is for goal.
                          (if (extract-keyword-from-args :induct (car user-hints))
                              ;; Explicit induct hint is provided; do not override.
                              user-hints
                            ;; Provide our induct hint in addition to the hints
                            ;; provided in goal.
                            (cons `("Goal" :induct ,flag-fncall
                                    . ,(cdar user-hints))
                                  (cdr user-hints)))
                        ;; No goal hint; cons our induction hint onto the rest.
                        (cons `("Goal" :induct ,flag-fncall)
                              user-hints))
                      (list
                       `(flag-hint-cases
                         ,flag-var
                         . ,(pair-up-cases-with-hints alist thmparts skip-ok)))))))

    `(progn
       (encapsulate
        ()
        (local (defthm ,name
                 (case ,flag-var . ,(pair-up-cases-with-thmparts
                                     alist thmparts skip-ok))
                 :rule-classes nil
                 :hints ,hints
                 :instructions ,instructions
                 :otf-flg ,(extract-keyword-from-args :otf-flg args)))

        . ,(make-defthm-macro-fn-aux name explicit-name flag-var alist thmparts))
       (value-triple ',name))))


(defun make-defthm-macro (real-macro-name alist flag-var flag-fncall)
  `(defmacro ,real-macro-name (&rest args) ;; was (name &rest args)
     (make-defthm-macro-fn args ',alist ',flag-var ',flag-fncall)))

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



; LEGACY HINT.  We found cases where EXPAND-CALLS-COMPUTED-HINT was too
; aggressive and expanded 'inner' terms that shouldn't have been expanded.
; We now FLAG-EXPAND-COMPUTED-HINT instead, which is more targetted for
; exactly the expansions we want.

; BOZO we are leaving expand-calls-computed-hint here only because Sol
; uses it in other places; we may wish to clean this up eventually and
; move it to some more appropriate file.

;; Collects up any calls of functions listed in FNS that are present in x.
(mutual-recursion
 (defun find-calls-of-fns-term (x fns acc)
   (cond ((or (atom x) (eq (car x) 'quote)) acc)
         ((member-eq (car x) fns)
          (find-calls-of-fns-list (cdr x) fns (cons x acc)))
         (t
          (find-calls-of-fns-list (cdr x) fns acc))))
 (defun find-calls-of-fns-list (x fns acc)
   (if (atom x)
       acc
     (find-calls-of-fns-term
      (car x) fns
      (find-calls-of-fns-list (cdr x) fns acc)))))

;; Gives an expand hint for any function in FNS present in the
;; conclusion of the clause.
(defun expand-calls-computed-hint (clause fns)
 (let ((expand-list (find-calls-of-fns-term (car (last clause)) fns nil)))
   `(:expand ,expand-list)))



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
                   `(:expand ,expands))))
           (&
            nil)))))

(defun flag-table-events (alist entry)
  (if (atom alist)
      nil
    (cons `(table flag-fns ',(caar alist) ',entry)
          (flag-table-events (cdr alist) entry))))

(defun make-flag-fn (flag-fn-name clique-member-name flag-var flag-mapping hints
                                  defthm-macro-name local world)
  (let* ((flag-var (or flag-var
                       (intern-in-package-of-symbol "FLAG" flag-fn-name)))
         (alist (or flag-mapping
                    (pairlis$ (get-clique-members clique-member-name world)
                              (get-clique-members clique-member-name world))))
         (defthm-macro-name (or defthm-macro-name
                                (intern-in-package-of-symbol
                                 (concatenate 'string "DEFTHM-" (symbol-name flag-fn-name))
                                 flag-fn-name)))
         (equiv-thm-name (intern-in-package-of-symbol
                          (concatenate 'string (symbol-name flag-fn-name) "-EQUIVALENCES")
                          flag-fn-name))
         (formals        (merge-formals alist world)))
    `(,@(if local '(progn) '(encapsulate nil))
      ;; use encapsulate instead of progn so set-ignore-ok is local to this
      (logic)
      ,@(and (not local) '((set-ignore-ok t))) ;; can't wrap this in local --- fubar!

      (,(if local 'local 'id)
       ,(make-flag-body flag-fn-name flag-var alist hints world))
      ,(make-defthm-macro defthm-macro-name alist flag-var
                          `(,flag-fn-name ,flag-var . ,formals))

      (,(if local 'local 'id)
       (with-output
        :off (prove event) ;; hides induction scheme, too
        (encapsulate nil
          (logic)
          (defthm ,equiv-thm-name
            (equal (,flag-fn-name ,flag-var . ,formals)
                   (case ,flag-var
                     ,@(make-cases-for-equiv alist world)))
            :hints (("Goal"
                     :induct
                     (,flag-fn-name ,flag-var . ,formals)
                     :in-theory
                     (set-difference-theories
                      (union-theories (theory 'minimal-theory)
                                      '((:induction ,flag-fn-name)
                                        (:rewrite expand-all-hides)))
                      '(;; Jared found mv-nth to be slowing down a couple of flag
                        ;; function admissions.  Take it out of the minimal theory.
                        (:definition mv-nth)
                        ;; Jared found a case where "linear" forced some goals
                        ;; from an equality, which were unprovable.  So, turn
                        ;; off forcing.
                        (:executable-counterpart force))))
                    (flag-expand-computed-hint stable-under-simplificationp
                                               ACL2::clause
                                               ',(cons flag-fn-name
                                                       (strip-cars alist))))))))

      (progn . ,(flag-table-events alist `(,flag-fn-name
                                           ,alist
                                           ,defthm-macro-name
                                           ,equiv-thm-name)))
      (,(if local 'local 'id)
       (in-theory (disable (:definition ,flag-fn-name)))))))

(defmacro make-flag (flag-fn-name clique-member-name
                     &key
                     flag-var
                     flag-mapping
                     hints
                     defthm-macro-name
                     local)
  `(make-event (make-flag-fn ',flag-fn-name
                             ',clique-member-name
                             ',flag-var
                             ',flag-mapping
                             ',hints
                             ',defthm-macro-name
                             ',local
                             (w state))))



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





(logic) ;; so local events aren't skipped

#!ACL2
(local

; A couple tests to make sure things are working.

 (encapsulate
  ()

  (FLAG::make-flag flag-pseudo-termp
                   pseudo-termp
                   :flag-var flag
                   :flag-mapping ((pseudo-termp . term)
                                  (pseudo-term-listp . list))
                   ;; :hints {for the measure theorem}
                   :defthm-macro-name defthm-pseudo-termp
                   )

; This introduces (flag-pseudo-termp flag x lst)
; Theorems equating it with pseudo-termp and pseudo-term-listp
; And the macro shown below.

  (in-theory (disable (:type-prescription pseudo-termp)
                      (:type-prescription pseudo-term-listp)))

  ;; A few syntactic variations on defining the same theorems:
  (encapsulate
   nil
   (local (defthm-pseudo-termp type-of-pseudo-termp
            (term (booleanp (pseudo-termp x))
                  :rule-classes :rewrite
                  :doc nil)
            (list (booleanp (pseudo-term-listp lst))))))

  (encapsulate
   nil
   (local (defthm-pseudo-termp type-of-pseudo-termp2
            (defthm booleanp-of-pseudo-termp
              (booleanp (pseudo-termp x))
              :rule-classes :rewrite
              :doc nil
              :flag term)
            :skip-others t)))


  (encapsulate
   nil
   (local (in-theory (disable pseudo-termp pseudo-term-listp)))
   (local (defthm-pseudo-termp type-of-pseudo-termp
            (term (booleanp (pseudo-termp x))
                  :hints ('(:expand ((pseudo-termp x))))
                  :rule-classes :rewrite
                  :doc nil)
            (list (booleanp (pseudo-term-listp lst))
                  :hints ('(:expand ((pseudo-term-listp lst))))))))

  (encapsulate
   nil
   (local (defthm-pseudo-termp
            (term (booleanp (pseudo-termp x))
                  :rule-classes :rewrite
                  :doc nil
                  :name type-of-pseudo-termp)
            (list (booleanp (pseudo-term-listp lst))
                  :skip t))))

  (encapsulate
   nil
   (local (defthm-pseudo-termp
            (defthm type-of-pseudo-termp
              (booleanp (pseudo-termp x))
              :rule-classes :rewrite
              :doc nil
              :flag term)
            (defthm type-of-pseudo-term-listp
              (booleanp (pseudo-term-listp lst))
              :flag list
              :skip t))))

  (encapsulate
   nil
   (local (defthm-pseudo-termp
            (defthm type-of-pseudo-termp
              (booleanp (pseudo-termp x))
              :rule-classes :rewrite
              :doc nil
              :flag term)
            (list
              (booleanp (pseudo-term-listp lst))
              :skip t))))



  (defstobj term-bucket
    (terms))

  (mutual-recursion

   (defun terms-into-bucket (x term-bucket)
     ;; Returns (mv number of terms added, term-bucket)
     (declare (xargs :stobjs (term-bucket)
                     :verify-guards nil))
     (cond ((or (atom x)
                (quotep x))
            (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
              (mv 1 term-bucket)))
           (t
            (mv-let (numterms term-bucket)
                    (terms-into-bucket-list (cdr x) term-bucket)
                    (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
                      (mv (+ numterms 1) term-bucket))))))

   (defun terms-into-bucket-list (x term-bucket)
     (declare (xargs :stobjs (term-bucket)))
     (if (atom x)
         (mv 0 term-bucket)
       (mv-let (num-car term-bucket)
               (terms-into-bucket (car x) term-bucket)
               (mv-let (num-cdr term-bucket)
                       (terms-into-bucket-list (cdr x) term-bucket)
                       (mv (+ num-car num-cdr) term-bucket))))))

  (FLAG::make-flag flag-terms-into-bucket
                   terms-into-bucket)


  ;; previously this didn't work, now we set-ignore-ok to fix it.
  (encapsulate
   ()
   (set-ignore-ok t)
   (mutual-recursion
    (defun ignore-test-f (x)
      (if (consp x)
          (let ((y (+ x 1)))
            (ignore-test-g (cdr x)))
        nil))
    (defun ignore-test-g (x)
      (if (consp x)
          (ignore-test-f (cdr x))
        nil))))

  (FLAG::make-flag flag-ignore-test
                   ignore-test-f)

  ))
