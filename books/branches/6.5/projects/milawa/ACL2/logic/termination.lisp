; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "substitute-term")
(include-book "negate-term")
(include-book "pequal-list")
(include-book "disjoin-formulas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Termination of Function Definitions.
;;
;; Milawa permits a definitional extension principle which allows new functions
;; to be introduced as axioms in the logic.  If we are not careful, this could
;; lead to inconsistency, e.g., one should not be permitted to define (f x) as
;; (not (f x)), as this would be inconsistent.  So, we will allow definition to
;; be admitted only when they can be shown to be terminating for all inputs.
;;
;; To keep this simple, Milawa does not support mutually recursive functions.
;; So, suppose we are trying to admit a recursive function, (f x1 ... xn).
;; Our goal is to find a term, m, called the "measure" of f, which satisfies
;; the following obligations:
;;
;;   1. The free variables of m are a subset of { x1 ... xn },
;;
;;   2. We can prove (ordp m), and
;;
;;   3. We can prove (ord< m/[xi<-ai] m) whenever (f a1 ... an) is called
;;      recursively in the body of f.



;; Example.  The function "len" is defined as follows.
;;
;;  (len x) = (if (consp x) (+ 1 (len (cdr x))) 0)
;;
;; To see that m = (rank x) is sufficient, we need to check:
;;
;;   1. The free variables of (cdr x) are a subset of { x },
;;
;;   2. We can prove (ordp (rank x)), and
;;
;;   3. We can prove (consp x) --> (ord< (rank (cdr x)) (rank x)) = t.
;;
;; We are allowed to assume (consp x) != nil in the #3 above, because the
;; recursive call is only made in the "true" branch of the if-expression.



;; These Obligations are Sufficient.
;;
;; Returning now to the general case, let us show these conditions are
;; sufficient to ensure that every all of (f x1 ... xn) terminates.
;;
;; Lemma.  Suppose the above conditions hold and that all previously-defined
;; functions are total.  If (f z1 ... zn) does not terminate, then there
;; exists z1' ... zn' such that (f z1' ... zn') also does not terminate, with
;; (ord< m/[xi<-zi'] m/[xi<-zi]).
;;
;; Proof.  Assume (f z1 ... zn) does not terminate.  Since all the previously
;; defined functions terminate, we must not be in a base case.  Indeed, there
;; must be some recursive call, (f a1 ... an), which itself does not terminate.
;;
;; Since property #3 holds, we know (ord< m/[xi<-ai] m).  Instantiating this
;; with [xi<-zi], we see that: (ord< (m/[xi<-ai])/[xi<-zi] m/[xi<-zi]).  So,
;; letting zi'=ai/zi, we are done.
;;
;; Q.E.D.
;;
;; Theorem.  Suppose the above conditions hold, and all the previously
;; defined functions terminate.  Then, f terminates as well.
;;
;; Proof by contradiction.  If (f z1 ... zn) does not terminate, then by our
;; lemma we can find inputs z1' ... zn' such that (f z1' ... zn') does not
;; terminate.  Continuing like this, we can find inputs z1'' ... zn'' so that
;; (f z1'' ... zn'') does not terminate, and so on forever to infinity.
;;
;; Now, by condition #2, we know that each of m/[xi<-zi], m/[xi<-zi'],
;; m/[xi<-zi''], and so on are ordinals.  Furthermore, by our lemma we know
;; that m/[xi<-zi] > m/[xi<-zi'] > m/[xi<-zi''], ..., where > denotes ordinal
;; greater-than.
;;
;; Hence, we have constructed an infinite, strictly decreasing sequence of
;; ordinals, which contradicts the well-foundedness of the ordinals.  This
;; cannot be, so (f z1 ... zn) must terminate for all choices of inputs.
;;
;; Q.E.D.



;; Computing Termination Obligations with Call Maps.
;;
;; Obligation #1 is straightforward to check, and Obligation #2 is easy to
;; generate.  But the conditions for Obligation #3 take some work to generate.
;; We use a structure called a Call Map to do this.
;;
;; The Call Map associates each recursive call in the function's body with a
;; list of all the terms ruling it.  Once we have such a map, we can easily
;; generate the measure conditions we need to prove.  The call map is just a
;; regular map, i.e., a list of (key . value) pairs.
;;
;; The "key" of each entry is a list of the actuals for this function call,
;; e.g., for the call (len (cdr x)) in our example, the key would be the
;; singleton list containing (cdr x).
;;
;; The "value" of each entry is a list of terms which are the rulers of this
;; recursive call.  For example, it would be the singleton list containing
;; (consp x) in our "len" example.

(defmap :map (logic.callmapp x)
        :key (logic.term-listp x)
        :val (logic.term-listp x)
        :key-list (logic.term-list-listp x)
        :val-list (logic.term-list-listp x)
        :val-of-nil t)

(defthm forcing-logic.callmapp-of-cons-onto-ranges
  (implies (force (and (logic.callmapp x)
                       (logic.termp a)))
           (equal (logic.callmapp (cons-onto-ranges a x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defmap :map (logic.callmap-atblp x atbl)
        :key (logic.term-list-atblp x atbl)
        :val (logic.term-list-atblp x atbl)
        :key-list (logic.term-list-list-atblp x atbl)
        :val-list (logic.term-list-list-atblp x atbl)
        :val-of-nil t
        :guard (and (logic.callmapp x)
                    (logic.arity-tablep atbl)))

(defthm forcing-logic.callmap-atblp-of-cons-onto-ranges
  (implies (force (and (logic.callmap-atblp x atbl)
                       (logic.term-atblp a atbl)))
           (equal (logic.callmap-atblp (cons-onto-ranges a x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defund logic.substitute-callmap (x sigma)
  ;; X is a callmap and sigma is a substitution list.  We apply sigma to every
  ;; actual and every ruler throughout the entire map.
  (declare (xargs :guard (and (logic.callmapp x)
                              (logic.sigmap sigma))))
  (if (consp x)
      (let ((actuals (car (car x)))
            (rulers  (cdr (car x))))
        (cons (cons (logic.substitute-list actuals sigma)
                    (logic.substitute-list rulers sigma))
              (logic.substitute-callmap (cdr x) sigma)))
    nil))

(defthm logic.substitute-callmap-when-not-consp
  (implies (not (consp x))
           (equal (logic.substitute-callmap x sigma)
                  nil))
  :hints(("Goal" :in-theory (enable logic.substitute-callmap))))

(defthm logic.substitute-callmap-of-cons
  (equal (logic.substitute-callmap (cons a x) sigma)
         (cons (cons (logic.substitute-list (car a) sigma)
                     (logic.substitute-list (cdr a) sigma))
               (logic.substitute-callmap x sigma)))
  :hints(("Goal" :in-theory (enable logic.substitute-callmap))))

(defthm true-listp-of-logic.substitute-callmap
  (equal (true-listp (logic.substitute-callmap x sigma))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-logic.substitute-callmap
  (equal (len (logic.substitute-callmap x sigma))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-callmap-of-list-fix
  (equal (logic.substitute-callmap (list-fix x) sigma)
         (logic.substitute-callmap x sigma))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-callmap-of-app
  (equal (logic.substitute-callmap (app x y) sigma)
         (app (logic.substitute-callmap x sigma)
              (logic.substitute-callmap y sigma)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm domain-of-logic.substitute-callmap
  (equal (domain (logic.substitute-callmap x sigma))
         (logic.substitute-list-list (domain x) sigma))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm range-of-logic.substitute-callmap
  (equal (range (logic.substitute-callmap x sigma))
         (logic.substitute-list-list (range x) sigma))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm mapp-of-logic.substitute-callmapp
  (equal (mapp (logic.substitute-callmap x sigma))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.callmapp-of-logic.substitute-callmapp
  (implies (force (and (logic.callmapp x)
                       (logic.sigmap sigma)))
           (equal (logic.callmapp (logic.substitute-callmap x sigma))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.callmap-atblp-of-logic.substitute-callmapp
  (implies (force (and (logic.callmap-atblp x atbl)
                       (logic.sigma-atblp sigma atbl)))
           (equal (logic.callmap-atblp (logic.substitute-callmap x sigma) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




;; Building Call Maps.
;;
;; We construct the call map for a function using the mutually-recursive
;; logic.flag-callmap function, below.
;;
;; We work inside-out.  Each time we encounter a recursive call of f, we add
;; its actuals to the callmap, associating an empty set of rulers with this
;; call.  As our recursion unwinds, we add in the appropriate rulers from any
;; "if" expressions we pass by.
;;
;; We also considered using an outside-in approach, i.e., where we keep a list
;; of rulers we have seen so far as we descend the term.  But this did not seem
;; to work well in the lambda case, where we need to account for the new
;; bindings in the body of the lambda.

(defun logic.flag-callmap (flag f x)
  ;; We build a callmap for the function f in the term(-list) x.
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (logic.function-namep f))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x)
             ;; There are no calls of f in a constant
             nil)
            ((logic.variablep x)
             ;; There are no calls of f in a variable
             nil)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (cond ((and (equal name 'if)
                           (equal (len args) 3))
                      ;; Special handling for (if test true else):
                      ;;  -- We collect all the calls of f in test, leaving their rulers intact
                      ;;  -- We collect all the calls of f in the true branch, adding test as an extra ruler to each such call
                      ;;  -- We collect all the calls of f in the else branch, adding (not test) as an extra ruler to each such call
                      (let ((test-calls (logic.flag-callmap 'term f (first args)))
                            (true-calls (cons-onto-ranges (first args)
                                                          (logic.flag-callmap 'term f (second args))))
                            (else-calls (cons-onto-ranges (logic.function 'not (list (first args)))
                                                          (logic.flag-callmap 'term f (third args)))))
                        (app test-calls (app true-calls else-calls))))
                     ((equal name f)
                      ;; Special handling for (f x1 ... xn):
                      ;;  -- We collect this call of f
                      ;;  -- We collect all the calls of f in x1...xn
                      ;; We leave the rulers of this-call empty; they are added in as the recursion unwinds.
                      (let ((this-call   (cons args nil))
                            (child-calls (logic.flag-callmap 'list f args)))
                        (cons this-call child-calls)))
                     (t
                      ;; Generic handling for other functions:
                      ;;  -- We just collect all the calls of f in the arguments
                      (logic.flag-callmap 'list f args)))))
            ((logic.lambdap x)
             (let ((formals (logic.lambda-formals x))
                   (body    (logic.lambda-body x))
                   (actuals (logic.lambda-actuals x)))
               ;; Handling of Lambdas.
               ;;  -- We collect all the calls of f in the lambda's actuals, then
               ;;  -- We collect all the calls of f in the lambda's body and correct them to remove the "temporary formals"
               ;; Why do we separately collect the actuals?
               ;;  -- Some actuals might not make it into the body, e.g., (f x) = (let ((temp (f x))) (+ x 1)),
               ;;     so we want to make sure we collect them too.  (They don't affect soundness, but we want our
               ;;     computations to terminate.)
               (let ((actuals-calls (logic.flag-callmap 'list f actuals))
                     (body-calls    (logic.flag-callmap 'term f body))
                     (sigma         (pair-lists formals actuals)))
                 (app actuals-calls
                      (logic.substitute-callmap body-calls sigma))))))
    (if (consp x)
        (app (logic.flag-callmap 'term f (car x))
             (logic.flag-callmap 'list f (cdr x)))
       nil)))

(definlined logic.callmap (f x)
  (declare (xargs :guard (and (logic.function-namep f)
                              (logic.termp x))
                  :verify-guards nil))
  (logic.flag-callmap 'term f x))

(definlined logic.callmap-list (f x)
  (declare (xargs :guard (and (logic.function-namep f)
                              (logic.term-listp x))
                  :verify-guards nil))
  (logic.flag-callmap 'list f x))

(defthmd definition-of-logic.callmap
  (equal (logic.callmap f x)
         (cond ((logic.constantp x) nil)
               ((logic.variablep x) nil)
               ((logic.functionp x)
                (let ((name (logic.function-name x))
                      (args (logic.function-args x)))
                  (cond ((and (equal name 'if)
                              (equal (len args) 3))
                         (let ((test-calls (logic.callmap f (first args)))
                               (true-calls (cons-onto-ranges (first args)
                                                             (logic.callmap f (second args))))
                               (else-calls (cons-onto-ranges (logic.function 'not (list (first args)))
                                                             (logic.callmap f (third args)))))
                           (app test-calls (app true-calls else-calls))))
                        ((equal name f)
                         (let ((this-call   (cons args nil))
                               (child-calls (logic.callmap-list f args)))
                           (cons this-call child-calls)))
                        (t
                         (logic.callmap-list f args)))))
               ((logic.lambdap x)
                (let ((formals (logic.lambda-formals x))
                      (body    (logic.lambda-body x))
                      (actuals (logic.lambda-actuals x)))
                  (let ((actuals-calls (logic.callmap-list f actuals))
                        (body-calls    (logic.callmap f body))
                        (sigma         (pair-lists formals actuals)))
                    (app actuals-calls
                         (logic.substitute-callmap body-calls sigma)))))))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logic.callmap logic.callmap-list)
          :expand (logic.flag-callmap 'term f x))))

(defthmd definition-of-logic.callmap-list
  (equal (logic.callmap-list f x)
         (if (consp x)
             (app (logic.callmap f (car x))
                  (logic.callmap-list f (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logic.callmap logic.callmap-list)
          :expand (logic.flag-callmap 'list f x))))

(defthm logic.flag-callmap-of-term
  (equal (logic.flag-callmap 'term f x)
         (logic.callmap f x))
  :hints(("Goal" :in-theory (enable logic.callmap))))

(defthm logic.flag-callmap-of-term-list
  (equal (logic.flag-callmap 'list f x)
         (logic.callmap-list f x))
  :hints(("Goal" :in-theory (enable logic.callmap-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.callmap))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.callmap-list))))




(defthm mapp-of-rev
  ;; BOZO move this to utilities.lisp
  (equal (mapp (rev x))
         (mapp x))
  :hints(("Goal" :induct (cdr-induction x))))




;; Well-Formedness of Logic.Flag-Callmap
;;
;; We prove that logic.flag-callmap always produces a true-listp, a mapp, a
;; callmapp, and a callmap-atblp.

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'term)
              (true-listp (logic.callmap f x))
            (true-listp (logic.callmap-list f x)))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.flag-callmap flag f x)
                  :expand ((:free (f) (logic.callmap f x))
                           (:free (f) (logic.callmap-list f x)))))))

 (defthm true-listp-of-logic.callmap
   (equal (true-listp (logic.callmap f x))
          t)
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm true-listp-of-logic.callmap-list
   (equal (true-listp (logic.callmap-list f x))
          t)
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'term)
              (mapp (logic.callmap f x))
            (mapp (logic.callmap-list f x)))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.flag-callmap flag f x)
                  :expand ((:free (f) (logic.callmap f x))
                           (:free (f) (logic.callmap-list f x)))))))

 (defthm mapp-of-logic.callmap
   (equal (mapp (logic.callmap f x))
          t)
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm mapp-of-logic.callmap-list
   (equal (mapp (logic.callmap-list f x))
          t)
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'term)
              (implies (logic.termp x)
                       (logic.callmapp (logic.callmap f x)))
            (implies (logic.term-listp x)
                     (logic.callmapp (logic.callmap-list f x))))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.flag-callmap flag f x)
                  :expand ((:free (f) (logic.callmap f x))
                           (:free (f) (logic.callmap-list f x)))))))

 (defthm forcing-logic.callmapp-of-logic.callmap
   (implies (force (logic.termp x))
            (equal (logic.callmapp (logic.callmap f x))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm forcing-logic.callmapp-of-logic.callmap-list
   (implies (force (logic.term-listp x))
            (equal (logic.callmapp (logic.callmap-list f x))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'term)
              (implies (and (logic.arity-tablep atbl)
                            (logic.termp x)
                            (logic.term-atblp x atbl)
                            (equal (cdr (lookup 'not atbl)) 1))
                       (logic.callmap-atblp (logic.callmap f x) atbl))
            (implies (and (logic.arity-tablep atbl)
                          (logic.term-listp x)
                          (logic.term-list-atblp x atbl)
                          (equal (cdr (lookup 'not atbl)) 1))
                     (logic.callmap-atblp (logic.callmap-list f x) atbl)))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.flag-callmap flag f x)
                  :expand ((:free (f) (logic.callmap f x))
                           (:free (f) (logic.callmap-list f x)))))))

 (defthm forcing-logic.callmap-atblp-of-logic.callmap
   (implies (force (and (logic.arity-tablep atbl)
                        (logic.termp x)
                        (logic.term-atblp x atbl)
                        (equal (cdr (lookup 'not atbl)) 1)))
            (equal (logic.callmap-atblp (logic.callmap f x) atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm forcing-logic.callmap-atblp-of-logic.callmap-list
   (implies (force (and (logic.arity-tablep atbl)
                        (logic.term-listp x)
                        (logic.term-list-atblp x atbl)
                        (equal (cdr (lookup 'not atbl)) 1)))
            (equal (logic.callmap-atblp (logic.callmap-list f x) atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(verify-guards logic.flag-callmap)
(verify-guards logic.callmap)
(verify-guards logic.callmap-list)




;; Theorem: the actuals produced by logic.flag-callmap always have the same arity,
;; given that the term was well-formed to begin with.

(encapsulate
 ()
 (local (in-theory (e/d (domain-of-rev)
                        (rev-of-domain))))

 (local (defthm lemma
          (if (equal flag 'term)
              (implies (and (logic.arity-tablep atbl)
                            (logic.termp x)
                            (logic.term-atblp x atbl))
                       (all-equalp (cdr (lookup f atbl))
                                   (strip-lens (domain (logic.callmap f x)))))
            (implies (and (logic.arity-tablep atbl)
                          (logic.term-listp x)
                          (logic.term-list-atblp x atbl))
                     (all-equalp (cdr (lookup f atbl))
                                 (strip-lens (domain (logic.callmap-list f x))))))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.flag-callmap flag f x)
                  :expand ((:free (f) (logic.callmap f x))
                           (:free (f) (logic.callmap-list f x)))))))

 (defthm forcing-all-equalp-of-lengths-of-domain-of-callmap
   (implies (force (and (logic.arity-tablep atbl)
                        (logic.termp x)
                        (logic.term-atblp x atbl)))
            (equal (all-equalp (cdr (lookup f atbl))
                               (strip-lens (domain (logic.callmap f x))))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))

 (defthm forcing-all-equalp-of-lengths-of-domain-of-callmap-list
   (implies (force (and (logic.arity-tablep atbl)
                        (logic.term-listp x)
                        (logic.term-list-atblp x atbl)))
            (equal (all-equalp (cdr (lookup f atbl))
                               (strip-lens (domain (logic.callmap-list f x))))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))




(defund logic.progress-obligation (measure formals actuals rulers)
  ;; We create the clause for a single callmap entry's obligation.
  ;;  -- Measure is the measure of the function we want to admit
  ;;  -- Formals are the formals of the function we want to admit
  ;;  -- Actuals are the arguments to the recursive call we found
  ;;  -- Rulers are the terms which rule this recursive call
  ;; We need to show the measure decreases for this recursive call. That is,
  ;;    rulers --> (ord< measure/[formals<-actuals] measure)
  ;; Suppose rulers are (r1 ... rn).  Then our obligation is the clause:
  ;;    (not r1) v ... v (not rn) v (ord< measure/[formals<-actuals] measure)
  (declare (xargs :guard (and (logic.termp measure)
                              (logic.variable-listp formals)
                              (logic.term-listp actuals)
                              (logic.term-listp rulers)
                              (equal (len actuals) (len formals))
                              )))
  (let* ((sigma    (pair-lists formals actuals))
         (m/sigma  (logic.substitute measure sigma))
         (ord-term (logic.function 'ord< (list m/sigma measure))))
    (logic.disjoin-formulas
     (cons (logic.pequal ord-term ''t)
           (logic.pequal-list rulers (repeat ''nil (len rulers)))))))

(defthm forcing-logic.formulap-of-logic.progress-obligation
  (implies (force (and (logic.termp measure)
                       (logic.variable-listp formals)
                       (logic.term-listp actuals)
                       (logic.term-listp rulers)
                       (equal (len formals) (len actuals))))
           (equal (logic.formulap (logic.progress-obligation measure formals actuals rulers))
                  t))
  :hints(("Goal" :in-theory (enable logic.progress-obligation))))



(defund logic.progress-obligations (measure formals callmap)
  ;; We create the clauses for all the obligations in this callmap.
  ;;  -- Measure is the measure of the function we want to admit
  ;;  -- Formals are the formals of the function we want to admit
  (declare (xargs :guard (and (logic.termp measure)
                              (logic.variable-listp formals)
                              (logic.callmapp callmap)
                              (all-equalp (len formals) (strip-lens (domain callmap))))))
  (if (consp callmap)
      (let* ((entry   (car callmap))
             (actuals (car entry))
             (rulers  (cdr entry)))
        (cons (logic.progress-obligation measure formals actuals rulers)
              (logic.progress-obligations measure formals (cdr callmap))))
    nil))

(defthm forcing-logic.formula-list-of-logic.progress-obligations
  (implies (force (and (logic.termp measure)
                       (logic.variable-listp formals)
                       (logic.callmapp callmap)
                       (all-equalp (len formals) (strip-lens (domain callmap)))))
           (equal (logic.formula-listp (logic.progress-obligations measure formals callmap))
                  t))
  :hints(("Goal" :in-theory (enable logic.progress-obligations))))



;; BOZO Horrible --- we can verify the guards of this function if we assume
;; that body and measure are well-formed w.r.t. an arity table, atbl.  But the
;; atbl isn't used for anything else, so that sucks and is hard to explain when
;; we write up the core Milawa proof checker.  Hence, we drop the atbl and use
;; ACL2's EC-CALL mechanism to get verified guards here.

(defund logic.termination-obligations (name formals body measure)
   ;; We create the clauses for obligations #2 and #3 for a new definition.
   ;;  -- We take the Name, Formals, Measure, and Body of the new definition
   (declare (xargs :guard (and (logic.function-namep name)
                               (logic.variable-listp formals)
                               (logic.termp body)
                               (logic.termp measure)
                               ;(logic.arity-tablep atbl)
                               ;(logic.term-atblp body atbl)
                               ;(logic.term-atblp measure atbl)
                               (uniquep formals)
                               (subsetp (logic.term-vars body) formals)
                               (subsetp (logic.term-vars measure) formals)
                               ;(equal (cdr (lookup name atbl)) (len formals))
                               )))
   (let ((callmap (logic.callmap name body)))
     (if callmap
         (cons (logic.pequal (logic.function 'ordp (list measure)) ''t)
               (ACL2::ec-call
                (logic.progress-obligations measure formals callmap)))
       nil)))

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthm forcing-logic.formula-listp-of-logic.termination-obligations
   (implies (force (and (logic.function-namep name)
                        (logic.variable-listp formals)
                        (logic.termp body)
                        (logic.termp measure)
                        (logic.arity-tablep atbl)
                        (uniquep formals)
                        (subsetp (logic.term-vars body) formals)
                        (subsetp (logic.term-vars measure) formals)
                        (logic.term-atblp body atbl)
                        (logic.term-atblp measure atbl)
                        (equal (cdr (lookup name atbl)) (len formals))))
            (equal (logic.formula-listp (logic.termination-obligations name formals body measure))
                   t))
   :hints(("Goal" :in-theory (enable logic.termination-obligations)))))

