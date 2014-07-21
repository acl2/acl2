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
(include-book "evaluator")
(include-book "../build/lambda")
(include-book "../build/equal")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; We now work to prove that the generic-evaluator is sound.  That is, if all
;; of the guards are satisfied (we have a ground term, we have definitional
;; axioms for each definition in the database, etc.) and the generic-evaluator
;; does not fail (i.e., the "n" used is sufficient, etc.), then it follows that
;; the input term is provably equal to the value produced by the generic
;; evaluator.
;;
;; Our proof strategy should not be surprising if you have read through the
;; previous extensions, such as tautology checking.  We will write a new
;; function, generic-evaluator-bldr (and its mutually recursive counterpart)
;; which will build a proof that an input term is equal to its value whenever
;; generic-evaluator is able to evaluate it.

(defderiv eval-lemma-1-bldr
  :derive (= (if (? a) (? b) (? c)) (? b2))
  :from   ((proof x (= (? a) (? a2)))
           (proof y (= (? b) (? b2)))
           (term c (? c)))
  :where  ((logic.constantp (@term (? a2)))
           (iff (logic.unquote (@term (? a2))) t))
  :proof (@derive
          ((!= (? a2) nil)                                     (build.not-pequal-constants (@term (? a2)) (@term nil)))
          ((= (? a) (? a2))                                    (@given x))
          ((!= (? a) nil)                                      (build.substitute-into-not-pequal @-- @-)     *1)
          ((v (= x nil) (= (if x y z) y))                      (build.axiom (axiom-if-when-not-nil)))
          ((v (= (? a) nil) (= (if (? a) (? b) (? c)) (? b)))  (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
          ((= (if (? a) (? b) (? c)) (? b))                    (build.modus-ponens-2 *1 @-))
          ((= (? b) (? b2))                                    (@given y))
          ((= (if (? a) (? b) (? c)) (? b2))                   (build.transitivity-of-pequal @-- @-)))
  :minatbl ((if . 3)
            (equal . 2)))

(defderiv eval-lemma-2-bldr
  :derive (= (if (? a) (? b) (? c)) (? c2))
  :from   ((proof x (= (? a) nil))
           (proof y (= (? c) (? c2)))
           (term then (? b)))
  :proof (@derive
          ((v (!= x nil) (= (if x y z) z))                       (build.axiom (axiom-if-when-nil)))
          ((v (!= (? a) nil) (= (if (? a) (? b) (? c)) (? c)))   (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
          ((= (? a) nil)                                         (@given x))
          ((= (if (? a) (? b) (? c)) (? c))                      (build.modus-ponens @- @--))
          ((= (? c) (? c2))                                      (@given y))
          ((= (if (? a) (? b) (? c)) (? c2))                     (build.transitivity-of-pequal @-- @-)))
  :minatbl ((if . 3)))





;: generic-evaluator-bldr
;: Derive (f c1 ... cn) = val
;:   where c1,...,cn are constants and
;:   the computation successfully completes.
;:
;; We are finally ready to introduce the function that can build a proof that
;; the input term is equal to the evaluator's output.
;;
;; Note that generic-evaluator can fail.  If it fails, our builder will return
;; nil.  Otherwise, we will produce a proof that term = result.  (In the list
;; case, we return nil or (cons t proofs), where proofs is a list of proofs
;; which conclude arg1=val1, ..., argn=valn.)

(defund flag-generic-evaluator-bldr (flag x defs n)
  (declare (xargs :guard (and (definition-listp defs)
                              (natp n)
                              (if (equal flag 'term)
                                  (and (logic.termp x)
                                       (logic.groundp x)
                                       (generic-evaluator x defs n))
                                (and (logic.term-listp x)
                                     (logic.ground-listp x)
                                     (generic-evaluator-list x defs n))))
                  :measure (two-nats-measure n (rank x))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((zp n)
             ;; Insufficient "n" to evaluate this term.
             nil)
            ((logic.constantp x)
             ;; Constants evaluate to themselves.
             (build.reflexivity x))
            ((logic.variablep x)
             ;; Not a ground term.
             nil)
            ((logic.functionp x)
             (let ((fn   (logic.function-name x))
                   (args (logic.function-args x)))
               (if (equal fn 'if)
                   ;; Special lazy handling of the if function for recursive termination.
                   (and (equal (len args) 3)
                        (let ((arg1-proof (flag-generic-evaluator-bldr 'term (first args) defs n)))
                          (and arg1-proof
                               (let ((arg1-prime (logic.=rhs (logic.conclusion arg1-proof))))
                                 (if (logic.unquote arg1-prime)
                                     ;; Arg1 evaluted to a non-nil constant.
                                     (let ((arg2-proof (flag-generic-evaluator-bldr 'term (second args) defs n)))
                                       (and arg2-proof
                                            (eval-lemma-1-bldr arg1-proof arg2-proof (third args))))
                                   ;; Arg1 evaluated to nil.
                                   (let ((arg3-proof (flag-generic-evaluator-bldr 'term (third args) defs n)))
                                     (and arg3-proof
                                          (eval-lemma-2-bldr arg1-proof arg3-proof (second args)))))))))
                 ;; We eagerly evaluate the arguments to functions other than "if".
                 (let ((aproofs+ (flag-generic-evaluator-bldr 'list args defs n)))
                   (and aproofs+
                        ;; Arguments successfully evaluated; aproofs+ is of the form
                        ;; (t . [proofs of arg1=val1 ... argn=valn])
                        (let* ((aproofs (cdr aproofs+))
                               (vals    (logic.=rhses (logic.strip-conclusions aproofs))))
                          (if (memberp fn (domain (logic.initial-arity-table)))
                              ;; We found a base function
                              (and (equal (cdr (lookup fn (logic.initial-arity-table))) (len aproofs))
                                   ;; Goal: (fn arg1 ... argn) = result.
                                   ;;   1. (fn arg1 ... argn) = (fn val1 ... valn) by logic.pequal by args
                                   ;;   2. (fn val1 ... valn) = result             by base evaluation
                                   ;;   3. (fn arg1 ... argn) = result             by transitivity of =
                                   ;; Q.E.D.
                                   (build.transitivity-of-pequal (build.pequal-by-args fn aproofs)
                                                                 (build.base-eval (logic.function fn vals))))
                            ;; We found a defined function
                            (let* ((def (definition-list-lookup fn defs)))
                              (and def
                                   (let ((formals (logic.function-args (logic.=lhs def)))
                                         (body    (logic.=rhs def)))
                                     (and (equal (len formals) (len aproofs))
                                          ;; Substitute the values into the body and recursively evaluate the result.
                                          (let* ((sigma       (pair-lists formals vals))
                                                 (ground-body (logic.substitute body sigma))
                                                 (body-proof  (flag-generic-evaluator-bldr 'term ground-body defs (- n 1))))
                                            (and body-proof
                                                 ;; Goal: (fn arg1 ... argn) = value
                                                 ;;  1. body/sigma = value                      by our body-proof
                                                 ;;  2. (fn val1 ... valn) = body/sigma         by instantiation fn's definition
                                                 ;;  3. (fn val1 ... valn) = value              by transitivity of =
                                                 ;;  4. arg1=val1 ... argn=valn                 by aproofs
                                                 ;;  5. (fn arg1 ... argn) = (fn val1 ... valn) by pequal-by-args
                                                 ;;  6. (fn arg1 ... argn) = value              by transitivity of =
                                                 ;; Q.E.D.
                                                 (build.transitivity-of-pequal (build.pequal-by-args fn aproofs)
                                                                               (build.transitivity-of-pequal
                                                                                (build.instantiation (build.axiom def) sigma)
                                                                                body-proof)))))))))))))))
            ((logic.lambdap x)
             (let ((formals  (logic.lambda-formals x))
                   (body     (logic.lambda-body x))
                   (actuals  (logic.lambda-actuals x)))
               (let ((aproofs+ (flag-generic-evaluator-bldr 'list actuals defs n)))
                 (and aproofs+
                      (let* ((vals       (logic.=rhses (logic.strip-conclusions (cdr aproofs+))))
                             (sigma      (pair-lists formals vals))
                             (body-proof (flag-generic-evaluator-bldr 'term (logic.substitute body sigma) defs (- n 1))))
                        (and body-proof
                             ;; Goal: ((lambda formals body) actuals) = result
                             ;;  1. actuals[i] = values[i]                                            by aproofs
                             ;;  2. ((lambda formals body) actuals) = ((lambda formals body) values)  by logic.pequal by args
                             ;;  3. ((lambda formals body) values) = body/[formals<-values]           by beta reduction
                             ;;  4. ((lambda formals body) actuals) = body/[formals<-values]          by transitivity of =
                             ;;  5. body/[formals<-values] = result                                   by body-proof
                             ;;  6. ((lambda formals body) actuals) = result                          by transitivity of =
                             ;;
                             ;; Q.E.D.
                             (build.transitivity-of-pequal (build.transitivity-of-pequal
                                                            (build.lambda-pequal-by-args formals body (cdr aproofs+))
                                                            (build.beta-reduction formals body vals))
                                                           body-proof)))))))
            (t nil))
    (if (consp x)
        ;; Try to evaluate the first argument and then, recursively, the rest of
        ;; the arguments.
        (let ((first (flag-generic-evaluator-bldr 'term (car x) defs n))
              (rest  (flag-generic-evaluator-bldr 'list (cdr x) defs n)))
          (if (and first rest)
              ;; SUCCESS: evaluated the first and all other arguments.
              (cons t (cons first (cdr rest)))
            ;; FAILURE: couldn't evaluate some argument.
            nil))
      ;; SUCCESS: the empty list can always be evaluted.
      (cons t nil))))

(definlined generic-evaluator-bldr (x defs n)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.groundp x)
                              (definition-listp defs)
                              (natp n)
                              (generic-evaluator x defs n))
                  :verify-guards nil))
  (flag-generic-evaluator-bldr 'term x defs n))

(definlined generic-evaluator-list-bldr (x defs n)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.ground-listp x)
                              (definition-listp defs)
                              (natp n)
                              (generic-evaluator-list x defs n))
                  :verify-guards nil))
  (flag-generic-evaluator-bldr 'list x defs n))

(defthmd definition-of-generic-evaluator-bldr
  (equal (generic-evaluator-bldr x defs n)
         (cond ((zp n)
                ;; Insufficient "n" to evaluate this term.
                nil)
               ((logic.constantp x)
                ;; Constants evaluate to themselves.
                (build.reflexivity x))
               ((logic.variablep x)
                ;; Not a ground term.
                nil)
               ((logic.functionp x)
                (let ((fn   (logic.function-name x))
                      (args (logic.function-args x)))
                  (if (equal fn 'if)
                      ;; Special lazy handling of the if function for recursive termination.
                      (and (equal (len args) 3)
                           (let ((arg1-proof (generic-evaluator-bldr (first args) defs n)))
                             (and arg1-proof
                                  (let ((arg1-prime (logic.=rhs (logic.conclusion arg1-proof))))
                                    (if (logic.unquote arg1-prime)
                                        ;; Arg1 evaluted to a non-nil constant.
                                        (let ((arg2-proof (generic-evaluator-bldr (second args) defs n)))
                                          (and arg2-proof
                                               (eval-lemma-1-bldr arg1-proof arg2-proof (third args))))
                                      ;; Arg1 evaluated to nil.
                                      (let ((arg3-proof (generic-evaluator-bldr (third args) defs n)))
                                        (and arg3-proof
                                             (eval-lemma-2-bldr arg1-proof arg3-proof (second args)))))))))

                    ;; We eagerly evaluate the arguments to functions other than "if".
                    (let ((aproofs+ (generic-evaluator-list-bldr args defs n)))
                      (and aproofs+
                           ;; Arguments successfully evaluated; aproofs+ is of the form
                           ;; (t . [proofs of arg1=val1 ... argn=valn])
                           (let* ((aproofs (cdr aproofs+))
                                  (vals    (logic.=rhses (logic.strip-conclusions aproofs))))

                             (if (memberp fn (domain (logic.initial-arity-table)))
                                 ;; We found a base function
                                 (and (equal (cdr (lookup fn (logic.initial-arity-table))) (len aproofs))
                                      ;; Goal: (fn arg1 ... argn) = result.
                                      ;;   1. (fn arg1 ... argn) = (fn val1 ... valn) by logic.pequal by args
                                      ;;   2. (fn val1 ... valn) = result             by base evaluation
                                      ;;   3. (fn arg1 ... argn) = result             by transitivity of =
                                      ;; Q.E.D.
                                      (build.transitivity-of-pequal (build.pequal-by-args fn aproofs)
                                                                    (build.base-eval (logic.function fn vals))))
                               ;; We found a defined function
                               (let* ((def (definition-list-lookup fn defs)))
                                 (and def
                                      (let ((formals (logic.function-args (logic.=lhs def)))
                                            (body    (logic.=rhs def)))
                                        (and (equal (len formals) (len aproofs))
                                             ;; Substitute the values into the body and recursively evaluate the result.
                                             (let* ((sigma       (pair-lists formals vals))
                                                    (ground-body (logic.substitute body sigma))
                                                    (body-proof  (generic-evaluator-bldr ground-body defs (- n 1))))
                                               (and body-proof
                                                    ;; Goal: (fn arg1 ... argn) = value
                                                    ;;  1. body/sigma = value                      by our body-proof
                                                    ;;  2. (fn val1 ... valn) = body/sigma         by instantiation fn's definition
                                                    ;;  3. (fn val1 ... valn) = value              by transitivity of =
                                                    ;;  4. arg1=val1 ... argn=valn                 by aproofs
                                                    ;;  5. (fn arg1 ... argn) = (fn val1 ... valn) by pequal-by-args
                                                    ;;  6. (fn arg1 ... argn) = value              by transitivity of =
                                                    ;; Q.E.D.
                                                    (build.transitivity-of-pequal (build.pequal-by-args fn aproofs)
                                                                                  (build.transitivity-of-pequal
                                                                                   (build.instantiation (build.axiom def) sigma)
                                                                                   body-proof)))))))))))))))
               ((logic.lambdap x)
                (let ((formals  (logic.lambda-formals x))
                      (body     (logic.lambda-body x))
                      (actuals  (logic.lambda-actuals x)))
                  (let ((aproofs+ (generic-evaluator-list-bldr actuals defs n)))
                    (and aproofs+
                         (let* ((vals       (logic.=rhses (logic.strip-conclusions (cdr aproofs+))))
                                (sigma      (pair-lists formals vals))
                                (body-proof (generic-evaluator-bldr (logic.substitute body sigma) defs (- n 1))))
                           (and body-proof
                                ;; Goal: ((lambda formals body) actuals) = result
                                ;;  1. actuals[i] = values[i]                                            by aproofs
                                ;;  2. ((lambda formals body) actuals) = ((lambda formals body) values)  by logic.pequal by args
                                ;;  3. ((lambda formals body) values) = body/[formals<-values]           by beta reduction
                                ;;  4. ((lambda formals body) actuals) = body/[formals<-values]          by transitivity of =
                                ;;  5. body/[formals<-values] = result                                   by body-proof
                                ;;  6. ((lambda formals body) actuals) = result                          by transitivity of =
                                ;;
                                ;; Q.E.D.
                                (build.transitivity-of-pequal (build.transitivity-of-pequal
                                                               (build.lambda-pequal-by-args formals body (cdr aproofs+))
                                                               (build.beta-reduction formals body vals))
                                                              body-proof)))))))
               (t nil)))
  :rule-classes :definition
  :hints (("Goal"
           :in-theory (enable generic-evaluator-bldr
                              generic-evaluator-list-bldr
                              flag-generic-evaluator-bldr)
           :expand ((flag-generic-evaluator-bldr 'term x defs n)))))

(defthmd definition-of-generic-evaluator-list-bldr
  (equal (generic-evaluator-list-bldr x defs n)
         (if (consp x)
             ;; Try to evaluate the first argument and then, recursively, the rest of
             ;; the arguments.
             (let ((first (generic-evaluator-bldr (car x) defs n))
                   (rest  (generic-evaluator-list-bldr (cdr x) defs n)))
               (if (and first rest)
                   ;; SUCCESS: evaluated the first and all other arguments.
                   (cons t (cons first (cdr rest)))
                 ;; FAILURE: couldn't evaluate some argument.
                 nil))
           ;; SUCCESS: the empty list can always be evaluted.
           (cons t nil)))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable generic-evaluator-bldr
                             generic-evaluator-list-bldr
                             flag-generic-evaluator-bldr))))

(defthm flag-generic-evaluator-bldr-of-term
  (equal (flag-generic-evaluator-bldr 'term x defs n)
         (generic-evaluator-bldr x defs n))
  :hints(("Goal" :in-theory (enable generic-evaluator-bldr))))

(defthm flag-generic-evaluator-bldr-of-list
  (equal (flag-generic-evaluator-bldr 'list x defs n)
         (generic-evaluator-list-bldr x defs n))
  :hints(("Goal" :in-theory (enable generic-evaluator-list-bldr))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition generic-evaluator-bldr))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition generic-evaluator-list-bldr))))

(defobligations generic-evaluator-bldr
  (build.reflexivity eval-lemma-1-bldr eval-lemma-2-bldr build.transitivity-of-pequal
   build.pequal-by-args build.base-eval build.lambda-pequal-by-args))

(defobligations generic-evaluator-list-bldr
  (generic-evaluator-bldr))



(defthm forcing-len-of-cdr-of-generic-evaluator-list-bldr
  (implies (force (generic-evaluator-list-bldr x defs n))
           (equal (len (cdr (generic-evaluator-list-bldr x defs n)))
                  (len x)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable definition-of-generic-evaluator-list-bldr))))

(local (defthm crock
         (implies (submapp (logic.initial-arity-table) atbl)
                  (equal (lookup 'if atbl)
                         '(if . 3)))
         :hints(("Goal"
                 :in-theory (enable logic.initial-arity-table)
                 :use ((:instance equal-of-lookups-when-submapp
                                  (x (logic.initial-arity-table))
                                  (y atbl)
                                  (a 'if)))))))

(defthms-flag
  :shared-hyp (force (definition-listp defs))
  :thms ((term forcing-logic.appealp-of-generic-evaluator-bldr
               (implies (and (force (logic.termp x))
                             (force (generic-evaluator x defs n)))
                        (equal (logic.appealp (generic-evaluator-bldr x defs n))
                               t)))
         (term forcing-logic.conclusion-of-generic-evaluator-bldr
               (implies (and (force (logic.termp x))
                             (force (generic-evaluator x defs n)))
                        (equal (logic.conclusion (generic-evaluator-bldr x defs n))
                               (logic.pequal x (generic-evaluator x defs n)))))
         (t forcing-consp-of-generic-evaluator-list-bldr
            (implies (and (force (logic.term-listp x))
                          (force (generic-evaluator-list x defs n)))
                     (equal (consp (generic-evaluator-list-bldr x defs n))
                            t)))
         (t forcing-logic.appeal-listp-of-generic-evaluator-list-bldr
            (implies (and (force (logic.term-listp x))
                          (force (generic-evaluator-list x defs n)))
                     (equal (logic.appeal-listp (cdr (generic-evaluator-list-bldr x defs n)))
                            t)))
         (t forcing-logic.strip-conclusions-of-generic-evaluator-list-bldr
            (implies (and (force (logic.term-listp x))
                          (force (generic-evaluator-list x defs n)))
                     (equal (logic.strip-conclusions (cdr (generic-evaluator-list-bldr x defs n)))
                            (logic.pequal-list x (cdr (generic-evaluator-list x defs n)))))))
  :hints (("Goal"
           :in-theory (e/d (definition-of-generic-evaluator
                             definition-of-generic-evaluator-list
                             definition-of-generic-evaluator-bldr
                             definition-of-generic-evaluator-list-bldr
                             flag-generic-evaluator)
                           (forcing-lookup-of-logic.function-name))
           :induct (flag-generic-evaluator flag x defs n))))


(encapsulate
 ()
 (local (in-theory (disable logic.unquote-under-iff-when-logic.constantp)))
 (local (in-theory (disable forcing-lookup-of-logic.function-name)))

 (local (defthm lemma1
          (implies (and (generic-evaluator term defs n)
                        (logic.termp term)
                        (logic.functionp term)
                        (equal (logic.function-name term) 'if)
                        (logic.unquote (generic-evaluator (first (logic.function-args term)) defs n)))
                   (generic-evaluator (second (logic.function-args term)) defs n))
          :hints(("Goal" :in-theory (enable definition-of-generic-evaluator)))))

 (local (defthm lemma2
          (implies (and (generic-evaluator term defs n)
                        (logic.functionp term)
                        (equal (logic.function-name term) 'if)
                        (not (logic.unquote (generic-evaluator (first (logic.function-args term)) defs n))))
                   (generic-evaluator (third (logic.function-args term)) defs n))
          :hints(("Goal" :in-theory (enable definition-of-generic-evaluator)))))

 (local (defthm lemma3
          (implies (and (generic-evaluator term defs n)
                        (logic.functionp term)
                        (equal (logic.function-name term) 'if))
                   (generic-evaluator (first (logic.function-args term)) defs n))
          :hints(("Goal" :in-theory (enable definition-of-generic-evaluator)))))

 (local (defthm lemma4
          (implies (and (generic-evaluator term defs n)
                        (logic.functionp term)
                        (not (equal (logic.function-name term) 'if))
                        (not (lookup (logic.function-name term) (logic.initial-arity-table))))
                   (generic-evaluator
                    (logic.substitute
                     (logic.=rhs (definition-list-lookup (logic.function-name term) defs))
                     (pair-lists (logic.function-args (logic.=lhs (definition-list-lookup (logic.function-name term) defs)))
                                 (cdr (generic-evaluator-list (logic.function-args term) defs n))))
                    defs (- n 1)))
          :hints(("Goal" :in-theory (enable definition-of-generic-evaluator)))))

 (local (defthm lemma5
          (implies (and (generic-evaluator term defs n)
                        (logic.functionp term)
                        (not (equal (logic.function-name term) 'if)))
                   (generic-evaluator-list (logic.function-args term) defs n))
          :hints(("Goal" :in-theory (enable definition-of-generic-evaluator)))))

 (local (defthm lemma6
          (implies (and (generic-evaluator term defs n)
                        (not (logic.constantp term))
                        (not (logic.variablep term))
                        (not (logic.functionp term))
                        (logic.termp term))
                   (iff (generic-evaluator
                         (logic.substitute (logic.lambda-body term)
                                           (pair-lists (logic.lambda-formals term)
                                                       (cdr (generic-evaluator-list (logic.lambda-actuals term) defs n))))
                         defs (- n 1))
                        t))
          :hints(("Goal" :in-theory (enable definition-of-generic-evaluator)))))

 (local (defthm lemma7
          (implies (and (generic-evaluator term defs n)
                        (not (logic.constantp term))
                        (not (logic.variablep term))
                        (not (logic.functionp term))
                        (logic.termp term))
                   (iff (generic-evaluator-list (logic.lambda-actuals term) defs n)
                        t))
          :hints(("Goal" :in-theory (enable definition-of-generic-evaluator)))))

 (local (in-theory (enable logic.unquote-under-iff-when-logic.constantp)))

 (verify-guards flag-generic-evaluator-bldr)
 (verify-guards generic-evaluator-bldr
                :hints(("Goal" :in-theory (enable definition-of-generic-evaluator
                                                  definition-of-generic-evaluator-list)))))

(defthm forcing-generic-evaluator-bldr-under-iff
  (implies (and (force (logic.termp x))
                (force (definition-listp defs))
                (force (generic-evaluator x defs n)))
           (iff (generic-evaluator-bldr x defs n)
                t))
  :hints(("Goal"
          :in-theory (disable forcing-logic.appealp-of-generic-evaluator-bldr)
          :use ((:instance forcing-logic.appealp-of-generic-evaluator-bldr)))))

(defthm forcing-generic-evaluator-list-bldr-under-iff
  (implies (and (force (logic.term-listp x))
                (force (definition-listp defs))
                (force (generic-evaluator-list x defs n)))
           (iff (generic-evaluator-list-bldr x defs n)
                t))
  :hints(("Goal"
          :in-theory (disable forcing-consp-of-generic-evaluator-list-bldr)
          :use ((:instance forcing-consp-of-generic-evaluator-list-bldr)))))



(defthms-flag
  :@contextp t
  :shared-hyp (force (and (definition-listp defs)
                          (logic.formula-list-atblp defs atbl)
                          (equal (cdr (lookup 'if atbl)) 3)
                          (equal (cdr (lookup 'equal atbl)) 2)
                          (subsetp defs axioms)
                          (@obligations generic-evaluator-bldr)))
  :thms ((term forcing-logic.proofp-of-generic-evaluator-bldr
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (generic-evaluator x defs n)))
                        (equal (logic.proofp (generic-evaluator-bldr x defs n) axioms thms atbl)
                               t)))
         (t forcing-logic.proof-listp-of-generic-evaluator-list-bldr
            (implies (force (and (logic.term-listp x)
                                 (logic.term-list-atblp x atbl)
                                 (generic-evaluator-list x defs n)))
                     (equal (logic.proof-listp (cdr (generic-evaluator-list-bldr x defs n)) axioms thms atbl)
                            t))))
  :hints (("Goal"
           :in-theory (enable definition-of-generic-evaluator
                              definition-of-generic-evaluator-list
                              definition-of-generic-evaluator-bldr
                              definition-of-generic-evaluator-list-bldr
                              flag-generic-evaluator
                              )
           ;; :restrict ((forcing-lookup-of-logic.function-name ((atbl atbl))))
           :induct (flag-generic-evaluator flag x defs n))))


