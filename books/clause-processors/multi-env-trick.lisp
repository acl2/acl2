; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")

;; This book introduces a trick for proving clause-processors correct.
;; The correctness theorem for a clause-processor looks like this:
;; (defthm my-cproc-correct
;;   (implies (and (pseudo-term-listp cl)
;;                 (alistp a)
;;                 (my-ev (conjoin-clauses (my-cp cl hints))
;;                        (my-alist cl hints a)))
;;            (my-ev (disjoin cl) a))
;;    :rule-classes :clause-processor)
;; This means we get to assume that each of the clauses produced by my-cp
;; evaluates to true under the alist produced by my-alist, and use this to
;; prove that cl evaluates to true under al.

;; However, in some cases it would be convenient to apply a different alist to
;; each clause produced or to apply multiple alists to some clauses.  This is
;; intuitively sound because when we use a clause-processor, we must prove that
;; all the generated clauses are generally true; that is, they evaluate to a
;; nonnil value under every alist.

;; Somewhat counterintuitively, if we can prove (my-ev (disjoin cl) a) given
;; multiple evaluations of each clause with each alist, then we can prove the
;; above theorem.  We can do this as follows: define a function that tries
;; evaluating every generated clause with each of the alists tried.  If any of
;; these evaluations are nil, return the first such alist, but if none are,
;; choose one arbitrarily.  By definition of this function, if the conjunction
;; of all clauses evaluates to true under the alist produced by the function,
;; then it evaluates to true under all alists mentioned.  Therefore if we use
;; this alist in the theorem above, we can assume those clauses evaluate to
;; true under the required alists.

;; This book introduces two event-producing macros. The first,
;; DEF-MULTI-ENV-FNS, defines several functions based on an evaluator; this
;; must be done as a prerequisite for the second.  The second,
;; PROVE-MULTI-ENV-CLAUSE-PROC, introduces the correctness theorem for a clause
;; processor. See the example (with DEMO-EV and EQUAL-FS-CP) at the bottom of
;; this file.

;; Usage of these macros:

;; DEF-MULTI-ENV-FNS is invoked as (DEF-MULTI-ENV-FNS <EV>) where EV is an
;; evaluator function defined using defevaluator.  This evaluator should, at
;; minimum, have IF among its recognized functions.  This introduces, among
;; other things, a function named CLAUSES-APPLY-ALISTS-<EV>.  This function
;; takes a list of clauses and a list of lists of alists.  It iterates through
;; the two lists in parallel.  For each corresponding pair of a clause and a
;; list of alists, it checks that under every alist in the list, the clause
;; evaluates to a nonnil value.  In order to prove a clause processor correct
;; under evaluator EV using PROVE-MULTI-ENV-CLAUSE-PROC, you will need to be
;; able to provide a function CLAUSE-PROC-ALIST-LISTS which produces a list of
;; lists of alists appropriate for pairing with the clauses produced by the
;; clause processor.  It then suffices to prove the following:

;; (implies (and (pseudo-term-listp cl)
;;               (alistp al)
;;               (clauses-apply-alists-ev
;;                (clause-proc cl hints)
;;                (clause-proc-alist-lists cl hints al)))
;;          (ev (disjoin cl) al))

;; PROVE-MULTI-ENV-CLAUSE-PROC will introduce a clause-processor correctness
;; theorem in the standard format (as MY-CPROC-CORRECT, at the top of the
;; page) using a bad-guy function for the alist in the third hyp.  It gives a
;; hint to prove this by functional instantiation such that this proof reduces
;; to a proof of the above lemma.

;; PROVE-MULTI-ENV-CLAUSE-PROC is invoked as follows:

;; (prove-multi-env-clause-proc
;;  <name of correctness thm>
;;  :ev <evaluator>
;;  :evlst <corresponding evaluator for lists>
;;  :clauseproc <clause processor function name>
;;  :alistfn <alist-list-list function or lambda>
;;  :hints <supplemental hints>)

;; Currently only clause processors which take one or two arguments (clause or
;; clause and hints) are supported; it is certainly possible to support clause
;; processors which take stobj arguments in addition, but this is not yet
;; impelemented.  The :ALISTFN argument expects a function or lambda of three
;; arguments corresponding to CL, HINTS, and AL in the theorem statement above.
;; If it takes fewer arguments, you must provide a lambda which wraps this
;; function, such as (LAMBDA (CL HINTS AL) (MY-ALIST-LIST-FN CL AL)).

(include-book "misc/untranslate-patterns" :dir :system)
(local (include-book "join-thms"))

(defevaluator multi-env-ev multi-env-ev-lst ((if a b c)))

(defchoose multi-env-ev-bad-guy (a) (x)
  (not (multi-env-ev x a)))

(defun clause-apply-alists-multi-env-ev (clause alists)
  (or (atom alists)
      (and (multi-env-ev (disjoin clause) (car alists))
           (clause-apply-alists-multi-env-ev clause (cdr alists)))))

(defun clauses-apply-alists-multi-env-ev (clauses alist-lists)
  (or (atom clauses)
      (and (clause-apply-alists-multi-env-ev
            (car clauses) (car alist-lists))
           (clauses-apply-alists-multi-env-ev
            (cdr clauses) (cdr alist-lists)))))

(defmacro multi-env-ev-theoremp (x)
  `(multi-env-ev ,x (multi-env-ev-bad-guy ,x)))

(add-untranslate-pattern
 (multi-env-ev ?x (multi-env-ev-bad-guy ?x))
 (multi-env-ev-theoremp ?x))



(local (def-join-thms multi-env-ev))

(defthm multi-env-ev-theoremp-implies-clause-apply-alists
  (implies (multi-env-ev-theoremp (disjoin x))
           (clause-apply-alists-multi-env-ev x alists))
  :hints (("Subgoal *1/3" :use
           ((:instance multi-env-ev-bad-guy
                       (x (disjoin x))
                       (a (car alists)))))))

(defthm multi-env-ev-theoremp-conjoin-cons
  (iff (multi-env-ev-theoremp (conjoin (cons a b)))
       (and (multi-env-ev-theoremp a)
            (multi-env-ev-theoremp (conjoin b))))
  :hints (("goal" :use
           ((:instance multi-env-ev-bad-guy
                       (x a)
                       (a (multi-env-ev-bad-guy
                           (conjoin (cons a b)))))
            (:instance multi-env-ev-bad-guy
                       (x (conjoin (cons a b)))
                       (a (multi-env-ev-bad-guy a)))
            (:instance multi-env-ev-bad-guy
                       (x (conjoin b))
                       (a (multi-env-ev-bad-guy
                           (conjoin (cons a b)))))
            (:instance multi-env-ev-bad-guy
                       (x (conjoin (cons a b)))
                       (a (multi-env-ev-bad-guy
                           (conjoin b))))))))

(defthm multi-env-theoremp-conjoin-clauses-cons
  (iff (multi-env-ev-theoremp (conjoin-clauses (cons a b)))
       (and (multi-env-ev-theoremp (disjoin a))
            (multi-env-ev-theoremp (conjoin-clauses b))))
  :hints(("Goal" :in-theory (enable conjoin-clauses))))



(defthm multi-env-ev-theoremp-implies-clauses-apply-alists
  (implies (multi-env-ev-theoremp (conjoin-clauses x))
           (clauses-apply-alists-multi-env-ev x alists))
  :hints(("Goal" :in-theory (enable conjoin-clauses disjoin-lst))))



(defmacro incat (sym &rest lst)
  `(intern-in-package-of-symbol
    (concatenate 'string . ,lst)
    ,sym))

(defun multi-env-functional-instance-fn
  (thm x alists ev evlst bad-guy)
  (let* ((bad-guy (or bad-guy (incat ev (symbol-name ev) "-BAD-GUY")))
         (clause-apply (incat ev "CLAUSE-APPLY-ALISTS-" (symbol-name ev)))
         (clauses-apply (incat ev "CLAUSES-APPLY-ALISTS-" (symbol-name ev))))
    `(:use ((:instance
             (:functional-instance
              ,thm
              (multi-env-ev ,ev)
              (multi-env-ev-lst ,evlst)
              (multi-env-ev-bad-guy ,bad-guy)
              (clause-apply-alists-multi-env-ev
               ,clause-apply)
              (clauses-apply-alists-multi-env-ev
               ,clauses-apply))
             (x ,x)
             (alists ,alists))))))

(defmacro multi-env-functional-instance
  (thm x alists &key ev evlst bad-guy)
  `(multi-env-functional-instance-fn
    ',thm ',x ',alists ',ev ',evlst ',bad-guy))


(defun def-multi-env-fn (ev evlst)
  (declare (xargs :mode :program))
  (let ((bad-guy (incat ev (symbol-name ev) "-BAD-GUY"))
        (bad-guy-rewrite (incat ev (symbol-name ev) "-BAD-GUY-REWRITE"))
        (theoremp (incat ev (symbol-name ev) "-THEOREMP"))
        (clause-apply (incat ev "CLAUSE-APPLY-ALISTS-" (symbol-name ev)))
        (clauses-apply (incat ev "CLAUSES-APPLY-ALISTS-" (symbol-name ev)))
        (clause-apply-thm
         (incat ev (symbol-name ev)
                "-THEOREMP-IMPLIES-CLAUSE-APPLY-ALISTS"))
        (clauses-apply-thm
         (incat ev (symbol-name ev)
                "-THEOREMP-IMPLIES-CLAUSES-APPLY-ALISTS"))
        (constraint-0 (genvar ev (symbol-name (pack2 ev '-constraint-))
                              0 nil)))
    `(progn
       (defchoose ,bad-guy (a) (x)
         (not (,ev x a)))

       (defthm ,bad-guy-rewrite
         (implies (,ev x (,bad-guy x))
                  (,ev x a))
         :hints (("goal" :use ,bad-guy)))

       (defmacro ,theoremp (x)
         `(,',ev ,x (,',bad-guy ,x)))

       (add-untranslate-pattern
        (,ev ?x (,bad-guy ?x))
        (,theoremp ?x))

       (defun ,clause-apply (clause alists)
         (or (atom alists)
             (and (,ev (disjoin clause) (car alists))
                  (,clause-apply clause (cdr alists)))))

       (defun ,clauses-apply (clauses alist-lists)
         (or (atom clauses)
             (and (,clause-apply (car clauses) (car alist-lists))
                  (,clauses-apply (cdr clauses) (cdr alist-lists)))))

       (defthmd ,clause-apply-thm
         (implies (,theoremp (disjoin clause))
                  (,clause-apply clause alists))
         :hints ((multi-env-functional-instance
                  multi-env-ev-theoremp-implies-clause-apply-alists
                  clause alists
                  :ev ,ev
                  :evlst ,evlst)
                 (and stable-under-simplificationp
                      '(:in-theory (enable ,constraint-0)))))

       (defthmd ,clauses-apply-thm
         (implies (,theoremp (conjoin-clauses clause))
                  (,clauses-apply clause alists))
         :hints ((multi-env-functional-instance
                  multi-env-ev-theoremp-implies-clauses-apply-alists
                  clause alists
                  :ev ,ev
                  :evlst ,evlst))))))

(defmacro def-multi-env-fns (ev evlst)
  (def-multi-env-fn ev evlst))




(defun prove-multi-env-clause-proc-fn (name ev evlst clauseproc alists hints
                                            bad-guy alist-name world)
  (declare (xargs :mode :program))
  (let* ((bad-guy (or bad-guy (incat ev (symbol-name ev) "-BAD-GUY")))
         (clauses-apply-thm
          (incat ev (symbol-name ev)
                 "-THEOREMP-IMPLIES-CLAUSES-APPLY-ALISTS"))
         (cp-args
          (fgetprop clauseproc 'formals nil world))
         (clausename (car cp-args))
         (multivaluesp (< 1 (len (fgetprop clauseproc 'stobjs-out nil world))))
         (cp-call1 `(,clauseproc . ,cp-args))
         (cp-call (if multivaluesp `(clauses-result ,cp-call1) cp-call1)))
    `(progn
       (def-multi-env-fns ,ev ,evlst)
       (defthm ,name
         (implies (and (pseudo-term-listp ,clausename)
                       (alistp ,alist-name)
                       (,ev (conjoin-clauses ,cp-call)
                            (,bad-guy (conjoin-clauses ,cp-call))))
                  (,ev (disjoin ,clausename) ,alist-name))
         :hints (("Goal" :use ((:instance
                                ,clauses-apply-thm
                                (clause ,cp-call)
                                (alists ,alists))))
                 . ,hints)
         :otf-flg t
         :rule-classes :clause-processor))))

(defmacro prove-multi-env-clause-proc
  (name &key ev evlst clauseproc alists bad-guy (alist-name 'al) hints)
  `(make-event
    (prove-multi-env-clause-proc-fn
     ',name ',ev ',evlst ',clauseproc ',alists
     ',hints ',bad-guy ',alist-name (w state))))



#||

;; Say we want to prove that a certain term always produces a CONS, and we
;; think this can be shown by a very simple syntactic analysis where we don't
;; consider contextual information such as let bindings, if tests, etc.  (In
;; reality this is pretty useless because ACL2 does a good job with this via
;; type reasoning.  But the principle can be applied to other things.)

;; Here is the evaluator we'll use:

(defevaluator cons-ev cons-ev-lst ((cons a b) (consp a) (if a b c)))

;; We want our clause processor to walk through the term as follows:

;; (consp-cp `(if ,x ,y ,z)) => (append (consp-cp y) (consp-cp z))
;; (consp-cp `((lambda ,vars ,body) . ,args)) => (consp-cp body)
;; (consp-cp `(cons ,a ,b)) => true
;; (consp-cp `(quote ,x)) => (consp x)
;; otherwise
;; (consp-cp x) => `(consp ,x).

(defun consp-cp-term (term)
  (case-match term
    (('if & y z)            (append (consp-cp-term y) (consp-cp-term z)))
    ((('lambda & body) . &) (consp-cp-term body))
    ;; If it's definitely a CONS we don't need to produce any new clauses.  If
    ;; it's definitely not a CONS then we produce the empty clause.
    (('cons & &)            nil)
    (('quote x)             (if (consp x) nil (list nil)))
    (&                      (list (list `(consp ,term))))))

;; The only difficulty with this is with the lambda step.  If we're evaluating
;; a term under alist AL and we get to a lambda, the evaluation of the lambda
;; body under AL has nothing to do with the evaluation of the term -- it needs
;; to be evaluated under the alist (pairlis$ lambda-vars (ev-lst lambda-args
;; al)).  So we introduce another function CONSP-CP-TERM-ALISTS which produces
;; alists corresponding to the clauses produced by the clause processor.
;; Actually, due to how clauses-apply-alists-cons-ev works, we produce a
;; singleton list containing the appropriate alist for each clause produced by
;; consp-cp-term.

(defun consp-cp-term-alists (term al)
  (case-match term
    (('if & y z)            (append (consp-cp-term-alists y al)
                                    (consp-cp-term-alists z al)))
    ((('lambda vars body) . args)
                            (consp-cp-term-alists
                             body
                             (pairlis$ vars
                                       (cons-ev-lst args al))))
    (('cons & &)            nil)
    (('quote x)             (if (consp x) nil (list (list al))))
    (&                      (list (list al)))))

;; We then define the clause processor itself and a corresponding
;; alist-generating function.

(defun consp-cp (clause)
  ;; Check that the clause's conclusion is of the form (consp term) and if so
  ;; run the subroutine above:
  (let ((term (car (last clause))))
    (case-match term
      (('consp x)  (consp-cp-term x))
      ;; otherwise, no-op:
      (&           (list clause)))))

(defun consp-cp-alists (clause al)
  (let ((term (car (last clause))))
    (case-match term
      (('consp x) (consp-cp-term-alists x al))
      (&          (list (list al))))))


;; The correctness argument:

(def-multi-env-fns cons-ev)

(def-join-thms cons-ev)

(defthm len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm consp-cp-term-alists-length
  (equal (len (consp-cp-term-alists term al))
         (len (consp-cp-term term))))

(defthm clauses-apply-alists-append
  (implies (equal (len a) (len a-al))
           (equal (clauses-apply-alists-cons-ev
                   (append a b) (append a-al b-al))
                  (and (clauses-apply-alists-cons-ev a a-al)
                       (clauses-apply-alists-cons-ev b b-al)))))

(defthm consp-cp-term-correct
  (implies (clauses-apply-alists-cons-ev
            (consp-cp-term term)
            (consp-cp-term-alists term al))
           (consp (cons-ev term al))))

(defthm consp-cp-term-correct1
  (implies (not (consp (cons-ev term al)))
           (not (clauses-apply-alists-cons-ev
                 (consp-cp-term term)
                 (consp-cp-term-alists term al)))))

(in-theory (disable consp-cp-term consp-cp-term-alists))

(defthm ev-car-last-implies-ev-clause
  (implies (cons-ev (car (last clause)) al)
           (cons-ev (disjoin clause) al))
  :hints(("Goal" :in-theory (e/d (disjoin) (cons-ev-of-disjoin-3)))))

;; The following lemma is the main requirement for successfully proving the
;; clause processor correct.  It says that when the clauses produced by
;; CONSP-CP evaluate to true with each of the corresponding alists produced by
;; CONSP-CP-ALISTS, then the original clause is satisfied.
(defthm consp-cp-correct-main-lemma
  (implies (clauses-apply-alists-cons-ev
            (consp-cp clause)
            (consp-cp-alists clause al))
           (cons-ev (disjoin clause) al)))

(in-theory (disable consp-cp consp-cp-alists))

;; Finally, this submits the correctness theorem allowing us to use CONSP-CP as
;; a verified clause processor:
(prove-multi-env-clause-proc
 consp-cp-correct
 :ev cons-ev :evlst cons-ev-lst
 :clauseproc consp-cp
 :alistfn (lambda (cl hints al) (consp-cp-alists cl al)))





||#
