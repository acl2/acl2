
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

(local (include-book "join-thms"))


(encapsulate
  (((bad-guy-clause-proc * *) => *)
   ((bad-guy-alist-lists * * *) => *))

  (defevaluator if-ev if-ev-lst ((if a b c)))

  (defchoose if-ev-bad-guy (al) (clauses)
    (not (if-ev (conjoin (disjoin-lst clauses)) al)))

  (defun clause-apply-alists-if-ev (clause alists)
    (or (atom alists)
        (and (if-ev (disjoin clause) (car alists))
             (clause-apply-alists-if-ev clause (cdr alists)))))

  (defun clauses-apply-alists-if-ev (clauses alist-lists)
    (or (atom clauses)
        (and (clause-apply-alists-if-ev (car clauses) (car alist-lists))
             (clauses-apply-alists-if-ev (cdr clauses) (cdr alist-lists)))))


  (local (defun bad-guy-clause-proc (cl hints)
           (declare (ignore cl hints))
           (list nil)))

  (local (defun bad-guy-alist-lists (cl hints al)
           (declare (ignore cl hints al))
           (list (list nil))))


  (defthm bad-guy-clause-proc-lemma
    (implies (and (pseudo-term-listp cl)
                  (alistp al)
                  (clauses-apply-alists-if-ev
                   (bad-guy-clause-proc cl hints)
                   (bad-guy-alist-lists cl hints al)))
             (if-ev (disjoin cl) al))
    :hints (("goal" :do-not-induct t
             :expand ((:free (x) (hide x)))))
    :rule-classes nil))


(local
 (progn
   (def-join-thms if-ev)




   (defthm member-conjoin-clauses-true
     (implies (and (member-equal clause clauses)
                   (if-ev (conjoin (disjoin-lst clauses)) al))
              (if-ev (disjoin clause) al))
     :hints (("goal" :in-theory (enable conjoin-clauses))))

   (defthm if-ev-bad-guy-rewrite
     (implies (not (if-ev (conjoin (disjoin-lst clauses)) al))
              (not (if-ev (conjoin (disjoin-lst clauses))
                          (if-ev-bad-guy clauses))))
     :hints (("goal" :use if-ev-bad-guy)))

   (defthm clauses-true-for-if-ev-cdr
     (implies (if-ev (conjoin (disjoin-lst clauses)) (if-ev-bad-guy clauses))
              (if-ev (conjoin (disjoin-lst (cdr clauses)))
                     (if-ev-bad-guy (cdr clauses))))
     :hints (("Subgoal *1/2"
              :use ((:instance if-ev-bad-guy
                               (al (if-ev-bad-guy (cdr clauses))))))))


   (defthm member-true-for-if-ev
     (implies (and (member-equal clause clauses)
                   (if-ev (conjoin (disjoin-lst clauses)) (if-ev-bad-guy clauses)))
              (if-ev (disjoin clause) al))
     :hints (("Subgoal *1/2" :use if-ev-bad-guy)))

   (defthm clause-true-for-ev-apply-alists-ok
     (implies (and (member-equal clause clauses)
                   (if-ev (conjoin (disjoin-lst clauses))
                          (if-ev-bad-guy clauses)))
              (clause-apply-alists-if-ev clause alists))
     :hints(("Goal"
             :induct (clause-apply-alists-if-ev clause alists))))

   (defthm clauses-true-for-ev-apply-alists-ok
     (implies (if-ev (conjoin (disjoin-lst clauses))
                     (if-ev-bad-guy clauses))
              (clauses-apply-alists-if-ev clauses alist-lists))
     :hints(("Subgoal *1/4"
             :in-theory  (e/d ()
                              (clause-true-for-ev-apply-alists-ok))
             :use ((:instance clause-true-for-ev-apply-alists-ok
                              (clause (car clauses))
                              (alists (car alist-lists)))))))))

(defthm bad-guy-clause-proc-correct
  (implies (and (pseudo-term-listp cl)
                (alistp al)
                (if-ev (conjoin-clauses
                        (bad-guy-clause-proc cl hints))
                       (if-ev-bad-guy (bad-guy-clause-proc cl hints))))
           (if-ev (disjoin cl) al))
  :hints (("goal" :in-theory (enable conjoin-clauses)
           :use bad-guy-clause-proc-lemma))
  :rule-classes nil)


(defmacro incat (sym &rest lst)
  `(intern-in-package-of-symbol
    (concatenate 'string . ,lst)
    ,sym))

(defun def-multi-env-fn (ev)
  (let ((bad-guy (incat ev (symbol-name ev) "-BAD-GUY"))
        (bad-guy-rewrite (incat ev (symbol-name ev) "-BAD-GUY-REWRITE"))
        (clause-apply (incat ev "CLAUSE-APPLY-ALISTS-" (symbol-name ev)))
        (clauses-apply (incat ev "CLAUSES-APPLY-ALISTS-" (symbol-name ev))))
    `(progn
       (defchoose ,bad-guy (al) (clauses)
         (not (,ev (conjoin (disjoin-lst clauses)) al)))

       (defthm ,bad-guy-rewrite
         (implies (not (,ev (conjoin (disjoin-lst clauses)) al))
                  (not (,ev (conjoin (disjoin-lst clauses))
                            (,bad-guy clauses))))
         :hints (("goal" :use ,bad-guy)))

       (defun ,clause-apply (clause alists)
         (or (atom alists)
             (and (,ev (disjoin clause) (car alists))
                  (,clause-apply clause (cdr alists)))))

       (defun ,clauses-apply (clauses alist-lists)
         (or (atom clauses)
             (and (,clause-apply (car clauses) (car alist-lists))
                  (,clauses-apply (cdr clauses) (cdr alist-lists))))))))

(defmacro def-multi-env-fns (ev)
  (def-multi-env-fn ev))

(defun nth-bindings (n var varlst)
  (if (endp varlst)
      nil
    (cons `(,(car varlst) (nth ,n ,var))
          (nth-bindings (1+ n) var (cdr varlst)))))

(defun prove-multi-env-clause-proc-fn (name ev evlst clauseproc alistfn hints
                                            world)
  (declare (xargs :mode :program))
  (let* ((bad-guy (incat ev (symbol-name ev) "-BAD-GUY"))
         ;; (bad-guy-rewrite (incat ev (symbol-name ev) "-BAD-GUY-REWRITE"))
         (clause-apply (incat ev "CLAUSE-APPLY-ALISTS-" (symbol-name ev)))
         (clauses-apply (incat ev "CLAUSES-APPLY-ALISTS-" (symbol-name ev)))
         (cp-nargs
          (length (getprop clauseproc 'formals nil 'current-acl2-world world)))
         (ign (and (< 2 cp-nargs)
                 (er hard 'prove-multi-env-clause-proc
                     "This utility currently only works for clause processors ~
                     that take 1 or 2 arguments.  Feel free to patch.~%")))
         (cp-call `(,clauseproc . ,(take cp-nargs '(cl hints))))
         (cp-lambda `(lambda (cl hints)
                       (,clauseproc . ,(take cp-nargs '(cl hints)))))
         (constraint-0 (genvar ev (symbol-name (pack2 ev '-constraint-))
                               0 nil)))
    (declare (ignore ign))
    `(progn
       (def-multi-env-fns ,ev)
       (defthm ,name
         (implies (and (pseudo-term-listp cl)
                       (alistp al)
                       (,ev (conjoin-clauses ,cp-call)
                            (,bad-guy ,cp-call)))
                  (,ev (disjoin cl) al))
         :hints (("Goal" :use ((:functional-instance
                                bad-guy-clause-proc-correct
                                (if-ev ,ev)
                                (if-ev-lst ,evlst)
                                (if-ev-bad-guy ,bad-guy)
                                (clause-apply-alists-if-ev
                                 ,clause-apply)
                                (clauses-apply-alists-if-ev
                                 ,clauses-apply)
                                (bad-guy-clause-proc
                                 ,cp-lambda)
                                (bad-guy-alist-lists
                                 ,alistfn))))
                 (and stable-under-simplificationp
                      '(:in-theory (enable ,constraint-0)))
                 . ,hints)
         :rule-classes :clause-processor))))

(defmacro prove-multi-env-clause-proc
  (name &key ev evlst clauseproc alistfn hints)
  `(make-event
    (prove-multi-env-clause-proc-fn
     ',name ',ev ',evlst ',clauseproc ',alistfn ',hints (w state))))



#||
;; example.

;; evaluator:

(defevaluator demo-ev demo-ev-lst ((if a b c) (equal a b)))


;;; This stupid clause processor takes a term of the form
;;; (equal (f a b) (f c d))
;;; and produces the single clause (equal x y).  (hah!)  
(defun equal-fs-cp (clause)
  (if (and (consp clause)
           (null (cdr clause)))
      (let ((car (car clause)))
        (case-match car
          (('equal (f & &) (g & &))
           (if (equal f g)
               '(((equal x y)))
             (list clause)))
          (& (list clause))))
    (list clause)))     


;; This function produces, for each clause produced by the clause processor
;; above, a list of alists.  Proving that each clause evaluates to nonnil under
;; all the corresponding alists suffices to prove the original clause.
(defun equal-fs-cp-alists (clause al)
  (if (and (consp clause)
           (null (cdr clause)))
      (let ((car (car clause)))
        (case-match car
          (('equal (f a b) (g c d))
           (if (equal f g)
               `((((x . ,a) (y . ,c))
                  ((x . ,b) (y . ,d))))
             (list (list al))))
          (& (list (list al)))))
    (list (list al))))


(def-multi-env-fns demo-ev)

(def-join-thms demo-ev)

(defthm equal-fs-cp-lemma
  (implies (and (pseudo-term-listp cl)
                (alistp al)
                (clauses-apply-alists-demo-ev
                 (equal-fs-cp cl)
                 (equal-fs-cp-alists cl al)))
           (demo-ev (disjoin cl) al)))

(in-theory (disable equal-fs-cp equal-fs-cp-alists))



;; (defthm eval-fs-cp-correct
;;   (implies (and (pseudo-term-listp cl)
;;                 (alistp al)
;;                 (demo-ev (conjoin-clauses (equal-fs-cp cl))
;;                          (demo-ev-bad-guy (equal-fs-cp cl))))
;;            (demo-ev (disjoin cl) al))
;;   :hints (("goal" :use ((:functional-instance 
;;                          bad-guy-clause-proc-correct
;;                          (if-ev demo-ev)
;;                          (if-ev-lst demo-ev-lst)
;;                          (if-ev-bad-guy demo-ev-bad-guy)
;;                          (clause-apply-alists-if-ev
;;                           clause-apply-alists-demo-ev)
;;                          (clauses-apply-alists-if-ev
;;                           clauses-apply-alists-demo-ev)
;;                          (bad-guy-clause-proc
;;                           (lambda (cl hints) (equal-fs-cp cl)))
;;                          (bad-guy-alist-lists
;;                           (lambda (cl hints al)
;;                             (equal-fs-cp-alists cl al))))))
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable demo-ev-constraint-0))))
;;   :rule-classes :clause-processor)

(prove-multi-env-clause-proc
 equal-fs-cp-correct
 :ev demo-ev
 :evlst demo-ev-lst
 :clauseproc equal-fs-cp
 :alistfn (lambda (cl hints al) (equal-fs-cp-alists cl al)))





||#
