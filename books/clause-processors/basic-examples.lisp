; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Certify with:
; (certify-book "basic-example" 0 t :ttags (my-ttag))

(in-package "ACL2")

; Define must-succeed and must-fail macros.
(include-book "misc/eval" :dir :system)

; A very basic example.

(defun note-fact-clause-processor (cl term)
  (declare (xargs :guard t)) ; optional, for better efficiency
  (list (cons (list 'not term)
              cl)
        (list term)))

(define-trusted-clause-processor
  note-fact-clause-processor
  nil
  :ttag my-ttag)

; redundant
(define-trusted-clause-processor
  note-fact-clause-processor
  nil
  :ttag my-ttag)

; equivalent to the preceding
(define-trusted-clause-processor
  note-fact-clause-processor
  nil
  :label note-fact-clause-processor$label
  :ttag my-ttag)

; not redundant
(must-fail
 (define-trusted-clause-processor
   note-fact-clause-processor
   nil
   :label other-label
   :ttag my-ttag))

(must-succeed
 (thm (equal (car (cons x y))
             x)
      :hints (("Goal"
               :clause-processor (:function
                                  note-fact-clause-processor
                                  :hint
                                  '(equal a a))))))

; Or pick some other functions for this evaluator:
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
(defevaluator evl evl-list
  ((if x y z) (length x) (member-equal x y) (equal x y) (not x)))

(defun strengthen-cl (cl term state)
  (declare (xargs :stobjs state))
; sad that we can't translate term first
  (cond ((null term) ; then no change
         (value (list cl)))
        ((pseudo-termp term) ; sad that we can't use termp!
         (value (list (cons (list 'not term)
                            cl)
                      (list term))))
        (t ; sad that we can't use (er soft ...)
         (prog2$ (cw "~%ERROR: Strengthen-cl was supplied an alleged term ~
                      that is not a term in the current ACL2 world.  Consider ~
                      evaluating the following, which will either cause an ~
                      error (with a potentially helpful message) or will ~
                      provide an appropriate term to use:~|~%  ~x0~|"
                     `(translate ',term t t t 'top-level (w state) state))
                 (mv t nil state)))))

(defthm correctness-of-strengthen-cl
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (strengthen-cl cl term state)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(must-fail
 (defthm test
   nil
   :rule-classes nil
   :hints (("Goal"
            :clause-processor
            (strengthen-cl (list ''t) '(equal x x) state)))))

(defthm test
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (strengthen-cl clause '(equal x x) state))))

; This one also tests the use of CLAUSE in the hint:
(defthm test2
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (:function strengthen-cl :hint (if clause '(equal x x) *t*)))))

; As above, but misspelled clause, so we get an error.
(must-fail
 (thm
   (equal (car (cons x y))
          x)
   :hints (("Goal"
            :clause-processor
            (:function strengthen-cl :hint (if clausexyz '(equal x x) *t*))))))

; fails with nice error messages (note missing arg of equal and non-term shape)
(must-fail
 (thm
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (strengthen-cl clause '(equal x) state)))))

(must-fail
 (thm
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (strengthen-cl clause '(equal x . y) state)))))

(must-fail
 (thm
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (:function strengthen-cl)))))

(must-succeed
; Same as immediately above, but succeeds under more liberal requirements on
; the hint: a symbol can have arity more than 1.
 (thm
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           strengthen-cl))))

(must-fail
 (thm
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           car))))

(must-fail
 (thm
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           binary-append))))

; Next we test the return of summary-data with a variant of strengthen-cl.

(defun strengthen-cl2 (cl term state)
  (declare (xargs :stobjs state))
; sad that we can't translate term first
  (cond ((null term) ; then no change
         (mv nil (list cl) state nil))
        ((pseudo-termp term) ; sad that we can't use termp!
         (mv nil
             (list (cons (list 'not term)
                         cl)
                   (list term))
             state
             (make-summary-data :runes '((:rewrite car-cons)
                                         (:rewrite cdr-cons)
                                         (:rewrite car-cons))
                                :use-names '(nth binary-append)
                                :by-names '(nthcdr)
                                :clause-processor-fns
                                '(note-fact-clause-processor))))
        (t ; sad that we can't use (er soft ...)
         (prog2$ (cw "~%ERROR: Strengthen-cl2 was supplied an alleged term ~
                      that is not a term in the current ACL2 world.  Consider ~
                      evaluating the following, which will either cause an ~
                      error (with a potentially helpful message) or will ~
                      provide an appropriate term to use:~|~%  ~x0~|"
                     `(translate ',term t t t 'top-level (w state) state))
                 (mv t nil state nil)))))

(defthm correctness-of-strengthen-cl2
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (strengthen-cl2 cl term state)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(defthm test-strengthen-cl2
  (equal y y)
  :hints (("Goal"
           :instructions
           ((:prove
             :hints (("Goal" 
                      :clause-processor
                      (strengthen-cl2 clause '(equal x x) state)))))))
  :rule-classes nil)

(assert-event
 (equal (sort-symbol-listp
         (car (global-val 'proof-supporters-alist (w state))))
        '(BINARY-APPEND CAR-CONS CDR-CONS
                        NOTE-FACT-CLAUSE-PROCESSOR NTH NTHCDR
                        STRENGTHEN-CL2 TEST-STRENGTHEN-CL2)))

; This variant returns summary-data = nil.
(defun strengthen-cl3 (cl term state)
  (declare (xargs :stobjs state))
; sad that we can't translate term first
  (cond ((null term) ; then no change
         (mv nil (list cl) state nil))
        ((pseudo-termp term) ; sad that we can't use termp!
         (mv nil
             (list (cons (list 'not term)
                         cl)
                   (list term))
             state
             nil))
        (t ; sad that we can't use (er soft ...)
         (prog2$ (cw "~%ERROR: Strengthen-cl3 was supplied an alleged term ~
                      that is not a term in the current ACL2 world.  Consider ~
                      evaluating the following, which will either cause an ~
                      error (with a potentially helpful message) or will ~
                      provide an appropriate term to use:~|~%  ~x0~|"
                     `(translate ',term t t t 'top-level (w state) state))
                 (mv t nil state nil)))))

(defthm correctness-of-strengthen-cl3
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (strengthen-cl3 cl term state)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(defthm test-strengthen-cl3
  (equal y y)
  :hints (("Goal"
           :instructions
           ((:prove
             :hints (("Goal" 
                      :clause-processor
                      (strengthen-cl3 clause '(equal x x) state)))))))
  :rule-classes nil)

(assert-event
 (equal (sort-symbol-listp
         (car (global-val 'proof-supporters-alist (w state))))
        '(STRENGTHEN-CL3 TEST-STRENGTHEN-CL3)))

; End of tests of the return of summary-data.

(must-fail ; need clauses-result
 (defthm correctness-of-strengthen-cl-bad
   (implies (and (pseudo-term-listp cl)
                 (alistp a)
                 (evl (conjoin-clauses
                       (strengthen-cl cl term state))
                      a))
            (evl (disjoin cl) a))
   :rule-classes :clause-processor))

(defun strengthen-cl1 (cl)
  (declare (xargs :guard t))
  (list (cons (list 'not '(equal x x))
              cl)
        (list '(equal x x))))

(defthm correctness-of-strengthen-cl1
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (strengthen-cl1 cl))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(defthm test3
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (strengthen-cl1 clause))))

(defthm test4
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           strengthen-cl1)))

(defthm test5
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (:function strengthen-cl1))))

(must-fail
 (thm
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (:function strengthen-cl1 :hint nil)))))

(defun strengthen-cl-program (cl term state)
  (declare (xargs :stobjs state :mode :program))
  (let ((ctx 'strengthen-cl-program))
    (er-let* ((tterm (translate term t t t ctx (w state) state)))
             (value (list (cons (fcons-term* 'not tterm)
                                cl)
                          (list tterm))))))

(must-fail ; not a known function symbol
 (define-trusted-clause-processor
   abcd
   nil
   :ttag my-ttag))

(must-fail ; non-true-listp supporters
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
  ()
  (define-trusted-clause-processor
    strengthen-cl-program
    car
    :ttag my-ttag)))

(must-fail ; supporters has symbol that is not a known function symbol
 (define-trusted-clause-processor
   strengthen-cl-program
   (abcd binary-append efgh)
   :ttag my-ttag))

(must-fail ; :doc but no :label
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
  ()
  (define-trusted-clause-processor
    strengthen-cl-program
    nil
    :doc "howdy"
    ;;; :label some-label
    :ttag my-ttag)))

(must-succeed ; ttag is there, even though not in macro call
 (encapsulate
  ()
  (defttag my-ttag)
  (define-trusted-clause-processor
    strengthen-cl-program
    nil)))

(must-fail ; no ttag
 (define-trusted-clause-processor
   strengthen-cl-program
   nil))

(define-trusted-clause-processor
  strengthen-cl-program
  nil
  :label strengthen-cl-program-cl-proc
;;; The following legacy doc string was replaced Nov. 2014 by the
;;; defxdoc form just below.
; :doc
; ":Doc-Section clause-processor
;
; example of a trusted (unverified) goal-level simplifier~/
;
; Documentation remains to be written.~/~/"

  :ttag my-ttag)

(include-book "xdoc/top" :dir :system)

(defxdoc strengthen-cl-program-cl-proc
  :parents (clause-processor)
  :short "example of a trusted (unverified) goal-level simplifier"
  :long "Documentation remains to be written.")

(must-fail ; not a symbol
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
  ()
  (define-trusted-clause-processor
    (strengthen-cl-program)
    nil
    :ttag my-ttag)))

(defmacro my-equal (x y)
  `(equal ,x ,y))

(defthm test6
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (strengthen-cl-program clause '(my-equal x x) state))))

(defun strengthen-cl-program2 (cl term state)
  (declare (xargs :stobjs state :mode :program))
  (let ((ctx 'strengthen-cl-program))
    (er-let* ((tterm (translate term t t t ctx (w state) state)))
             (value (list (cons (fcons-term* 'not tterm)
                                cl)
                          (list tterm))))))

(must-fail ; empty signature in :partial-theory
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
  ()
  (define-trusted-clause-processor
    strengthen-cl-program2
    nil
    :partial-theory (encapsulate ()
                                 (defthm my-car-cons
                                   (equal (car (cons x y)) x)))
    :ttag my-ttag)))

(must-fail
 (partial-encapsulate ; empty signature
  ()
  nil
  (defthm my-car-cons
    (equal (car (cons x y)) x))))

(must-fail ; no sub-events of encapsulate
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
  ()
  (define-trusted-clause-processor
    strengthen-cl-program2
    nil
    :partial-theory (encapsulate ((f0 (x) t)))
    :ttag my-ttag)))

(must-fail
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
   ()
   (partial-encapsulate ; no sub-events
    ((f0 (x) t))
    nil)))

(must-fail ; non true-listp sub-events of encapsulate
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
  ()
  (define-trusted-clause-processor
    strengthen-cl-program2
    nil
    :partial-theory (encapsulate ((f0 (x) t)) (local (defun f0 (x) x)) . 3)
    :ttag my-ttag)))

(must-fail    ; non true-listp sub-events of encapsulate
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
   ()
   (partial-encapsulate
    ((f0 (x) t))
    (local (defun f0 (x) x))
    . 3)))

(must-fail
; nested non-trivial encapsulates around the table event, so no unique promised
; encapsulate
 (encapsulate
  ((g0 (x) t))
  (local (defun g0 (x) x))
  (define-trusted-clause-processor
    strengthen-cl-program2
    nil
    :partial-theory (encapsulate ((f0 (x) t))
                                 (local (defun f0 (x) x))
                                 (defthm f0-prop
                                   (implies (integerp x)
                                            (integerp (f0 x)))))
    :ttag my-ttag)))

(must-fail
; nested non-trivial encapsulate around partial-encapsulate
 (encapsulate
   ((g0 (x) t))
   (local (defun g0 (x) x))
   (partial-encapsulate
    ((f0 (x) t))
    nil
    (local (defun f0 (x) x))
    (defthm f0-prop
      (implies (integerp x)
               (integerp (f0 x)))))))

(must-fail ; partial encapsulate introduces something not in its signature
 (define-trusted-clause-processor
   strengthen-cl-program2
   nil
   :partial-theory (encapsulate ((f0 (x) t))
                                (local (defun f0 (x) x))
                                (defun g (x) x)
                                (defthm f0-prop
                                  (implies (integerp x)
                                           (integerp (f0 x)))))
   :ttag my-ttag))

(must-fail ; partial encapsulate introduces something not in its signature
 (partial-encapsulate
  ((f0 (x) t))
  nil
  (local (defun f0 (x) x))
  (defun g (x) x)
  (defthm f0-prop
    (implies (integerp x)
             (integerp (f0 x))))))

(encapsulate ; just to check that empty signature isn't a problem
 ()
 (define-trusted-clause-processor
   strengthen-cl-program2
   (f0)
   :partial-theory (encapsulate ((f0 (x) t))
                                (local (defun f0 (x) x))
                                (defthm f0-prop
                                  (implies (integerp x)
                                           (integerp (f0 x)))))
   :ttag my-ttag))

; redundant
(define-trusted-clause-processor
  strengthen-cl-program2
  (f0)
  :partial-theory (encapsulate ((f0 (x) t))
                    (local (defun f0 (x) x))
                    (defthm f0-prop
                      (implies (integerp x)
                               (integerp (f0 x)))))
  :ttag my-ttag)

(defthm test7
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (strengthen-cl-program2 clause '(my-equal x x) state))))

; The :clause-processor rule correctness-of-strengthen-cl-a below should
; cause an error since the evaluators have unknown constraints.

(defun strengthen-cl-program3 (cl term state)
  (declare (xargs :stobjs state :mode :program))
  (let ((ctx 'strengthen-cl-program))
    (er-let* ((tterm (translate term t t t ctx (w state) state)))
             (value (list (cons (fcons-term* 'not tterm)
                                cl)
                          (list tterm))))))

; The following illustrates a way to get around the requirement that the
; :partial-theory must be an encapsulate form.  It also illustrates the
; constraint message, which talks about an "unknown constraint" and "introduces
; dependent clause processor STRENGTHEN-CL-PROGRAM3".
(make-event
 (er-let*
  ((encap
    (trans1 '(defevaluator ev2 ev2-list
               ((if x y z) (length x) (member-equal x y) (equal x y)
                (not x))
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (skip checks so that we get an encapsulate form).]
               :skip-checks t))))
  (value
   `(define-trusted-clause-processor
      strengthen-cl-program3
      nil
      :partial-theory ,encap
      :ttag my-ttag))))

(defun strengthen-cl-a (cl term state)
  (declare (xargs :stobjs state))
; sad that we can't translate term first
  (cond ((pseudo-termp term) ; sad that we can't use termp!
         (value (list (cons (list 'not term)
                            cl)
                      (list term))))
        (t ; sad that we can't use (er soft ...)
         (prog2$ (cw "~%ERROR: Strengthen-cl was supplied an alleged term ~
                      that is not a term in the current ACL2 world.  Consider ~
                      evaluating the following, which will either cause an ~
                      error (with a potentially helpful message) or will ~
                      provide an appropriate term to use:~|~%  ~x0~|"
                     `(translate ',term t t t 'top-level (w state) state))
                 (mv t nil state)))))

(must-fail
; Ev2 is constrained by (unknown) theory of dependent clause processor,
; strengthen-cl-program3.
 (defthm correctness-of-strengthen-cl-a
   (implies (and (pseudo-term-listp cl)
                 (alistp a)
                 (ev2 (conjoin-clauses
                       (clauses-result (strengthen-cl-a cl term state)))
                      a))
            (ev2 (disjoin cl) a))
   :rule-classes :clause-processor))

; Should fail because we have already introduced this clause processor.

(must-fail
 (define-trusted-clause-processor
   strengthen-cl-program2
   nil
   :partial-theory (encapsulate ((f1 (x) t))
                                (local (defun f1 (x) x))
                                (defthm f1-prop
                                  (implies (integerp x)
                                           (integerp (f1 x)))))
   :ttag my-ttag))

(defun g0 (x)
  (declare (xargs :guard t))
  (f0 x))

(defun strengthen-cl-b (cl term state)
  (declare (xargs :stobjs state))
  (if (g0 cl)
      (value (list cl))
    (value (list (cons (list 'not term)
                       cl)
                 (list term)))))

; F0, supporting g0, is constrained by strengthen-cl-b, which has unknown
; constraints from dependent clause-processor strengthen-cl-program2.  However,
; we do know that f0 is the only direct supporter of strengthen-cl-b.
(defthm correctness-of-strengthen-cl-b
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (strengthen-cl-b cl term state)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(defun strengthen-cl-c (cl term state)
  (declare (xargs :stobjs state :guard (consp term)))
  (value (list (cons (list 'not term)
                     cl)
               (list term))))

(must-fail
; Guard for strengthen-cl-c isn't implied by pseudo-termp and stobj
; assumptions.
 (defthm correctness-of-strengthen-cl-c
   (implies (and (pseudo-term-listp cl)
                 (alistp a)
                 (evl (conjoin-clauses
                       (clauses-result (strengthen-cl-c cl term state)))
                      a))
            (evl (disjoin cl) a))
   :rule-classes :clause-processor))

(defun strengthen-cl-d (cl)
; guard not verified in this example
  (list cl))

(defthm correctness-of-strengthen-cl-d
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (strengthen-cl-d cl))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

; Silly example: Check that we don't if clause-processor returns clause
; unchanged.
(defthm correctness-of-strengthen-cl-d-test
  (equal (car (cons x y)) x)
  :hints (("Goal" :clause-processor strengthen-cl-d))
  :rule-classes nil)

(defun strengthen-cl-e (cl term state)
  (declare (xargs :stobjs state :guard (pseudo-term-listp cl)))
  (value (list (cons (list 'not term)
                     cl)
               (list term))))

; Test that we are using pseudo-term-listp rather than pseudo-termp for
; :clause-processor rules (as opposed to :meta rules).
(defthm correctness-of-strengthen-cl-e
   (implies (and (pseudo-term-listp cl)
                 (alistp a)
                 (evl (conjoin-clauses
                       (clauses-result (strengthen-cl-e cl term state)))
                      a))
            (evl (disjoin cl) a))
   :rule-classes :clause-processor)

(defun strengthen-cl-f (cl)
; returns invalid list of clauses, but extra atom can only strengthen proof
; obligation for subgoals, so this is still sound
  (list cl 'a))

(defthm correctness-of-strengthen-cl-f
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (strengthen-cl-f cl))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(must-fail ; invalid list of clauses returned
 (defthm correctness-of-strengthen-cl-f-test
   (equal (car (cons x y)) x)
   :hints (("Goal" :clause-processor strengthen-cl-f))
   :rule-classes nil))

; Start: Functional instantiation is defeated when we are unable to compute the
; constraints.

; First, a successful functional instantiation.

(encapsulate
 ((f2 (x) t))
 (local (defun f2 (x) x))
 (defthm f2-prop
   (implies (integerp x)
            (integerp (f2 x)))))

(defthm f2-thm
  (implies (integerp x)
           (integerp (f2 (f2 x)))))

(defun add1 (x)
  (1+ x))

(defthm add1-thm
  (implies (integerp x)
           (integerp (add1 (add1 x))))
  :hints (("Goal" :by (:functional-instance f2-thm
                                            (f2 add1)))))

(defthm f0-thm
  (implies (integerp x)
           (integerp (f0 (f0 x)))))

(must-fail ; not able to determine constraints on f0
 (defthm add1-thm-failure
   (implies (integerp x)
            (integerp (add1 (add1 x))))
   :hints (("Goal" :by (:functional-instance f0-thm
                                             (f0 add1))))))

; End: Functional instantiation is defeated when we are unable to compute the
; constraints.

; Test that we allow local include-book events with meta rules and evaluators
; inside non-trivial encapsulates.

(encapsulate
 ((f3 (x) t))
 (local (defun f3 (x) x))
 (local (include-book "arithmetic/top-with-meta" :dir :system)))

; Test that we disallow evaluators in support of defaxioms.

(must-fail
 (progn

   (defstub stub (x) t)

   (defaxiom stub-axiom
     (evl (stub x) a))

   (defthm correctness-of-cl-proc-after-axiom
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (evl (conjoin-clauses
                         (clauses-result (strengthen-cl cl term state)))
                        a))
              (evl (disjoin cl) a))
     :rule-classes :clause-processor)))

; Test that we disallow evaluators in support of metafunctions.

(defun strengthen-cl-g (cl)
  (if (evl *t* nil)
      cl
    (cons '(a) cl)))

(must-fail
 (defthm correctness-of-cl-proc-with-ev-supporting-metafn
   (implies (and (pseudo-term-listp cl)
                 (alistp a)
                 (evl (conjoin-clauses (strengthen-cl-g cl))
                      a))
            (evl (disjoin cl) a))
   :rule-classes :clause-processor))

; Test that all return values after the first two must be stobjs.

; Good version:

(make-event
 (progn
   (defun strengthen-cl-h (cl hint state)
     (declare (xargs :stobjs state))
     (declare (ignore hint))
     (mv nil (list '(a) cl) state))

   (defthm correctness-of-strengthen-cl-with-non-stobj-output
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (evl (conjoin-clauses
                         (clauses-result (strengthen-cl-h cl hint state)))
                        a))
              (evl (disjoin cl) a))
     :rule-classes :clause-processor)

   (value-triple '(value-triple nil)
                 :on-skip-proofs t)))

; Bad version:

(must-fail
 (progn
   (defun strengthen-cl-h (cl hint state)
     (declare (xargs :stobjs state))
     (mv nil (list '(a) cl) hint state))

   (defthm correctness-of-strengthen-cl-with-non-stobj-output
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (evl (conjoin-clauses
                         (clauses-result (strengthen-cl-h cl hint state)))
                        a))
              (evl (disjoin cl) a))
     :rule-classes :clause-processor)

   (value-triple '(value-triple nil))))

; Different error (nil not a variable in user-hint position):

(must-fail
 (progn
   (defun strengthen-cl-h (cl hint state)
     (declare (xargs :stobjs state))
     (declare (ignore hint))
     (mv nil (list '(a) cl) state))

   (defthm correctness-of-strengthen-cl-with-non-stobj-output
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (evl (conjoin-clauses
                         (clauses-result (strengthen-cl-h cl nil state)))
                        a))
              (evl (disjoin cl) a))
     :rule-classes :clause-processor)

   (value-triple '(value-triple nil))))

; Different error (duplicate variables):

(must-fail
 (progn
   (defun strengthen-cl-h (cl hint state)
     (declare (xargs :stobjs state))
     (declare (ignore hint))
     (mv nil (list '(a) cl) state))

   (defthm correctness-of-strengthen-cl-with-non-stobj-output
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (evl (conjoin-clauses
                         (clauses-result (strengthen-cl-h cl cl state)))
                        a))
              (evl (disjoin cl) a))
     :rule-classes :clause-processor)

   (value-triple '(value-triple nil))))

; Different error (alist variable is argument to cl-proc):

(must-fail
 (progn
   (defun strengthen-cl-h (cl hint state)
     (declare (xargs :stobjs state))
     (declare (ignore hint))
     (mv nil (list '(a) cl) state))

   (defthm correctness-of-strengthen-cl-with-non-stobj-output
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (evl (conjoin-clauses
                         (clauses-result (strengthen-cl-h cl a state)))
                        a))
              (evl (disjoin cl) a))
     :rule-classes :clause-processor)

   (value-triple '(value-triple nil))))

; Test generalizing alist.  (This example is referenced in :doc
; clause-processor.)

; In this example we illustrate generalization.  A more interesting example
; would take a "user hint" argument that is the term to generalize, perhaps
; together with the variable to generalize it to.  The variable could actually
; be computed, though, for example as follows:

#||
   ACL2 !>(genvar 'genvar ; this time, a symbol in the "ACL2" package
                   "X" ; prefix
                   0   ; root
                   ;; avoid-lst from clause
                   (all-vars1-lst '((not (foo x0)) (bar x1) (g x3))
                                  nil ; accumulator
                                  )
                   )
   X2
   ACL2 !>
||#

; Anyhow, here we do something much simpler: when a clause has a single literal
; that is a call of function f4, replace that literal by (f4 y).  This isn't
; sound in general, of course; but here, it's OK because f4 is constrained to
; return a non-nil value.

(encapsulate
 ((f4 (x) t))
 (local (defun f4 (x) (cons x x)))
 (defthmd f4-prop
   (f4 x)))

(defevaluator ev3 ev3-list
  ((f4 x)))

(defun gen-cl (cl)
; Replace clause cl by a list of clauses whose validity implies the validity of
; cl.
  (case-match cl
    ((('f4 &))
     '(((f4 y))))
    (& (list cl))))

(defun gen-cl-alist (cl a)
; The value of clause cl, with respect to binding alist a, corresponds to the
; value of clause list (gen-cl cl) with respect to binding list (gen-cl-alist
; cl a).  Since gen-cl maps the clause containing unique literal (f4 term) to a
; singleton clause containing (f4 y), this new binding alist should map y to
; the value of term in the given alist, a.
  (case-match cl
    ((('f4 term))
     (list (cons 'y (ev3 term a))))
    (& a)))

; Now unlike the typical :clause-processor rule, here the ev3 hypothesis uses
; the generalizing binding alist, (gen-cl-alist cl a), in place of the given
; binding alist, a.
(defthm correctness-of-gen-cl
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (ev3 (conjoin-clauses (gen-cl cl))
                     (gen-cl-alist cl a)))
           (ev3 (disjoin cl) a))
  :hints (("Goal" :in-theory (enable f4-prop)))
  :rule-classes :clause-processor)

; Since f4-prop is disabled, this next rule will be the only way to rewrite a
; call of f4 to t.  So the next theorem, f4-test, tests that the expected
; generalization really is taking place to produce the clause containing single
; literal (f4 y).


(defthm f4-prop-restricted
  (implies (syntaxp (eq x 'y))
           (f4 x))
  :hints (("Goal" :in-theory (enable f4-prop))))

(must-fail ; Hint needs to be on "Goal'", not "Goal".
 (defthm f4-test
   (car (cons (f4 (+ u v)) w))
   :hints (("Goal" :clause-processor (:function gen-cl)))))

(defthm f4-test
  (car (cons (f4 (+ u v)) w))
  :hints (("Goal'" :clause-processor (:function gen-cl))))

; End of "Test generalizing alist" example.

; Let's try user-defined stobjs and then look at the error message about
; non-executability.

(defstobj st fld)

(defun cl-proc-st (cl hint st)
  (declare (xargs :stobjs st) (ignore hint))
  (mv nil (list cl) st))

; Proves:
(defthm correctness-of-cl-proc-st
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (ev3 (conjoin-clauses
                      (clauses-result
                       (cl-proc-st cl hint st)))
                     a))
           (ev3 (disjoin cl) a))
  :rule-classes :clause-processor)

(must-fail ; state instead of st
 (defthm correctness-of-cl-proc-st-failure
   (implies (and (pseudo-term-listp cl)
                 (alistp a)
                 (ev3 (conjoin-clauses
                       (clauses-result
                        (cl-proc-st cl hint state)))
                      a))
            (ev3 (disjoin cl) a))
   :rule-classes :clause-processor))

; Let's see the proof proceed if there's no change from the clause processor.
; While we're at it, check that macro alias is OK.

(defun trivial-cl-proc (cl)
  (list cl))

(defthm correctness-of-trivial-cl-proc
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (ev3 (conjoin-clauses
                      (trivial-cl-proc cl))
                     a))
           (ev3 (disjoin cl) a))
  :rule-classes :clause-processor)

(defmacro trivial-cl-proc-macro (x)
  `(trivial-cl-proc ,x))

; OK, even without macro alias
(defthm cl-proc-no-change
  (equal x x)
  :hints (("Goal" :clause-processor trivial-cl-proc-macro))
  :rule-classes nil)

; OK, even without macro alias
(defthm cl-proc-no-change-2
  (equal x x)
  :hints (("Goal" :clause-processor (:function trivial-cl-proc-macro)))
  :rule-classes nil)

; Now let's get some failures due to bad hints.

(must-fail ; non-symbol atom for :clause-processor
 (defthm my-failure
   (equal x x)
   :hints (("Goal" :clause-processor 3))
   :rule-classes nil))

(must-fail ; non-symbol atom for :clause-processor
 (defthm my-failure
   (equal x x)
   :hints (("Goal" :clause-processor (:function 3)))
   :rule-classes nil))

(must-fail ; non-true-listp cons for :clause-processor
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
  ()
  (defthm my-failure
    (equal x x)
    :hints (("Goal" :clause-processor (trivial-cl-proc . 3)))
    :rule-classes nil)))

(must-fail ; consp for :clause-processor :function
 (defthm my-failure
   (equal x x)
   :hints (("Goal" :clause-processor (:function (trivial-cl-proc))))
   :rule-classes nil))

(must-fail ; non-executable :clause-processor hint
 (defthm my-failure
   (equal x x)
   :hints (("Goal" :clause-processor (trivial-cl-proc (car (mv clause nil)))))
   :rule-classes nil))

(defmacro my-id (x)
  x)

(must-fail ; translates to atom
 (defthm my-failure
   (equal x x)
   :hints (("Goal" :clause-processor (my-id clause)))
   :rule-classes nil))

(must-fail ; free variable cl (expected clause)
 (defthm my-failure
   (equal x x)
   :hints (("Goal" :clause-processor (trivial-cl-proc cl)))
   :rule-classes nil))

; Unknown constraints in a defaxiom were prohibited through Version 3.6.1 of
; ACL2.  However, now that we use the supporters of a dependent
; clause-processor to determine ancestors, there is no longer that problem.
(defaxiom formerly-bad
  (true-listp (strengthen-cl-b cl term state))
  :rule-classes nil)

(must-fail ; :partial-theory must be an encapsulate
 (encapsulate ; hard error thrown below defeats must-fail without encapsulate
  ()
  (define-trusted-clause-processor
    strengthen-cl-program2
    nil
    :partial-theory (car nil)
    :ttag my-ttag)))

; Non-executable clause-processors were illegal, but that is no longer the case
; starting with v4-0 because we want to support attachments.

(defun-nx trivial-cl-proc-nonexec (cl)
  (list cl))

(encapsulate
 ()
 (local
  (defthm correctness-of-trivial-cl-proc-nonexec
    (implies (and (pseudo-term-listp cl)
                  (alistp a)
                  (ev3 (conjoin-clauses
                        (trivial-cl-proc-nonexec cl))
                       a))
             (ev3 (disjoin cl) a))
    :rule-classes :clause-processor)))

(defun-nx strengthen-cl-nonexec (cl term)
; sad that we can't translate term first
  (cond ((pseudo-termp term) ; sad that we can't use termp!
         (list (cons (list 'not term)
                     cl)
               (list term)))
        (t ; sad that we can't use (er soft ...)
         (prog2$ (cw "~%NO CHANGE: Strengthen-cl was supplied an alleged term ~
                      that is not a term in the current ACL2 world.  Consider ~
                      evaluating the following, which will either cause an ~
                      error (with a potentially helpful message) or will ~
                      provide an appropriate term to use:~|~%  ~x0~|"
                     `(translate ',term t t t 'top-level (w state) state))
                 (list cl)))))

(encapsulate
 ()
 (local ; non-executable is OK starting with v4-0
  (define-trusted-clause-processor
    strengthen-cl-nonexec
    nil
    :ttag my-ttag)))

; Now verify the original (trusted) clause processor.

(defevaluator evl0 evl0-list
  ((if x y z) (length x) (not x)))

(defthm correctness-of-note-fact-clause-processor
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl0 (conjoin-clauses
                       (note-fact-clause-processor cl term))
                      a))
           (evl0 (disjoin cl) a))
  :rule-classes :clause-processor)

(must-succeed
 (thm (equal (car (cons x y))
             x)
      :hints (("Goal"
               :clause-processor
               (note-fact-clause-processor clause '(equal a a))))))

; Test errors.

(defun er-clause-processor (cl hint state)
  (declare (xargs :stobjs state))
; Let's check that the clauses-result is irrelevant for non-nil error.
  (mv hint
      (if hint
          (list *true-clause*)
        (list cl))
      state))

(defthm correctness-of-er-clause-processor
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl0 (conjoin-clauses
                       (clauses-result
                        (er-clause-processor cl term state)))
                      a))
           (evl0 (disjoin cl) a))
  :rule-classes :clause-processor)

(defthm er-clause-processor-hint-successful-test
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (:function er-clause-processor :hint nil))))

(must-fail
 (defthm er-clause-processor-hint-failure
   (equal (car (cons x y))
          x)
   :hints (("Goal"
            :clause-processor
            (:function er-clause-processor :hint t)))))

(must-fail
 (defthm er-clause-processor-hint-failure
   (equal (car (cons x y))
          x)
   :hints (("Goal"
            :clause-processor
            (:function er-clause-processor :hint "Ouch")))))

(must-fail
 (defthm er-clause-processor-hint-failure
   (equal (car (cons x y))
          x)
   :hints (("Goal"
            :clause-processor
            (:function
             er-clause-processor
             :hint
             (msg "Ouch ~@0"
                  (msg "Bummer: ~x0 ~x1"
                       'foo 'bar)))))))

; Check untouchables etc.

(defun forbidden-clause-processor (cl)
  (list (cons (list 'if *t* *nil* '(equal (big-n) x))
              cl)))

(defthm correctness-of-forbidden-clause-processor
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl0 (conjoin-clauses
                       (forbidden-clause-processor cl))
                      a))
           (evl0 (disjoin cl) a))
  :rule-classes :clause-processor)

(must-fail
 (thm (equal x x)
      :hints (("Goal"
               :clause-processor
               (:function forbidden-clause-processor)))))

(defttag my-ttag)
(set-skip-meta-termp-checks (forbidden-clause-processor))
(defttag nil)

(must-succeed
 (thm (equal x x)
      :hints (("Goal"
               :clause-processor
               (:function forbidden-clause-processor)))))

; Let's conclude with various tests for the case that the hint is a symbol.

(defun cl-3-3 (cl term state)
  (declare (xargs :stobjs state)
           (ignore term))
  (value (list cl)))

(defthm correctness-of-cl-3-3
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (cl-3-3 cl term state)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor cl-3-3))))

(defstobj st fld)

(defun cl-3-4 (cl term state st)
  (declare (xargs :stobjs (state st))
           (ignore term))
  (mv nil (list cl) st state))

(defthm correctness-of-cl-3-4
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (cl-3-4 cl term state st)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor cl-3-4))))

(defmacro cl-3-4-mac (cl term)
  `(cl-3-4 ,cl ,term state st))

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor cl-3-4-mac))))

(defun cl-3-2 (cl term state)
  (declare (xargs :stobjs state)
           (ignore term state))
  (mv nil (list cl)))

(defthm correctness-of-cl-3-2
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (cl-3-2 cl term state)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor cl-3-2))))

(defmacro cl-3-2-mac (cl term)
  `(cl-3-2 ,cl ,term state))

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor cl-3-2-mac))))

(defun cl-2-1 (cl term)
  (declare (ignore term))
  (mv nil (list cl)))

(defthm correctness-of-cl-2-1
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (cl-2-1 cl term)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor cl-2-1))))

(defmacro cl-2-1-mac (cl term)
  `(cl-2-1 ,cl ,term))

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor cl-2-1-mac))))

(defmacro cl-2-1-mac-alt (cl &optional term)
  `(cl-2-1 ,cl ,term))

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor cl-2-1-mac-alt))))

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor (cl-2-1-mac-alt clause 'xyz)))))

(must-succeed
 (thm (equal x x)
  :hints (("Goal" :clause-processor (cl-2-1-mac-alt clause clause)))))

(partial-encapsulate
 ((f-partial (x) t))
 (nth)
 (local (defun f-partial (x) (declare (xargs :guard t)) (consp x)))
 (defthm booleanp-f-partial (booleanp (f-partial x))))

(assert-event
 (equal (getpropc 'f-partial 'constraint-lst)
        '(:UNKNOWN-CONSTRAINTS BOOLEANP F-PARTIAL NTH)))

(defthm booleanp-f-partial-again
  (booleanp (f-partial y))
  :hints (("Goal" :by booleanp-f-partial)))

(encapsulate
 ((g-partial (x) t))
 (local (defun g-partial (x) (declare (xargs :guard t)) (consp x)))
 (defthm booleanp-g-partial (booleanp (g-partial x))))

(must-fail ; fails because f-partial has unknown-constraints
 (defthm booleanp-g-partial-again
   (booleanp (g-partial y))
   :hints (("Goal" :by (:functional-instance booleanp-f-partial-again
                                             (f-partial g-partial))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The following are variants of
;   (defun strengthen-cl-program2 ...)
;   (define-trusted-clause-processor strengthen-cl-program2 ...)
;   (defthm test7 ... :clause-processor ...)
; where we separate out the :partial-theory into a separate
; partial-encapsulate.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; First, simply separate out the partial-encapsulate from the
;;; define-trusted-clause-processor event.

(defun cl-proc1 (cl term state)
  (declare (xargs :stobjs state :mode :program))
  (let ((ctx 'strengthen-cl-program))
    (er-let* ((tterm (translate term t t t ctx (w state) state)))
             (value (list (cons (fcons-term* 'not tterm)
                                cl)
                          (list tterm))))))

(partial-encapsulate
 ((h1 (x) t))
 nil ; could be (h1)
 (local (defun h1 (x) x))
 (defthm h1-prop
   (implies (integerp x)
            (integerp (h1 x)))))

(define-trusted-clause-processor cl-proc1
  (h1)
  :ttag my-ttag)

(defthm cl-proc1-test
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (cl-proc1 clause '(my-equal x x) state))))

;;; Now further separate things out so that we have an ordinary encapsulate
;;; with a somewhat-buried table event that makes it, in essence, a
;;; partial-encapsulate.

(defun cl-proc2 (cl term state)
  (declare (xargs :stobjs state :mode :program))
  (let ((ctx 'strengthen-cl-program))
    (er-let* ((tterm (translate term t t t ctx (w state) state)))
             (value (list (cons (fcons-term* 'not tterm)
                                cl)
                          (list tterm))))))

(encapsulate
 ((h2 (x) t))
 (local (defun h2 (x) x))
 (encapsulate ; just bury the table event below a bit
   ()
   (set-unknown-constraints-supporters))
 (defthm h2-prop
   (implies (integerp x)
            (integerp (h2 x)))))

(define-trusted-clause-processor cl-proc2
  (h2)
  :ttag my-ttag)

(defthm cl-proc2-test
  (equal (car (cons x y))
         x)
  :hints (("Goal"
           :clause-processor
           (cl-proc2 clause '(my-equal x x) state))))

;;; Now avoid define-trusted-clause-processor in favor of a table event.  I'm
;;; wrapping this in an encapsulate so that the ttag doesn't get exported.

(encapsulate
  ()
  (defun cl-proc3 (cl term state)
    (declare (xargs :stobjs state :mode :program))
    (let ((ctx 'strengthen-cl-program))
      (er-let* ((tterm (translate term t t t ctx (w state) state)))
        (value (list (cons (fcons-term* 'not tterm)
                           cl)
                     (list tterm))))))

  (encapsulate
    ((h3 (x) t))
    (local (defun h3 (x) x))
    (encapsulate ; just bury the table event below a bit
      ()
      (set-unknown-constraints-supporters))
    (defthm h3-prop
      (implies (integerp x)
               (integerp (h3 x)))))

  (defttag my-ttag)

  (table trusted-cl-proc-table 'cl-proc3 '(h3))

  (defthm cl-proc3-test
    (equal (car (cons x y))
           x)
    :hints (("Goal"
             :clause-processor
             (cl-proc3 clause '(my-equal x x) state)))))
