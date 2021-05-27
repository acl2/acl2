; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "programs")
(include-book "evaluation-states")
(include-book "primitive-functions")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ evaluation
  :parents (acl2-programming-language)
  :short "Evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation semantics of ACL2 is formalized here
     in terms of a succession of the evaluation states
     formalized by the fixtype @(tsee eval-state).
     This is a small-step operational semantics,
     from which we could also define a big-step operational semantics
     (by composing the small steps).")
   (xdoc::p
    "A small-step semantics is more flexible than a big-step semantics,
     because it lets us talk about intermediate evaluation states,
     and not just the final states.
     This is particularly important to describe non-terminating executions.
     Also, we can easily derive a big-step semantics from a small-step one,
     but not vice versa.")
   (xdoc::p
    "There are different options for the granularity of the (small) steps.
     The granularity that we formalize here should be adequate,
     but it can be changed if needed or useful."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-from-init ((function symbol-valuep) (arguments value-listp))
  :returns (estate eval-state-p)
  :short "Evaluation step from the initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our formalization, an evaluation sequence starts
     with a call of a named function on some argument values,
     which together form an initial state (see @(tsee eval-state)).
     The first evaluation step, which starts from this initial state,
     is formalized here, given the function symbol and argument values.")
   (xdoc::p
    "This first evaluation step produces
     the first transitional state of the evaluation sequence.
     This transitional state consists of a stack with a single frame
     that contains the empty binding and
     the ground call of the function symbol on the quoted values."))
  (b* ((frame (make-frame :term (tterm-call (tfunction-named function)
                                            (tterm-constant-list arguments))
                          :binding nil))
       (stack (list frame)))
    (eval-state-trans stack))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-leftmost-nonconst ((terms tterm-listp))
  :returns (term? maybe-ttermp)
  :short "Return the leftmost term in a list that is not a quoted constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used as explained in @(tsee step-from-trans).")
   (xdoc::p
    "If there is no such term, we return @('nil').
     Note that @('nil') is not a term in our formalization of terms."))
  (b* (((when (endp terms)) nil)
       (term (car terms))
       ((when (tterm-case term :constant))
        (get-leftmost-nonconst (cdr terms))))
    (tterm-fix term))
  :hooks (:fix)
  ///

  (defruled tterm-case-constant-listp-when-not-get-leftmost-nonconst
    (implies (and (tterm-listp terms)
                  (not (ttermp (get-leftmost-nonconst terms))))
             (tterm-case-constant-listp terms))
    :enable (get-leftmost-nonconst tterm-case-constant-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define put-leftmost-nonconst ((terms tterm-listp) (value valuep))
  :returns (mv (foundp booleanp) (new-terms tterm-listp))
  :short "Replace the leftmost term in a list that is not a quoted constant
          with a quoted constant with the given value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used as explained in @(tsee step-from-trans).")
   (xdoc::p
    "If all the terms in the list are quoted constants,
     no replacement takes place, and the first result is @('nil').
     Otherwise, the first result is @('t'),
     and the second result is the updated list of terms."))
  (b* (((when (endp terms)) (mv nil nil))
       (term (car terms))
       ((when (tterm-case term :constant))
        (b* (((mv foundp new-terms)
              (put-leftmost-nonconst (cdr terms) value))
             ((unless foundp) (mv nil nil)))
          (mv t (cons (tterm-fix term) new-terms)))))
    (mv t (cons (tterm-constant value) (cdr (tterm-list-fix terms)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-primitive-function
  ((name (and (symbol-valuep name)
              (primitive-function-namep name)))
   (arguments value-listp)
   (program programp))
  :returns (result maybe-valuep)
  :short "Call a primitive function on some arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee step-from-trans)
     when encountering a call of a primitive function.")
   (xdoc::p
    "We dispatch based on the primitive function name.
     If the number of arguments does not match the arity,
     we return @('nil').
     Otherwise, we return the value resulting from
     executing the primitive function."))
  (cond
   ((symbol-value-equiv name (lift-symbol 'acl2::acl2-numberp))
    (and (= (len arguments) 1)
         (eval-acl2-numberp (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::rationalp))
    (and (= (len arguments) 1)
         (eval-rationalp (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::integerp))
    (and (= (len arguments) 1)
         (eval-integerp (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::complex-rationalp))
    (and (= (len arguments) 1)
         (eval-complex-rationalp (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::complex))
    (and (= (len arguments) 2)
         (eval-complex (first arguments) (second arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::realpart))
    (and (= (len arguments) 1)
         (eval-realpart (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::imagpart))
    (and (= (len arguments) 1)
         (eval-imagpart (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::numerator))
    (and (= (len arguments) 1)
         (eval-numerator (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::denominator))
    (and (= (len arguments) 1)
         (eval-denominator (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::unary--))
    (and (= (len arguments) 1)
         (eval-unary-- (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::unary-/))
    (and (= (len arguments) 1)
         (eval-unary-/ (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::binary-+))
    (and (= (len arguments) 2)
         (eval-binary-+ (first arguments) (second arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::binary-*))
    (and (= (len arguments) 2)
         (eval-binary-* (first arguments) (second arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::<))
    (and (= (len arguments) 2)
         (eval-< (first arguments) (second arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::characterp))
    (and (= (len arguments) 1)
         (eval-characterp (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::char-code))
    (and (= (len arguments) 1)
         (eval-char-code (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::code-char))
    (and (= (len arguments) 1)
         (eval-code-char (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::stringp))
    (and (= (len arguments) 1)
         (eval-stringp (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::coerce))
    (and (= (len arguments) 2)
         (eval-coerce (first arguments) (second arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::symbolp))
    (and (= (len arguments) 1)
         (eval-symbolp (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::symbol-package-name))
    (and (= (len arguments) 1)
         (eval-symbol-package-name (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::symbol-name))
    (and (= (len arguments) 1)
         (eval-symbol-package-name (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::intern-in-package-of-symbol))
    (and (= (len arguments) 2)
         (eval-intern-in-package-of-symbol (first arguments)
                                           (second arguments)
                                           (program->packages program))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::consp))
    (and (= (len arguments) 1)
         (eval-consp (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::cons))
    (and (= (len arguments) 2)
         (eval-cons (first arguments) (second arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::car))
    (and (= (len arguments) 1)
         (eval-car (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::cdr))
    (and (= (len arguments) 1)
         (eval-cdr (first arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::pkg-imports))
    (and (= (len arguments) 1)
         (eval-pkg-imports (first arguments)
                           (program->packages program))))
   ((symbol-value-equiv name (lift-symbol 'acl2::pkg-witness))
    (and (= (len arguments) 1)
         (eval-pkg-witness (first arguments)
                           (program->packages program))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::equal))
    (and (= (len arguments) 2)
         (eval-equal (first arguments) (second arguments))))
   ((symbol-value-equiv name (lift-symbol 'common-lisp::if))
    (and (= (len arguments) 3)
         (eval-if (first arguments) (second arguments) (third arguments))))
   ((symbol-value-equiv name (lift-symbol 'acl2::bad-atom<=))
    (and (= (len arguments) 2)
         (eval-bad-atom<= (first arguments) (second arguments))))
   (t (impossible)))
  :guard-hints (("Goal" :in-theory (enable primitive-function-namep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-from-trans ((stack stackp) (program programp))
  :returns (estate eval-state-p)
  :short "Evaluation step from a transitional state."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the stack of frames is empty, we go into an error state.
     It should be an invariant that the stack is never empty
     during an evaluation that starts from a suitably well-formed initial state.
     This will be proved formally eventually.")
   (xdoc::p
    "If the stack is not empty, we pick the top frame,
     which is the @(tsee car) in our formalization.
     We look at the term in the frame, which tells us what must be done next.")
   (xdoc::p
    "If the term is a variable, we look it up in the binding of the frame.
     If the variable is unbounded, we go into an error state;
     this should never happen in well-formed evaluations,
     as we plan to prove formally.
     If it is bounded, we quote the value it is bound to
     and replace the variable with that quoted constant in the frame.
     Note that no frame is pushed or popped
     in this evaluation step in this case.")
   (xdoc::p
    "If the term is not a variable,
     it is either a quoted constant
     or a call of a named function or lambda expression.
     We explain the case of the call first,
     and then the case of a quoted constant.")
   (xdoc::p
    "If the term is a call of any function other than @(tsee if)
     (whose treatment is explained later),
     there are two subcases to consider.
     The first subcase is that not all the argument terms of the call
     are quoted constants.
     In this subcase, we push a new frame with
     the leftmost argument term that is not a quoted constant;
     the binding is copied.
     This is because that, in the left-to-right order of evaluation,
     that argument is the one that needs to be evaluated next,
     while the ones that precede it are fully evaluated
     (i.e. they are quoted constants where no further evaluation is possible).
     The second subcase is that all the argument terms are quoted constants.
     In this subcase, all the arguments of the call are fully evaluated
     (i.e. they are quoted constants where no further evaluation is possible),
     and so we need to proceed to evaluate the call itself,
     which we do as follows.
     If the function is a primitive one,
     we run it in one step:
     we use @(tsee call-primitive-function),
     and if it returns @('nil') we go into the error state,
     otherwise we replace the term in the curren frame
     with the quoted result of the primitive function call.
     Note that, in this case, the primitive function is never @(tsee if),
     because that case would have already been handled non-strictly.
     If instead the function is a named one that is not primitive,
     we look up its definition in the program.
     If no definition is found, we go into the error state;
     this will never happen in well-formed evaluations,
     as we plan to prove formally.
     If a definition is found, we push a new frame
     with the body of the definition as term,
     and with a binding that binds
     the values of the quoted constant arguments to the formal parameters.
     If instead the function being called is a lambda expression,
     then we push a new frame
     with the body of the lambda expression as term
     and with a binding that extends the current one with
     the values of the quoted constant arguments bound to the formal parameters.
     Thus the treatment of the lambda expression is not very different
     from the treatment of a named function,
     except that for the latter we need to look up the definition in the program
     while for the former we already have the ``definition'' right there.
     Another difference is in the binding in the pushed frame:
     for a named function, it is a fresh binding,
     while for a lambda expression, it is an update of the current one.
     Lambda expressions are closed in ACL2 translated terms,
     but here we want to be more general, and allow the well-formed evaluation
     of lambda expressions that are not necessarily closed,
     as may result, for instance, from transformations of ACL2 terms.")
   (xdoc::p
    "Note that, as just explained, a frame with a call
     always pushes a new frame,
     whether it is for the leftmost non-quoted-constant argument of the call,
     or for the body of the named function or lambda expression called.
     Successive evaluation steps will operate on the new frame,
     possibly pushing further frames, and so on,
     until the originally pushed frame (if the computation terminates)
     ends up with a quoted constant in it,
     which is the final result of evaluating
     the term in the originally pushed frame.
     This is where a frame with just a quoted constant comes into play,
     whose treatment we describe next
     (recall that, above, we had deferred this explanation).")
   (xdoc::p
    "If the term in a frame is a quoted constant,
     we pop the frame, and incorporate the quoted constant
     into the frame just below, if any.
     If there is no frame just below,
     i.e. the frame with the quoted constant, just popped, was the only one,
     then we go into the final evaluation state,
     which only contains a value, namely the value of the quoted constant.
     This means that the overall computation,
     which started from an initial evaluation state,
     has terminated, and this value is the result.
     If instead there is a frame below, we proceed as follows.
     If the term in the frame below is a variable or quoted constant,
     we go into the error state:
     this will never happen in well-formed evaluations;
     we will prove this formally eventually.
     If instead the term is a call, there are two subcases,
     the same that were described above for pushing a new frame.
     In the first subcase, the call in the frame has a leftmost argument term
     that is not a quoted constant:
     then the frame just popped must have derived from that argument term,
     and thus we replace that argument term with the quoted constant.
     In the second subcase,
     the call in the frame has all quoted constants as arguments:
     the the frame just popped must have derived from the body of the function,
     and thus we replace the whole call with the quoted constant.")
   (xdoc::p
    "A call of @(tsee if) is treated non-strictly.
     If the call has a number of arguments different from 3,
     we go into an error state;
     this will never happen in well-formed evaluations,
     as will be proved eventually.
     If the first argument (i.e. the test) is not a quoted constant,
     it is pushed into a new frame, like any other function argument.
     If instead it is a quoted constant,
     it means that it has been already evaluated,
     or that it does not need to be evaluated.
     Based on whether its value is @('nil') or not,
     we replace the whole @(tsee if) call with the second or third argument,
     which we then proceed to evaluate as any other term,
     in subsequent evaluation steps.
     Thus, the other branch is completely ignored, not evaluated,
     realizing the non-strictness of @(tsee if).")
   (xdoc::p
    "Note that the arguments of functions are evaluated left-to-right.
     This is consistent with "
    (xdoc::ahref
     "https://www.cs.cmu.edu/Groups/AI/html/cltl/clm/node61.html#SECTION00915000000000000000"
     "Section 5.1.5 of ``Common Lisp the Language,  2nd Edition''")
    "."))
  (b* (((when (endp stack)) (eval-state-error))
       (frame (car stack))
       ((frame frame) frame))
    (tterm-case
     frame.term
     :variable
     (b* ((var-val (omap::in frame.term.name frame.binding))
          ((unless (consp var-val)) (eval-state-error))
          (val (cdr var-val))
          (new-frame (change-frame frame :term (tterm-constant val)))
          (new-stack (cons new-frame (cdr stack))))
       (eval-state-trans new-stack))
     :constant
     (b* ((value frame.term.value)
          (stack (cdr stack))
          ((when (endp stack)) (eval-state-final value))
          (frame (car stack))
          ((frame frame) frame))
       (tterm-case
        frame.term
        :variable (eval-state-error)
        :constant (eval-state-error)
        :call
        (b* (((mv foundp arguments)
              (put-leftmost-nonconst frame.term.arguments value))
             (term (if foundp
                       (make-tterm-call :function frame.term.function
                                        :arguments arguments)
                     (tterm-constant value)))
             (frame (change-frame frame :term term))
             (stack (cons frame (cdr stack))))
          (eval-state-trans stack))))
     :call
     (if (tfunction-equiv frame.term.function
                          (tfunction-named (lift-symbol 'acl2::if)))
         (b* (((unless (= (len frame.term.arguments) 3)) (eval-state-error))
              (test (first frame.term.arguments)))
           (if (tterm-case test :constant)
               (b* ((branch (if (value-equiv (tterm-constant->value test)
                                             (value-nil))
                                (third frame.term.arguments)
                              (second frame.term.arguments)))
                    (new-frame (change-frame frame :term branch))
                    (new-stack (cons new-frame (cdr stack))))
                 (eval-state-trans new-stack))
             (eval-state-trans
              (cons (make-frame :term test :binding frame.binding)
                    stack))))
       (b* ((arg? (get-leftmost-nonconst frame.term.arguments)))
         (if (ttermp arg?)
             (eval-state-trans
              (cons (make-frame :term arg? :binding frame.binding)
                    stack))
           (tfunction-case
            frame.term.function
            :named
            (if (primitive-function-namep frame.term.function.name)
                (b* ((args
                      (tterm-constant-list->value-list frame.term.arguments))
                     (value? (call-primitive-function frame.term.function.name
                                                      args
                                                      program)))
                  (if (valuep value?)
                      (eval-state-trans
                       (cons (change-frame frame :term (tterm-constant value?))
                             (cdr stack)))
                    (eval-state-error)))
              (b* ((function? (function-lookup frame.term.function.name
                                               (program->functions program)))
                   ((unless (functionp function?)) (eval-state-error))
                   (params (function->params function?))
                   (body (function->body function?))
                   ((unless (= (len params) (len frame.term.arguments)))
                    (eval-state-error))
                   (args (tterm-constant-list->value-list frame.term.arguments))
                   (binding (omap::from-lists params args)))
                (eval-state-trans
                 (cons (make-frame :term body :binding binding) stack))))
            :lambda
            (b* ((params frame.term.function.parameters)
                 (body frame.term.function.body)
                 ((unless (= (len params) (len frame.term.arguments)))
                  (eval-state-error))
                 (args (tterm-constant-list->value-list frame.term.arguments))
                 (binding (omap::update* (omap::from-lists params args)
                                         frame.binding)))
              (eval-state-trans
               (cons (make-frame :term body :binding binding) stack)))))))))
  :guard-hints (("Goal"
                 :in-theory
                 (enable
                  tterm-case-constant-listp-when-not-get-leftmost-nonconst)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step ((estate eval-state-p) (program programp))
  :guard (not (member-eq (eval-state-kind estate) '(:final :error)))
  :returns (new-estate eval-state-p)
  :short "Evaluation step from any state that is not final or error."
  :long
  (xdoc::topstring
   (xdoc::p
    "No evaluation step may take place from a final or error state.
     Instead, an evaluation step may always take place
     from an initial or transitional state."))
  (eval-state-case estate
                   :init (step-from-init estate.function estate.arguments)
                   :trans (step-from-trans estate.stack program)
                   :final (prog2$ (impossible) (eval-state-fix estate))
                   :error (prog2$ (impossible) (eval-state-fix estate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stepn ((estate eval-state-p) (n natp) (program programp))
  :returns (new-estate eval-state-p)
  :short "Perform at most a given number of evaluation steps."
  :long
  (xdoc::topstring
   (xdoc::p
    "We repeatedly call @(tsee step) until
     either we reach a final or error state
     (from where no further evaluation step may take place)
     or we exhaust the given (maximum) number of steps."))
  (b* (((when (zp n)) (eval-state-fix estate))
       ((when (member-eq (eval-state-kind estate) '(:final :error)))
        (eval-state-fix estate))
       (estate (step estate program)))
    (stepn estate (1- n) program))
  :measure (nfix n)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk terminatingp ((estate eval-state-p) (program programp))
  :returns (yes/no booleanp)
  :short "Check if an evaluation state is terminating."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when a final or error state can be reached
     in a finite number of steps.")
   (xdoc::p
    "This is a non-executable predicate."))
  (exists (n) (and (natp n)
                   (member-eq (eval-state-kind (stepn estate n program))
                              '(:final :error))
                   t)) ; so the result is boolean
  ///

  (fty::deffixequiv-sk terminatingp
    :args ((estate eval-state-p) (program programp)))

  (defrule natp-of-terminatingp-witness-when-terminatingp
    (implies (terminatingp estate program)
             (natp (terminatingp-witness estate program)))
    :rule-classes :type-prescription)

  (defrule terminating-state-is-final-or-error
    (implies (terminatingp estate program)
             (member-equal (eval-state-kind
                            (stepn estate
                                   (terminatingp-witness estate program)
                                   program))
                           '(:final :error)))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum exec-outcome
  :short "Fixtype of execution outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "When attempting to exhaustively perform execution steps,
     there are three possible outcomes:
     (i) a final state is reached, with a final result value;
     (ii) an error state is reached; and
     (iii) execution continues forever.
     Here we capture these possible outcomes."))
  (:terminating ((result value)))
  (:error ())
  (:nonterminating ()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step* ((estate eval-state-p) (program programp))
  :returns (outcome exec-outcome-p)
  :short "Attempt to exhaustively perform execution steps from a state."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the state is terminating,
     then we return either the final result or an error outcome.
     If the state is nonterminating,
     we return the nonterminating outcome.")
   (xdoc::p
    "This function is not executable."))
  (if (terminatingp estate program)
      (b* ((end-estate (stepn estate
                              (terminatingp-witness estate program)
                              program)))
        (eval-state-case
         end-estate
         :init (prog2$ (impossible)
                       (ec-call (exec-outcome-fix :irrelevant)))
         :trans (prog2$ (impossible)
                        (ec-call (exec-outcome-fix :irrelevant)))
         :final (exec-outcome-terminating end-estate.result)
         :error (exec-outcome-error)))
    (exec-outcome-nonterminating))
  :guard-hints (("Goal" :use terminating-state-is-final-or-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-call ((function symbol-valuep)
                   (arguments value-listp)
                   (program programp))
  :returns (outcome exec-outcome-p)
  :short "Execute a call of a function on a list of arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "We create an initial state
     with the function (symbol) and the arguments,
     and we attempt to exhaustively perform execution steps.
     We return the execution outcome.")
   (xdoc::p
    "This function is not executable."))
  (b* ((start-estate (eval-state-init function arguments)))
    (step* start-estate program)))
