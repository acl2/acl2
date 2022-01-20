; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; cert_param: (non-acl2r)

(in-package "JAVA")

(include-book "../types")

(include-book "kestrel/std/system/check-mv-let-call" :dir :system)
(include-book "kestrel/std/system/make-mv-let-call" :dir :system)
(include-book "kestrel/std/system/term-possible-numbers-of-results" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-multiple-values
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          replacement of @(tsee list) calls with @(tsee mv) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "In untranslated terms,
     calls of @(tsee mv) determine when multiple results are produced.
     In translated terms,
     @(tsee mv) is expanded in the same way as @(tsee list),
     and thus the information is somewhat lost.
     However, it can be almost completely recovered with a bit of effort;
     the `almost' means that in some very unlikely and contrived situations
     we may regard a translated term
     that originally (i.e. before being translated)
     returned a single list value
     as a term that returns a multiple value instead,
     but this does not compromise correctness of the generated Java code.")
   (xdoc::p
    "In this pre-translation step,
     we replace certain nests of two or more @(tsee cons)es
     ending in a quoted @('nil'),
     which could be translated @(tsee list) calls if taken in isolation,
     with calls of @(tsee mv).
     Technically this is no longer a valid translated term,
     because @(tsee mv) is a macro,
     but it is a pseudo-term.
     The presence of these @(tsee mv) calls is then recognized,
     and handled appropriately,
     by successive pre-translation steps,
     as well as by the translation step."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-restore-mv-calls-in-term
  :short "Restore @(tsee mv) calls in a translated term."
  :long
  (xdoc::topstring
   (xdoc::p
    "We restore not only @(tsee mv) calls
     returned by multi-result functions,
     but also @(tsee mv) calls that may happen in an @(tsee mv-let)
     in a function that may or may not return multiple results.")
   (xdoc::p
    "At the top level,
     this code is called on the body of a function
     that must be translated to Java.
     In this top-level call,
     we pass as second argument the number of result of the function,
     which is known: see @(tsee atj-restore-mv-calls-in-body).
     As we descend into the term, this number may change.
     When we try to restore @(tsee mv) calls in a term,
     we always know the number of results that the term should return,
     as the @('numres') parameter.")
   (xdoc::p
    "When we encounter a variable,
     we must be expecting one result,
     and in that case we leave the variable unchanged.
     This would not be true for the @('mv') variable
     that results from a translated @(tsee mv-let)
     (see @(tsee check-mv-let-call)),
     but as explained below we process translated @(tsee mv-let)s specially:
     when we reach a variable, it is never that @('mv') variable,
     and so it is always single-valued.")
   (xdoc::p
    "When we encounter a quoted constant,
     we must be expecting one result,
     and in that case we leave the quoted constant unchanged.")
   (xdoc::p
    "Before processing a call,
     we use @(tsee check-mv-let-call) to see if
     the term may be a translated @(tsee mv-let).
     If the term has that form, it is possible, but unlikely,
     that it is not actually a translated @(tsee mv-let).
     In order to properly restore @(tsee mv) calls in the @('mv-term'),
     we need to determine how many results it is expected to return.
     Because of the pre-translation step that removes unused variables,
     this cannot be determined, in general, from the term,
     because some @(tsee mv-nth) calls may have been removed.
     Even if they were all present, it is still possible (though unlikely)
     that the term does not involve multiple values,
     and that it just looks like a translated @(tsee mv-let).
     Thus, we use the @(tsee term-possible-numbers-of-results) utility
     to calculate the number of results of the @('mv-term').
     Recall that this may return two possibilities,
     namely 1 and a number greater than 1:
     in this case, we pick the number greater than 1
     (but it would be also correct to pick 1).
     If instead there is just one possibility, then we obviously use that.
     This value is used as @('numres') to recursively process the @('mv-term'),
     which in general may restore not only @(tsee mv) calls
     at the top level of that term, but also in subterms.
     We also recursively process the @('body-term'),
     this time with the same @('numres') as for the @(tsee mv-let) term.")
   (xdoc::p
    "If the term does not have the form of a translated @(tsee mv-let),
     we check whether it is a translated @(tsee list),
     i.e. a nest of @(tsee cons)es ending with a quoted @('nil').
     If the expected number of results is 1, we leave this term as is,
     i.e. as a single list.
     Otherwise, we replace the term with an @(tsee mv) call.")
   (xdoc::p
    "If the term does not have any of the previous forms,
     we check whether it is a call of @(tsee if).
     In that case, we recursively process the arguments:
     the test must be single-valued,
     while the branches have the same @('numres') as the @(tsee if) call.")
   (xdoc::p
    "We check for @(tsee return-last) for robustness,
     but those have been all removed by a previous pre-translation step.")
   (xdoc::p
    "We treat all other calls as follows.
     We recursively process the arguments,
     each of which must return a single value.
     If the function is a lambda expression,
     we recursively process its body,
     with the same @('numres') as the lambda call."))

  (define atj-restore-mv-calls-in-term ((term pseudo-termp)
                                        (numres posp)
                                        (wrld plist-worldp))
    :returns (new-term pseudo-termp)
    (b* (((unless (mbt (pseudo-termp term))) nil)
         ((when (variablep term))
          (if (= numres 1)
              term
            (raise "Internal error: ~
                    the variable ~x0 cannot return ~x1 results."
                   term numres)))
         ((when (fquotep term))
          (if (= numres 1)
              term
            (raise "Internal error: ~
                    the quoted constant ~x0 cannot return ~x1 results."
                   term numres)))
         ((mv mv-let-callp & vars indices & mv-term body-term)
          (check-mv-let-call term))
         ((when mv-let-callp)
          (b* ((mv-term-numres-list
                (term-possible-numbers-of-results mv-term wrld))
               ((when (null mv-term-numres-list))
                (raise "Internal error: ~
                        the term ~x0 returns no results."
                       mv-term))
               (mv-term-numres (if (= (len mv-term-numres-list) 1)
                                   (car mv-term-numres-list)
                                 (max (first mv-term-numres-list)
                                      (second mv-term-numres-list))))
               (new-mv-term
                (atj-restore-mv-calls-in-term mv-term mv-term-numres wrld))
               (new-body-term
                (atj-restore-mv-calls-in-term body-term numres wrld)))
            (make-mv-let-call 'mv vars indices new-mv-term new-body-term)))
         ((mv list-callp elements) (check-list-call term))
         ((when list-callp)
          (b* (((when (= numres 1)) term)
               ((unless (= (len elements) numres))
                (raise "Internal error: ~
                        the term ~x0 cannot return ~x1 results."
                       term numres)))
            `(mv ,@elements)))
         (fn (ffn-symb term))
         ((when (eq fn 'if))
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3))
               (new-test (atj-restore-mv-calls-in-term test 1 wrld))
               (new-then (atj-restore-mv-calls-in-term then numres wrld))
               (new-else (atj-restore-mv-calls-in-term else numres wrld)))
            `(if ,new-test ,new-then ,new-else)))
         ((when (eq fn 'return-last))
          (raise "Internal error: ~
                  found unexpected call of RETURN-LAST ~x0."
                 term))
         (new-args (atj-restore-mv-calls-in-args (fargs term) wrld))
         ((when (symbolp fn)) (fcons-term fn new-args))
         (new-body (atj-restore-mv-calls-in-term (lambda-body fn) numres wrld))
         (new-fn (make-lambda (lambda-formals fn) new-body)))
      (fcons-term new-fn new-args)))

  (define atj-restore-mv-calls-in-args ((args pseudo-term-listp)
                                        (wrld plist-worldp))
    :returns (new-args (and (pseudo-term-listp new-args)
                            (equal (len new-args) (len args)))
                       :hyp (pseudo-term-listp args))
    (cond ((endp args) nil)
          (t (cons (atj-restore-mv-calls-in-term (car args) 1 wrld)
                   (atj-restore-mv-calls-in-args (cdr args) wrld)))))

  :prepwork ((local
              (in-theory
               (enable acl2::len-of-check-mv-let-call.indices/vars))))

  :verify-guards nil ; done below

  ///

  (local
   (std::deflist pos-listp (acl2::x)
     (posp acl2::x)
     :true-listp t
     :elementp-of-nil nil))

  (defrulel verify-guards-lemma-1
    (implies (> (len (term-possible-numbers-of-results term wrld)) 0)
             (posp (car (term-possible-numbers-of-results term wrld))))
    :disable posp)

  (defrulel verify-guards-lemma-2
    (implies (> (len (term-possible-numbers-of-results term wrld)) 1)
             (posp (cadr (term-possible-numbers-of-results term wrld))))
    :disable posp)

  (defrulel verify-guards-lemma-3
    (implies (posp x)
             (rationalp x)))

  (verify-guards atj-restore-mv-calls-in-term
    :hints (("Goal" :in-theory (disable posp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-restore-mv-calls-in-body ((body pseudo-termp)
                                      (out-types atj-type-listp)
                                      (wrld plist-worldp))
  :returns (new-body pseudo-termp :hyp (pseudo-termp body))
  :short "Restore @(tsee mv) calls in a translated function body."
  :long
  (xdoc::topstring-p
   "This is the top-level call of @(tsee atj-restore-mv-calls-in-term):
    see that function for details.
    We initialize @('numres') with the number of output types
    of the function whose body we are processing.")
  (b* ((numres (len out-types))
       ((unless (> numres 0))
        (raise "Internal error: no output types.")))
    (atj-restore-mv-calls-in-term body (len out-types) wrld)))
