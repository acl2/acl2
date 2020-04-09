; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; cert_param: (non-acl2r)

(in-package "JAVA")

(include-book "name-translation")
(include-book "types")

(include-book "kestrel/std/system/all-free-bound-vars" :dir :system)
(include-book "kestrel/std/system/all-vars-open" :dir :system)
(include-book "kestrel/std/system/check-unary-lambda-call" :dir :system)
(include-book "kestrel/std/system/make-mv-let-call" :dir :system)
(include-book "kestrel/std/system/mvify" :dir :system)
(include-book "kestrel/std/system/remove-dead-if-branches" :dir :system)
(include-book "kestrel/std/system/remove-mbe" :dir :system)
(include-book "kestrel/std/system/remove-progn" :dir :system)
(include-book "kestrel/std/system/remove-trivial-vars" :dir :system)
(include-book "kestrel/std/system/remove-unused-vars" :dir :system)
(include-book "kestrel/std/system/term-possible-numbers-of-results" :dir :system)
(include-book "kestrel/std/system/unquote-term" :dir :system)
(include-book "std/alists/remove-assocs" :dir :system)
(include-book "std/strings/symbols" :dir :system)
(include-book "std/typed-alists/symbol-pos-alistp" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)

(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation
  :parents (atj-code-generation)
  :short "Pre-translation performed by ATJ, as part of code generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-code-generation" "here")
    ", prior to generating Java code,
     ATJ performs an ACL2-to-ACL2 pre-translation.
     Currently, this pre-translation consists of the following steps.
     The first three steps apply to both the deep and the shallow embedding;
     the others apply only to the shallow embedding.")
   (xdoc::ol
    (xdoc::li
     "We remove @(tsee return-last).
      See "
     (xdoc::seetopic "atj-pre-translation-remove-return-last" "here")
     ".")
    (xdoc::li
     "We remove dead @(tsee if) branches.
      See "
     (xdoc::seetopic "atj-pre-translation-remove-dead-if-branches" "here")
     ".")
    (xdoc::li
     "We remove the unused lambda-bound variables.
      See "
     (xdoc::seetopic "atj-pre-translation-unused-vars" "here")
     ".")
    (xdoc::li
     "We remove the trivial lambda-bound variables.
      See "
     (xdoc::seetopic "atj-pre-translation-trivial-vars" "here")
     ".")
    (xdoc::li
     "We replace @(tsee list) calls with @(tsee mv) calls
      in functions that return multiple results.
      See "
     (xdoc::seetopic "atj-pre-translation-multiple-values" "here")
     ".")
    (xdoc::li
     "We annotate terms with ATJ type information.
      See "
     (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
     ".")
    (xdoc::li
     "We perform a single-threadedness analysis of the Java primitive arrays,
      but only if @(':guards') is @('t').
      See "
     (xdoc::seetopic "atj-pre-translation-array-analysis" "here")
     ".")
    (xdoc::li
     "We mark the lambda-bound variables
      that can be reused and destructively updated in Java.
      See "
     (xdoc::seetopic "atj-pre-translation-var-reuse" "here")
     ".")
    (xdoc::li
     "We rename variables
      so that their names are valid Java variable names
      and so that different variables with the same name are renamed apart,
      unless they have been marked for reuse in the previous step.
      See "
     (xdoc::seetopic "atj-pre-translation-var-renaming" "here")
     ".")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-remove-return-last
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of @(tsee return-last)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "We selectively remove the @(':logic') or @(':exec') parts of @(tsee mbe)s
     (which are translated to @('(return-last 'mbe1-raw <exec> <logic>)'))
     based on the @(':guards') input.
     We remove all the non-last arguments of @(tsee prog2$)s and @(tsee progn$)s
     (which are translated to @('(return-last 'progn <non-last> <last>)')).")
   (xdoc::p
    "These are the only @(tsee return-last) forms
     that make it through input validation.
     Note that the non-last arguments of @(tsee prog2$) and @(tsee progn$)
     are checked to be free of side effects by ATJ,
     and thus their removal is safe and semantics-preserving."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-return-last ((term pseudo-termp) (guards$ booleanp))
  :returns (new-term pseudo-termp :hyp (pseudo-termp term))
  :short "Remove all the @(tsee return-last)s from a term."
  (b* ((term (if guards$
                 (remove-mbe-logic term)
               (remove-mbe-exec term)))
       (term (remove-progn term)))
    term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-pre-translation-remove-dead-if-branches
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of dead @(tsee if) branches."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "If the test of an @(tsee if) is @('t'),
     we replace the @(tsee if) with the `then' branch;
     if the test of an @(tsee if) is @('nil'),
     we replace the @(tsee if) with the `else' branch.
     Note that the previous translation step
     may turn @(tsee mbt)s in @(tsee if) tests into @('t')s,
     so it is appropriate for this pre-translation step
     to come after the previous one.")
   (xdoc::p
    "We use the @(tsee remove-dead-if-branches) system utility.
     No other code is needed to do this in ATJ.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-unused-vars
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of all the unused lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "We remove all the lambda-bound variables,
     and corresponding actual arguments,
     that are not actually used in the body of the lambda expression.
     This way, we avoid calculating and assigning actual arguments
     that are then discarded.
     Recall that ATJ checks that the ACL2 code to be translated to Java
     is free of side effects:
     thus, this removal is safe and semantics-preserving.")
   (xdoc::p
    "This is accomplished
     via the @(tsee remove-unused-vars) system utility.
     No other code is needed to do this in ATJ.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-trivial-vars
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of all the trivial lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "We remove all the lambda-bound variables,
     and corresponding actual arguments,
     that are identical to the corresponding actual arguments.
     See the discussion in @(tsee remove-trivial-vars),
     which is the utility that we use
     to accomplish this pre-translation step.")
   (xdoc::p
    "This pre-translation step makes terms simpler to work with
     (for the purpose of ATJ)
     by only keeping the ``true'' @(tsee let)s in a term
     (which are lambda expressions in translated terms),
     avoiding the ``artificial'' ones to close the lambda expressions.
     Indeed, @(tsee let) terms are generally not closed in other languages,
     or even in ACL2's untranslated terms.")))

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
     and thus the information is somewhat.
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
                    the quoted constant ~x0 cannot return ~x1 results")))
         ((mv mv-let-callp & vars indices mv-term body-term)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-type-annotation
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          addition of type annotations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "This step annotates ACL2 terms with ATJ types:
     (i) each ACL2 term is wrapped with a function named @('[src>dst]'),
     where @('src') identifies the ATJ types of the term
     and @('dst') identifies ATJ types to which the term must be converted to;
     (ii) each ACL2 variable @('var') in a term is renamed to @('[type]var'),
     where @('type') identifies the ATJ type of the variable.")
   (xdoc::p
    "Both @('src') and @('dst') above identify non-empty lists of ATJ types.
     This is because an ACL2 term may return multiple values (see @(tsee mv)):
     each list consists of two or more ATJ types when he ACL2 term does;
     otherwise, it consists of one ATJ type only.
     The two lists (for @('src') and @('dst')) will always have the same length,
     because ACL2 prevents treating
     single values as multiple values,
     multiple values as single values,
     or multiple values of a certain number
     as multiple values of a different number.
     Non-executable functions relax these restrictions,
     but their body includes calls of @('acl2::throw-nonexec-error'),
     which has raw Lisp code and is currently not whitelisted by ATJ.")
   (xdoc::p
    "These annotations facilitate the ACL2-to-Java translation,
     which uses the type annotations as ``instructions'' for
     (i) which types to declare Java local variables with, and
     (ii) which Java conversion code to insert around expressions.")
   (xdoc::p
    "The annotated terms are still ACL2 terms, but with a specific structure.
     This should let us prove, in the ACL2 logic,
     the equality of the annotated terms with the original terms,
     under suitable variable rebinding,
     and by introducing the @('[src>dst]') functions as identities.
     (This has not been done yet.)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-id ((type atj-typep))
  :returns (id stringp)
  :short "Short string identifying an ATJ type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use a short two-letter string to identify each ATJ type.
     For the @(':acl2') types,
     the first letter is @('A') and the second letter is from the class name.
     For the @(':jprim') types,
     the first letter is @('J') and the second letter is from [JVMS:4.3.2].
     For the @(':jprimarr') types,
     the first letter is @('Y') (which is the ending letter of `array')
     and the second letter is from [JVMS:4.3.2]."))
  (atj-type-case type
                 :acl2 (atj-atype-case type.get
                                       :integer "AI"
                                       :rational "AR"
                                       :number "AN"
                                       :character "AC"
                                       :string "AS"
                                       :symbol "AY"
                                       :cons "AP"
                                       :value "AV")
                 :jprim (primitive-type-case type.get
                                             :boolean "JZ"
                                             :char "JC"
                                             :byte "JB"
                                             :short "JS"
                                             :int "JI"
                                             :long "JJ"
                                             :float "JF"
                                             :double "JD")
                 :jprimarr (primitive-type-case type.comp
                                                :boolean "YZ"
                                                :char "YC"
                                                :byte "YB"
                                                :short "YS"
                                                :int "YI"
                                                :long "YJ"
                                                :float "YF"
                                                :double "YD"))
  :hooks (:fix)
  ///

  (defrule atj-type-id-injective
    (equal (equal (atj-type-id x)
                  (atj-type-id y))
           (atj-type-equiv x y))
    :enable (atj-type-kind
             atj-type-fix
             atj-type-acl2->get
             atj-type-jprim->get
             atj-type-jprimarr->comp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-of-id ((id stringp))
  :returns (type atj-typep)
  :short "ATJ type identified by a short string."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-type-id).")
  (cond ((equal id "AI") (atj-type-acl2 (atj-atype-integer)))
        ((equal id "AR") (atj-type-acl2 (atj-atype-rational)))
        ((equal id "AN") (atj-type-acl2 (atj-atype-number)))
        ((equal id "AC") (atj-type-acl2 (atj-atype-character)))
        ((equal id "AS") (atj-type-acl2 (atj-atype-string)))
        ((equal id "AY") (atj-type-acl2 (atj-atype-symbol)))
        ((equal id "AP") (atj-type-acl2 (atj-atype-cons)))
        ((equal id "AV") (atj-type-acl2 (atj-atype-value)))
        ((equal id "JZ") (atj-type-jprim (primitive-type-boolean)))
        ((equal id "JC") (atj-type-jprim (primitive-type-char)))
        ((equal id "JB") (atj-type-jprim (primitive-type-byte)))
        ((equal id "JS") (atj-type-jprim (primitive-type-short)))
        ((equal id "JI") (atj-type-jprim (primitive-type-int)))
        ((equal id "JJ") (atj-type-jprim (primitive-type-long)))
        ((equal id "JF") (atj-type-jprim (primitive-type-float)))
        ((equal id "JD") (atj-type-jprim (primitive-type-double)))
        ((equal id "YZ") (atj-type-jprimarr (primitive-type-boolean)))
        ((equal id "YC") (atj-type-jprimarr (primitive-type-char)))
        ((equal id "YB") (atj-type-jprimarr (primitive-type-byte)))
        ((equal id "YS") (atj-type-jprimarr (primitive-type-short)))
        ((equal id "YI") (atj-type-jprimarr (primitive-type-int)))
        ((equal id "YJ") (atj-type-jprimarr (primitive-type-long)))
        ((equal id "YF") (atj-type-jprimarr (primitive-type-float)))
        ((equal id "YD") (atj-type-jprimarr (primitive-type-double)))
        (t (prog2$
            (raise "Internal error: ~x0 does not identify a type." id)
            (atj-type-irrelevant))))
  ///

  (defrule atj-type-of-id-of-atj-type-id
    (equal (atj-type-of-id (atj-type-id x))
           (atj-type-fix x))
    :enable (atj-type-id
             atj-type-fix
             atj-type-acl2->get
             atj-type-jprim->get
             atj-type-jprimarr->comp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-id ((types atj-type-listp))
  :guard (consp types)
  :returns (id stringp)
  :short "String identifying a non-empty list of ATJ types."
  :long
  (xdoc::topstring-p
   "We concatenate the short strings returned by @(tsee atj-type-id).")
  (atj-types-id-aux types)
  :hooks (:fix)

  :prepwork
  ((define atj-types-id-aux ((types atj-type-listp))
     :returns (id stringp)
     (cond ((endp types) "")
           (t (str::cat (atj-type-id (car types))
                        (atj-types-id-aux (cdr types)))))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-of-id ((id stringp))
  :returns (types atj-type-listp)
  :short "Non-empty list of ATJ types identified by
          a concatenation of short strings."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-types-id).")
  (b* ((types (atj-types-of-id-aux (explode id) id)))
    (if (consp types)
        types
      (prog2$
       (raise "Internal error: ~x0 identifies an empty list of types." id)
       (list (atj-type-irrelevant)))))

  :prepwork
  ((define atj-types-of-id-aux ((chars character-listp) (id stringp))
     :returns (types atj-type-listp)
     (b* (((when (endp chars)) nil)
          ((unless (>= (len chars) 2))
           (raise "Internal error: ~x0 does not identify a list of types." id))
          (first-id (implode (list (first chars) (second chars))))
          (first-type (atj-type-of-id first-id))
          (rest-types (atj-types-of-id-aux (cddr chars) id)))
       (cons first-type rest-types))))

  ///

  (more-returns
   (types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-conv ((src-types atj-type-listp) (dst-types atj-type-listp))
  :guard (and (consp src-types)
              (consp dst-types))
  :returns (name symbolp)
  :short "ATJ type conversion function names used to annotate ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
    ", each ACL2 term is wrapped with a function named @('[src>dst]'),
     where @('src') identifies the ATJ types of the term
     and @('dst') identifies an ATJ types
     to which the term must be converted to.")
   (xdoc::p
    "These function names are all in the @('\"JAVA\"') package.
     For now we do not need these functions to actually exist in the ACL2 world,
     because annotated terms are only created ephemerally as data
     manipulated by the ATJ code generation functions.
     However, in order to prove that the type annotation process
     preserves the ACL2 meaning of terms,
     these functions will need to exist and be defined as identify functions,
     which can be easily done with a macro when that becomes important."))
  (intern$ (str::cat "["
                     (atj-types-id src-types)
                     ">"
                     (atj-types-id dst-types)
                     "]")
           "JAVA")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-of-conv ((conv symbolp))
  :returns (mv (src-types atj-type-listp)
               (dst-types atj-type-listp))
  :short "Source and destination ATJ types of a conversion function."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-type-conv).")
  (b* ((string (symbol-name conv))
       ((unless (and (> (length string) 0)
                     (eql (char string 0) #\[)
                     (eql (char string (1- (length string))) #\])))
        (raise "Internal error: ~x0 is not a conversion function." conv)
        (mv (list (atj-type-irrelevant)) (list (atj-type-irrelevant))))
       (pos (position #\> string))
       ((unless (natp pos))
        (raise "Internal error: ~x0 is not a conversion function." conv)
        (mv (list (atj-type-irrelevant)) (list (atj-type-irrelevant))))
       (src-id (subseq string 1 pos))
       (dst-id (subseq string (1+ pos) (1- (length string))))
       (src-types (atj-types-of-id src-id))
       (dst-types (atj-types-of-id dst-id)))
    (mv src-types dst-types))
  :guard-hints (("Goal"
                 :use ((:instance acl2::nth-of-index-when-member
                        (k #\>) (x (explode (symbol-name conv)))))
                 :in-theory (disable acl2::nth-of-index-when-member)))
  :prepwork ((local (include-book "std/lists/index-of" :dir :system)))
  ///

  (more-returns
   (src-types consp :rule-classes :type-prescription)
   (dst-types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-conv-allowed-p ((src-type atj-typep)
                                 (dst-type atj-typep))
  :returns (yes/no booleanp)
  :short "Ensure that a conversion between ATJ types is allowed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Not all @('[src>dst]') wrappers are allowed during type annotation.
     These wrappers server to generate Java code
     to convert from the source to the destination types.
     This conversion is ``automatic'' in the sense that
     there is no corresponding conversion function
     in the original (i.e. not-typed-annotated) ACL2 code.")
   (xdoc::p
    "For example,
     we allow a conversion from @(':ainteger') to @(':anumber'),
     which may happen when an integer is passed to a function
     whose input type is that of numbers.
     As another example,
     we allow a conversion from @(':avalue') to @(':astring'),
     which may be justified by guard verification,
     since the inferred types are decidable over-approximations.")
   (xdoc::p
    "However, we do not allow conversions
     between @(':astring') and @(':anumber'),
     because those two types are disjoint:
     it is never the case, even when guards are verified,
     that a number may be (turned into) a string
     or a string may be (turned into) a number.
     This situation should only happen
     with program-mode or non-guard-verified code.")
   (xdoc::p
    "Among the @(':acl2') types, we allow conversions exactly when
     the two types have values in common.
     Currently this is only the case when one is a subset of the other,
     but future extensions of the ATJ types may result in
     more general situations.")
   (xdoc::p
    "We disallow any conversions
     involving the @(':jprim') and @(':jprimarr') types,
     unless the two types are identical, of course.
     That is, no @(':acl2') type can be converted to a @(':j...') type,
     and no @(':j...') type can be converted to an @(':acl2') type.
     Furthermore, no @(':j...') type can be converted
     to a different @(':j...') type.
     The reason for these restrictions is that we want to keep
     the @(':j...') types separate
     from each other and from the @(':acl2') types,
     and only allow explicit conversions between these,
     i.e. via functions that the developer must write
     in the original (i.e. non-typed-annotated) ACL2 code.")
   (xdoc::p
    "This predicate says whether
     a conversion between two single types is allowed.
     The predicate @(tsee atj-types-conv-allowed-p)
     does the same for type lists,
     which are actually used in the conversion functions
     used to wrap ACL2 terms during type annotation."))
  (if (and (atj-type-case src-type :acl2)
           (atj-type-case dst-type :acl2))
      (or (atj-type-<= src-type dst-type)
          (atj-type-<= dst-type src-type))
    (atj-type-equiv src-type dst-type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-conv-allowed-p ((src-types atj-type-listp)
                                  (dst-types atj-type-listp))
  :guard (and (consp src-types) (consp dst-types))
  :returns (yes/no booleanp)
  :short "Lift @(tsee atj-type-conv-allowed-p) to lists of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists should always have the same length.
     The conversion between type lists is allowed if and only if
     it is allowed element-wise.")
   (xdoc::p
    "As a temporary exception,
     we also allow singleton lists of @(':jprim') types
     to be converted to the singleton list of @(':avalue').
     This is needed in order to handle the translation to Java
     of Java primitive array constructions via functions like
     @(tsee byte-array-with-comps),
     which may take as inputs lists of primitive values like
     @('((byte-value 33) (byte-value 0) ...)'):
     when the elements of these lists are type-annotated,
     they are wrapped with conversions from @(':jprim') types to @(':avalue'),
     which are then rewrapped during the translation to Java
     (see @(tsee atj-type-rewrap-array-initializer-elements)).
     We plan to improve the treatment of these array constructions:
     when that is done, we will remove the temporary exception
     from this predicate."))
  (if (= (len src-types) (len dst-types))
      (or (and ; the exception:
           (endp (cdr src-types))
           (endp (cdr dst-types))
           (atj-type-case (car src-types) :jprim)
           (atj-type-equiv (car dst-types)
                           (atj-type-acl2 (atj-atype-value))))
          (atj-types-conv-allowed-p-aux src-types dst-types))
    (raise "Internal error: ~
            the type lists ~x0 and ~x1 differe in length."
           src-types dst-types))

  :prepwork
  ((define atj-types-conv-allowed-p-aux ((src-types atj-type-listp)
                                         (dst-types atj-type-listp))
     :guard (= (len src-types) (len dst-types))
     :returns (yes/no booleanp)
     (or (endp src-types)
         (and (atj-type-conv-allowed-p (car src-types)
                                       (car dst-types))
              (atj-types-conv-allowed-p-aux (cdr src-types)
                                            (cdr dst-types)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-wrap-term ((term pseudo-termp)
                            (src-types atj-type-listp)
                            (dst-types? atj-type-listp))
  :guard (consp src-types)
  :returns (wrapped-term pseudo-termp)
  :short "Wrap an ACL2 term with a type conversion function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conversion is from the source types to the destination types.
     If the destination types are the empty list,
     they are treated as if they were equal to the source types,
     i.e. the conversion is a no-op.")
   (xdoc::p
    "If the destination type list is not empty,
     we ensure that the conversion is allowed.
     If it is not, we stop with an error:
     this is a ``deep'' input validation error,
     because the problem is in the ACL2 code provided by the user."))
  (b* (((unless (mbt (pseudo-termp term))) nil)
       ((when (and (consp dst-types?)
                   (not (atj-types-conv-allowed-p src-types dst-types?))))
        (raise "Type annotation failure: ~
                cannot convert from ~x0 to ~x1."
               src-types dst-types?))
       (conv (if dst-types?
                 (atj-type-conv src-types dst-types?)
               (atj-type-conv src-types src-types))))
    (fcons-term* conv term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unwrap-term ((term pseudo-termp))
  :returns (mv (unwrapped-term pseudo-termp)
               (src-types atj-type-listp)
               (dst-types atj-type-listp))
  :short "Unwrap an ACL2 term wrapped by @(tsee atj-type-wrap-term)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially the inverse function,
     except that it always returns a list of destination types,
     never @('nil')."))
  (b* ((term (if (mbt (pseudo-termp term)) term nil))
       ((when (or (variablep term)
                  (fquotep term)
                  (flambda-applicationp term)))
        (raise "Internal error: the term ~x0 has the wrong format." term)
        (mv nil (list (atj-type-irrelevant)) (list (atj-type-irrelevant))))
       (fn (ffn-symb term))
       ((when (flambdap fn))
        (raise "Internal error: the term ~x0 has the wrong format." term)
        (mv nil (list (atj-type-irrelevant)) (list (atj-type-irrelevant))))
       ((mv src-types dst-types) (atj-types-of-conv fn)))
    (mv (fargn term 1) src-types dst-types))
  ///

  (more-returns
   (src-types consp :rule-classes :type-prescription)
   (dst-types consp :rule-classes :type-prescription))

  (defret acl2-count-of-atj-type-unwrap-term-linear
    (implies unwrapped-term
             (< (acl2-count unwrapped-term)
                (acl2-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atj-type-unwrap-term
    (implies (not (pseudo-term-case unwrapped-term :null))
             (< (pseudo-term-count unwrapped-term)
                (pseudo-term-count term)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable pseudo-term-call->args
                                       pseudo-term-kind
                                       pseudo-term-count)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-term ((term pseudo-termp)
                              (src-types atj-type-listp)
                              (dst-types? atj-type-listp))
  :guard (consp src-types)
  :returns (rewrapped-term pseudo-termp
                           :hints (("Goal" :expand ((pseudo-termp term)))))
  :short "Re-wrap an ACL2 term with a type conversion function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when a term is
     preliminarily wrapped with a type conversion function,
     but its wrapping is then finalized with a different conversion function.
     So here we replace the wrapper.")
   (xdoc::p
    "We also check that the new conversion is allowed.
     We stop with an error if that is not the case;
     as in @(tsee atj-type-wrap-term),
     this is a ``deep'' input validation error."))
  (b* (((when (or (variablep term)
                  (fquotep term)
                  (not (consp (fargs term)))))
        (raise "Internal error: the term ~x0 has the wrong format." term))
       ((when (and (consp dst-types?)
                   (not (atj-types-conv-allowed-p src-types dst-types?))))
        (raise "Type annotation failure: ~
                cannot convert from ~x0 to ~x1."
               src-types dst-types?)))
    (atj-type-wrap-term (fargn term 1) src-types dst-types?))
  :guard-hints (("Goal" :expand ((pseudo-termp term)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-terms ((terms pseudo-term-listp)
                               (src-typess atj-type-list-listp)
                               (dst-types?s atj-type-list-listp))
  :guard (and (cons-listp src-typess)
              (= (len terms) (len src-typess))
              (= (len terms) (len dst-types?s)))
  :returns (rewrapped-terms pseudo-term-listp)
  :short "Lift @(tsee atj-type-rewrap-term) to lists."
  (cond ((endp terms) nil)
        (t (cons (atj-type-rewrap-term (car terms)
                                       (car src-typess)
                                       (car dst-types?s))
                 (atj-type-rewrap-terms (cdr terms)
                                        (cdr src-typess)
                                        (cdr dst-types?s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-var ((var symbolp) (types atj-type-listp))
  :guard (consp types)
  :returns (annotated-var symbolp)
  :short "Annotate an ACL2 variable with a non-empty list of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
    ", we systematically add type information to each ACL2 variable.
     We do so by adding @('[types]') before the variable name,
     where @('types') identifies a list of ATJ types.")
   (xdoc::p
    "The result of this function is never the symbol @('nil'),
     because the name of that symbol always starts with @('[')."))
  (packn-pos (list "[" (atj-types-id types) "]" var) var)
  ///

  (defrule atj-type-annotate-var-not-nil
    (implies (symbolp var)
             (not (equal (atj-type-annotate-var var types) nil)))
    :rule-classes :type-prescription
    :enable (atj-type-annotate-var)
    :disable symbol-name-intern-in-package-of-symbol
    :use ((:instance symbol-name-intern-in-package-of-symbol
           (s (implode (cons #\[
                             (append (explode (atj-types-id types))
                                     (cons #\] (explode-atom var 10))))))
           (any-symbol var))
          (:instance lemma
           (x "NIL")
           (y (implode (cons #\[
                             (append (explode (atj-types-id types))
                                     (cons #\] (explode-atom var 10))))))))
    :prep-lemmas
    ((defruled lemma
       (implies (and (stringp x)
                     (stringp y)
                     (equal x y))
                (equal (char x 0)
                       (char y 0)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unannotate-var ((var symbolp))
  :returns (mv (unannotated-var symbolp)
               (types atj-type-listp))
  :short "Decompose an annotated ACL2 variable into
          its unannotated counterpart and its types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee atj-type-annotate-var)."))
  (b* ((string (symbol-name var))
       ((unless (and (> (length string) 0)
                     (eql (char string 0) #\[)))
        (raise "Internal error: ~x0 is not an annotated variable." var)
        (mv nil (list (atj-type-irrelevant))))
       (pos (position #\] string))
       ((unless (natp pos))
        (raise "Internal error: ~x0 is not an annotated variable." var)
        (mv nil (list (atj-type-irrelevant))))
       (types-id (subseq string 1 pos))
       (types (atj-types-of-id types-id))
       (unannotated-string (subseq string (1+ pos) (length string)))
       (unannotated-var (intern-in-package-of-symbol unannotated-string var)))
    (mv unannotated-var types))
  :guard-hints (("Goal"
                 :use ((:instance acl2::nth-of-index-when-member
                        (k #\]) (x (explode (symbol-name var)))))
                 :in-theory (disable acl2::nth-of-index-when-member)))
  :prepwork ((local (include-book "std/lists/index-of" :dir :system)))
  ///

  (more-returns
   (types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-vars ((vars symbol-listp)
                                (types atj-type-listp))
  :guard (int= (len vars) (len types))
  :returns (new-vars symbol-listp)
  :short "Annotate each of a list of ACL2 variable
          with a corresponding singleton list of types."
  (cond ((endp vars) nil)
        (t (cons (atj-type-annotate-var (car vars) (list (car types)))
                 (atj-type-annotate-vars (cdr vars) (cdr types)))))
  ///

  (defret len-of-atj-type-annotate-vars
    (equal (len new-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unannotate-vars ((vars symbol-listp))
  :returns (unannotated-vars symbol-listp)
  :short "Remove the type annotations from a list of variables."
  :long
  (xdoc::topstring-p
   "The annotating types are discarded.")
  (b* (((when (endp vars)) nil)
       ((mv var &) (atj-type-unannotate-var (car vars)))
       (vars (atj-type-unannotate-vars (cdr vars))))
    (cons var vars))
  ///

  (defret len-of-atj-type-unannotate-vars
    (equal (len unannotated-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-type-annotate-term
  :short "Add ATJ type annotations to ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type annotation procedure involves inferring the types of terms,
     and wrapping terms with type conversion functions
     to match certain type requirements.")
   (xdoc::p
    "The @('var-types') input assigns types to (at least)
     all the free variables in the term that is being annotated.
     At the top level (see @(tsee atj-type-annotate-formals+body)),
     @('var-types') is initialized with the formal parameters of a function
     and with its corresponding input types.
     When we encounter a lambda expression in a term,
     @('var-types') is updated with an alist that assigns
     to the formal parameters of the lambda expression
     the types inferred for the actual arguments of the lambda expression;
     that is, unlike at the top level, at intermediate levels
     variables receive the types inferred for their binding terms.
     Here `updated' means that
     the new alist is appended before the existing one:
     recall that, due to the pre-translation step
     that removes trivial lambda-bound variables,
     lambda expressions may not be closed at this point;
     thus, the appending achieves the desired ``overwriting''.")
   (xdoc::p
    "Even though variables can be annotated by multiple types in general
     (see @(tsee atj-type-annotate-var)),
     @('var-types') assigns single types to variables.
     The only variables annotated with lists of two or more types
     are the @('mv') vars that arise in the translation of @(tsee mv-let)
     (see @(tsee fty-check-mv-let-call)).
     These @('mv') variables are treated specially
     by the type annotation process,
     without a need to add them to @('var-types').")
   (xdoc::p
    "The @('required-types?') input specifies
     the type(s) required for the term, if any.
     This is @('nil') if there are no requirements;
     it is a singleton list if the term is single-valued;
     it is a list of two or more types if the term is multi-valued.
     At the top level (see @(tsee atj-type-annotate-formals+body)),
     @('required-types?') consists of the output type(s) of the function
     (singleton if single-valued, of length two or more if multi-valued):
     the body of the function must have the output type(s) of the function.
     The recursive function @('atj-type-annotate-args'),
     which operates on the arguments of a function call,
     does not take a list of required types as input.")
   (xdoc::p
    "The result of annotating a term is not only the annotated term,
     but also the type(s) of the wrapped term.
     This is always the same as the required types
     when there are required types;
     when there are no required types,
     the resulting type(s) is/are the one(s) inferred for the term.")
   (xdoc::p
    "The type inferred for a variable is the one assigned by @('var-types').
     (As already mentioned before,
     the @('mv') variables annotated with two or more types
     are handled specially;
     they are never passed to this function directly.)
     We annotate the variable with its associated type;
     note that the variable names in @('var-types')
     do not have type annotations.
     We wrap the variable with a type conversion function
     from the inferred type(s) to the required type(s) if supplied,
     or to the inferred type(s) (i.e. no-op conversion) if not supplied.")
   (xdoc::p
    "The type inferred for a quoted constant
     is determined by the value of the quoted constant.
     We wrap the quoted constant with a type conversion function
     as discussed above.")
   (xdoc::p
    "The non-strict function @(tsee if) is treated specially,
     because eventually it is translated to a Java @('if'),
     which assigns either the `then' part or the `else' part
     to a Java local variable.
     The type of the Java local variable is
     (the Java counterpart of) @('required-types?') if supplied:
     in this case, when @('required-types?') is recursively passed
     to the second and third argument of the @(tsee if),
     both terms will be wrapped so that they have the required type(s).
     However, if @('required-types?') is @('nil'),
     the recursive annotation of the `then' and `else' subterms
     may produce different types,
     and so in this case we re-wrap those terms
     with the least upper bound of the two types.
     The case of a term of the form @('(if a a b)')
     is treated a little differently,
     but there is no substantial difference.
     In the general case of @('(if a b c)') with @('a') different from @('b'),
     there is never any required type for the test @('a'),
     because in the Java code it is just used
     to generate the test of the @('if');
     ACL2 should ensure that the test of an @(tsee if) is single-valued,
     but we defensively check for that.
     In all cases, the @(tsee if) is wrapped with
     the identify conversion function for the overall type(s),
     for uniformity and to readily indicate the type
     of the Java local variable to generate.")
   (xdoc::p
    "For a lambda expression
     (other than the kind resulting from an @(tsee mv-let),
     whose treatment is described below),
     the argument terms are annotated without required types.
     The inferred types are then assigned to the formal parameters
     when the body of the lambda expression is annotated.
     We annotate all the formal parameters of the lambda expression;
     but note that the new @('var-types') has non-annotated variable names.
     Note that the list of types returned by @(tsee atj-type-annotate-args)
     has a different meaning from
     the one returned by @(tsee atj-type-annotate-term):
     while the latter is a single or multiple type for a single term,
     the latter consists of a single type for each argument
     (more on this below).")
   (xdoc::p
    "For a named function call other than @(tsee mv)
     (whose treatment is described below),
     the function's types are obtained.
     We first try annotating the argument terms without required types
     (as done for a lambda expression as explained above),
     thus inferring types for the arguments.
     Then we look for the function types (of the named function)
     whose input types are wider than or the same as
     the inferred argument types.
     If there are some, we select the one whose input types are the least
     (this always exists because of the closure property
     checked by @(tsee atj-other-function-type);
     see the documentation of that macro and supporting functions for details);
     we then use the output type(s) of the selected function type
     as the type(s) inferred for the function call,
     and wrap it to adapt to the required type(s) for the function call if any.
     The successful selection of such a function type means that,
     in the generated Java code, an overloaded method will be called
     based on the argument types inferred by the Java compiler.
     If there are no function types satisfying the above condition,
     we look at the primary function type (which always exists),
     and its input types become the required ones for the argument terms,
     while the output type(s) are used to infer the type(s) for the call,
     which is then wrapped as needed to match the required type(s) if any.")
   (xdoc::p
    "If we encounter a call of @(tsee mv),
     which may be introduced by a previous pre-translation step,
     we allow its arguments to have any types
     and we regard the call as having the multiple type obtained
     by putting the argument types into a list.
     We also collect the required (if present) or inferred (otherwise) types
     in a list without duplications that is threaded through these functions.
     This list does not affect the type annotations,
     but is used by the code generation functions
     in order to determine which @(tsee mv) classes must be generated.")
   (xdoc::p
    "Before attempting to process lambda expression or named function calls
     as described above,
     we first check whether the term is a translated @(tsee mv-let).
     For this to be the case,
     not only @(tsee fty-check-mv-let-call) must succeed,
     yielding variables @('var1'), ..., @('varn')
     and subterms @('mv-term') and @('body-term'),
     but also the term assigned to the @('mv') variable
     must have multiple types.
     If the term is not a translated @(tsee mv-let),
     the term is processed as any other term.
     If the term is a translated @(tsee mv-let),
     we annotate it by building a term of the form")
   (xdoc::codeblock
    "([reqinf>reqinf]"
    " ((lambda ([types]mv)"
    "          ([reqinf>reqinf]"
    "           ((lambda ([type1]var1 ... [typen]varn)"
    "                    ([...>reqinf] body-term))"
    "            ([AV>type1] (mv-nth ([AI>AI] '0)"
    "                                ([types>types] [types]mv)))"
    "            ..."
    "            ([AV>typen] (mv-nth ([AI>AI] 'n-1)"
    "                                ([types>types] [types]mv))))))"
    "  ([types>types] mv-term)))")
   (xdoc::p
    "where @('types') consists of @('type1'), ..., @('typen'),
     and where @('reqinf') is @('required-types?') if non-@('nil')
     or otherwise the types inferred for @('body-term').
     This term is systematically annotated in the same way as any other term,
     so that subsequent pre-processing steps can treat all terms uniformly.
     The @('[AV>typei]') conversions
     are consistent with the function type of @(tsee mv-nth),
     so that, as we are adding more direct support for @(tsee mv) in ATJ,
     the code generation functions can still treat these newly annotated terms
     as before, i.e. treating multiple values as lists.")
   (xdoc::p
    "The function @('atj-type-annotate-mv-let') first checks whether the term
     has the structure of a translated @(tsee mv-let).
     Then it annotates the term to which the @('mv') variable is bound,
     inferring a non-empty list of types (i.e. @('types') above) for it:
     if the list is a singleton,
     the term is actually not a translated @(tsee mv-let),
     and the function returns a failure,
     letting @('atj-type-annotate-term') handle the term.
     Otherwise, after checking that the number of types
     is consistent with the number of variables
     (this is never expected to fail),
     we annotate the body term:
     we pass the top-level required types (if any),
     and we update @('var-types') with the @(tsee mv-let) variables
     associated to the types for the term to which @('mv') is bound;
     we do not need to update @('var-types') with @('mv')
     because @(tsee fty-check-mv-let-call) ensures that
     the variable @('mv') does not occur free in the body term.
     Note that, in general, some variables bound to @(tsee mv-nth) calls
     may have been removed by a previous pre-translation step,
     the one that removes unused variables (see @(tsee fty-check-mv-let-call));
     thus, in order to extend @('var-types'),
     we select the types for which there are actually variables.")
   (xdoc::p
    "In @('atj-type-annotate-args'), we check that
     the types inferred for each single argument are a singleton.
     Except for the argument of @('((lambda (mv) ...) mv-term)')
     in a translated @(tsee mv-let),
     in ACL2 all the arguments of function calls must be single-valued.
     We do not expect this check to ever fail.")
   (xdoc::p
    "Note that an annotated term is still a regular term,
     but it has a certain structure."))

  (define atj-type-annotate-term ((term pseudo-termp)
                                  (required-types? atj-type-listp)
                                  (var-types atj-symbol-type-alistp)
                                  (mv-typess atj-type-list-listp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (cons-listp mv-typess)
    :returns (mv (annotated-term pseudo-termp)
                 (resulting-types (and (atj-type-listp resulting-types)
                                       (consp resulting-types)))
                 (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                     (cons-listp new-mv-typess))))
    (b* (((unless (mbt (atj-type-listp required-types?)))
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
         ((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
         ((unless (mbt (and (atj-type-list-listp mv-typess)
                            (cons-listp mv-typess))))
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
         ((when (pseudo-term-case term :null))
          (raise "Internal error: null term.")
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
         ((when (pseudo-term-case term :var))
          (b* ((var (pseudo-term-var->name term))
               (var+type (assoc-eq var var-types))
               ((unless (consp var+type))
                (prog2$
                 (raise "Internal error: the variable ~x0 has no type." term)
                 (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
               (type (cdr var+type))
               (types (list type))
               (var (atj-type-annotate-var var types))
               ((unless (<= (len required-types?) 1))
                (raise "Internal error: ~
                        requiring multiple types ~x0 ~
                        for a single-type variable ~x1."
                       required-types? var)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
            (mv (atj-type-wrap-term (pseudo-term-var var)
                                    types
                                    required-types?)
                (or required-types? types)
                mv-typess)))
         ((when (pseudo-term-case term :quote))
          (b* ((value (pseudo-term-quote->val term))
               (type (atj-type-of-value value))
               (types (list type))
               ((unless (<= (len required-types?) 1))
                (raise "Internal error: ~
                        requiring multiple types ~x0 ~
                        for a quoted constant ~x1."
                       required-types? term)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
            (mv (atj-type-wrap-term term types required-types?)
                (or required-types? types)
                mv-typess)))
         ((mv successp annotated-term resulting-types mv-typess)
          (atj-type-annotate-mv-let term
                                    required-types?
                                    var-types
                                    mv-typess
                                    guards$
                                    wrld))
         ((when successp) (mv annotated-term resulting-types mv-typess))
         (fn (pseudo-term-call->fn term))
         (args (pseudo-term-call->args term))
         ((when (and (eq fn 'if)
                     (int= (len args) 3))) ; should be always true
          (b* ((test (first args))
               (then (second args))
               (else (third args)))
            (if (equal test then) ; it's an OR
                (b* ((first test)
                     (second else)
                     ((unless (<= (len required-types?) 1))
                      (raise "Internal error: ~
                              requiring multiple types ~x0 ~
                              for the term ~x1."
                             required-types? term)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     ((mv first first-types mv-typess)
                      (atj-type-annotate-term first
                                              required-types?
                                              var-types
                                              mv-typess
                                              guards$
                                              wrld))
                     ((unless (= (len first-types) 1))
                      (raise "Internal error: ~
                              the first disjunct ~x0 of the term ~x1 ~
                              returns multiple values."
                             first term)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     ((mv second second-types mv-typess)
                      (atj-type-annotate-term second
                                              required-types?
                                              var-types
                                              mv-typess
                                              guards$
                                              wrld))
                     ((unless (= (len second-types) 1))
                      (raise "Internal error: ~
                              the second disjunct ~x0 of the term ~x1 ~
                              returns multiple values."
                             second term)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     (types (or required-types?
                                (atj-type-list-join first-types second-types)))
                     ((unless (atj-type-listp types))
                      (raise "Type annotation failure: ~
                              cannot merge types ~x0 with types ~x1."
                             first-types second-types)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     (first (if required-types?
                                first
                              (atj-type-rewrap-term first
                                                    first-types
                                                    types)))
                     (second (if required-types?
                                 second
                               (atj-type-rewrap-term second
                                                     second-types
                                                     types)))
                     (term (pseudo-term-call 'if (list first first second))))
                  (mv (atj-type-wrap-term term types types)
                      types
                      mv-typess))
              (b* (((mv test test-types mv-typess)
                    (atj-type-annotate-term test
                                            nil
                                            var-types
                                            mv-typess
                                            guards$
                                            wrld))
                   ((unless (= (len test-types) 1))
                    (raise "Internal error: ~
                            the test ~x0 of the term ~x1 ~
                            returns multiple values."
                           test term)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   ((mv then then-types mv-typess)
                    (atj-type-annotate-term then
                                            required-types?
                                            var-types
                                            mv-typess
                                            guards$
                                            wrld))
                   ((mv else else-types mv-typess)
                    (atj-type-annotate-term else
                                            required-types?
                                            var-types
                                            mv-typess
                                            guards$
                                            wrld))
                   ((unless (= (len then-types) (len else-types)))
                    (raise "Internal error: ~
                            the branches ~x0 and ~x1 of the term ~x2 ~
                            have different numbers of types, ~
                            namely ~x3 and ~x4."
                           then else term then-types else-types)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   ((unless (or (null required-types?)
                                (= (len required-types?) (len then-types))))
                    (raise "Internal error: ~
                            requiring the types ~x0 for the term ~x1, ~
                            which has a different number of types ~x2."
                           required-types? term (len then-types))
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   (types (or required-types?
                              (atj-type-list-join then-types else-types)))
                   ((unless (atj-type-listp types))
                    (raise "Type annotation failure: ~
                            cannot merge types ~x0 with types ~x1."
                           then-types else-types)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   (then (if required-types?
                             then
                           (atj-type-rewrap-term then then-types types)))
                   (else (if required-types?
                             else
                           (atj-type-rewrap-term else else-types types)))
                   (term (pseudo-term-call 'if (list test then else))))
                (mv (atj-type-wrap-term term types types)
                    types
                    mv-typess)))))
         ((mv args types mv-typess) (atj-type-annotate-args args
                                                            var-types
                                                            mv-typess
                                                            guards$
                                                            wrld))
         ((when (eq fn 'mv))
          (b* (((unless (>= (len types) 2))
                (raise "Internal error: ~
                        found MV applied to arguments ~x0."
                       args)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
               ((unless (or (null required-types?)
                            (= (len types) (len required-types?))))
                (raise "Internal error: ~
                        requiring the types ~x0 for the term ~x1."
                       required-types? term)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
               (resulting-types (or required-types? types)))
            (mv (atj-type-wrap-term (pseudo-term-call 'mv args)
                                    types
                                    required-types?)
                resulting-types
                (add-to-set-equal resulting-types mv-typess))))
         ((when (pseudo-term-case term :fncall))
          (b* ((fn-info (atj-get-function-type-info fn guards$ wrld))
               (main-fn-type (atj-function-type-info->main fn-info))
               (other-fn-types (atj-function-type-info->others fn-info))
               (all-fn-types (cons main-fn-type other-fn-types))
               (fn-type? (atj-function-type-of-min-input-types types
                                                               all-fn-types)))
            (if fn-type?
                (b* ((in-types (atj-function-type->inputs fn-type?))
                     (out-types (atj-function-type->outputs fn-type?))
                     ((unless (= (len in-types) (len args)))
                      (raise "Internal error: ~
                              the function ~x0 has ~x1 arguments ~
                              but a different number of input types ~x2."
                             fn (len args) (len in-types))
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     ((unless (= (len in-types) (len types)))
                      (raise "Internal error: ~
                              the input types ~x0 of the function ~x1 ~
                              differ in number from the argument types ~x2."
                             in-types fn types)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     (args (atj-type-rewrap-terms args
                                                (atj-type-list-to-type-list-list
                                                 types)
                                                (atj-type-list-to-type-list-list
                                                 in-types)))
                     ((unless (consp out-types))
                      (raise "Internal error: ~
                              no output types in function type ~x0."
                             fn-type?)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     ((unless (or (null required-types?)
                                  (= (len required-types?) (len out-types))))
                      (raise "Internal error: ~
                              requiring the types ~x0 for the term ~x1, ~
                              which has a different number of types ~x2."
                             required-types? term out-types)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
                  (mv (atj-type-wrap-term (pseudo-term-call fn args)
                                          out-types
                                          required-types?)
                      (or required-types? out-types)
                      mv-typess))
              (b* ((in-types (atj-function-type->inputs main-fn-type))
                   (out-types (atj-function-type->outputs main-fn-type))
                   ((unless (= (len in-types) (len args)))
                    (raise "Internal error: ~
                            the function ~x0 has ~x1 arguments ~
                            but a different number of input types ~x2."
                           fn (len args) (len in-types))
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   ((unless (= (len in-types) (len types)))
                    (raise "Internal error: ~
                            the input types ~x0 of the function ~x1 ~
                            differ in number from the argument types ~x2."
                           in-types fn types)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   (args (atj-type-rewrap-terms args
                                                (atj-type-list-to-type-list-list
                                                 types)
                                                (atj-type-list-to-type-list-list
                                                 in-types)))
                   ((unless (consp out-types))
                    (raise "Internal error: ~
                            the function ~x0 has an empty list of output types."
                           fn)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
                (mv (atj-type-wrap-term (pseudo-term-call fn args)
                                        out-types
                                        required-types?)
                    (or required-types? out-types)
                    mv-typess)))))
         (formals (pseudo-lambda->formals fn))
         (var-types (append (pairlis$ formals types) var-types))
         (formals (atj-type-annotate-vars formals types))
         ((mv body types mv-typess)
          (atj-type-annotate-term (pseudo-lambda->body fn)
                                  required-types?
                                  var-types
                                  mv-typess
                                  guards$
                                  wrld))
         (term (pseudo-term-call (pseudo-lambda formals body) args))
         ((unless (or (null required-types?)
                      (= (len required-types?) (len types))))
          (raise "Internal error: ~
                  requiring the types ~x0 for the term ~x1, ~
                  whose inferred types are ~x2."
                 required-types? term types)
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
      (mv (atj-type-wrap-term term
                              types
                              required-types?)
          (or required-types? types)
          mv-typess))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-TYPE-ANNOTATE-MV-LET decreases:
    :measure (two-nats-measure (pseudo-term-count term) 1))

  (define atj-type-annotate-mv-let ((term pseudo-termp)
                                    (required-types? atj-type-listp)
                                    (var-types atj-symbol-type-alistp)
                                    (mv-typess atj-type-list-listp)
                                    (guards$ booleanp)
                                    (wrld plist-worldp))
    :guard (cons-listp mv-typess)
    :returns (mv (success booleanp)
                 (annotated-term pseudo-termp)
                 (resulting-types (and (atj-type-listp resulting-types)
                                       (consp resulting-types)))
                 (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                     (cons-listp new-mv-typess))))
    (b* (((unless (mbt (atj-type-listp required-types?)))
          (mv nil nil (list (atj-type-irrelevant)) nil))
         ((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv nil nil (list (atj-type-irrelevant)) nil))
         ((unless (mbt (and (atj-type-list-listp mv-typess)
                            (cons-listp mv-typess))))
          (mv nil nil (list (atj-type-irrelevant)) nil))
         ((mv mv-let-p mv-var vars indices mv-term body-term)
          (fty-check-mv-let-call term))
         ((unless mv-let-p)
          (mv nil nil (list (atj-type-irrelevant)) mv-typess))
         ((mv annotated-mv-term mv-term-types mv-typess)
          (atj-type-annotate-term mv-term nil var-types mv-typess guards$ wrld))
         ((when (= (len mv-term-types) 1))
          (mv nil nil (list (atj-type-irrelevant)) mv-typess))
         (annotated-mv (atj-type-annotate-var mv-var mv-term-types))
         (sel-types (atj-select-mv-term-types indices mv-term-types))
         (annotated-vars (atj-type-annotate-vars vars sel-types))
         (var-types (append (pairlis$ vars sel-types) var-types))
         ((mv annotated-body-term body-term-types mv-typess)
          (atj-type-annotate-term body-term
                                  required-types?
                                  var-types
                                  mv-typess
                                  guards$
                                  wrld))
         ((unless (or (null required-types?)
                      (= (len required-types?) (len body-term-types))))
          (raise "Internal error: ~
                  requiring the types ~x0 for the term ~x1, ~
                  whose inferred types are ~x2."
                 required-types? term body-term-types)
          (mv nil nil (list (atj-type-irrelevant)) nil))
         (wrapped-mv (atj-type-wrap-term annotated-mv mv-term-types nil))
         (annotated-mv-nth-calls (atj-type-annotate-mv-nth-terms sel-types
                                                                 indices
                                                                 wrapped-mv))
         (inner-lambda (pseudo-lambda annotated-vars annotated-body-term))
         (inner-lambda-app (pseudo-term-call inner-lambda
                                             annotated-mv-nth-calls))
         (annotated-inner-lambda-app (atj-type-wrap-term inner-lambda-app
                                                         body-term-types
                                                         body-term-types))
         (outer-lambda (pseudo-lambda (list annotated-mv)
                                      annotated-inner-lambda-app))
         (outer-lambda-app (pseudo-term-call outer-lambda
                                             (list annotated-mv-term)))
         (final-term (atj-type-wrap-term outer-lambda-app
                                         body-term-types
                                         body-term-types)))
      (mv t
          final-term
          (or required-types? body-term-types)
          mv-typess))
    :measure (two-nats-measure (pseudo-term-count term) 0))

  (define atj-type-annotate-args ((args pseudo-term-listp)
                                  (var-types atj-symbol-type-alistp)
                                  (mv-typess atj-type-list-listp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (cons-listp mv-typess)
    :returns (mv (annotated-args (and (pseudo-term-listp annotated-args)
                                      (equal (len annotated-args)
                                             (len args))))
                 (resulting-types (and (atj-type-listp resulting-types)
                                       (equal (len resulting-types)
                                              (len args))))
                 (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                     (cons-listp new-mv-typess))))
    (b* (((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv (repeat (len args) (pseudo-term-null))
              (repeat (len args) (atj-type-irrelevant))
              nil))
         ((unless (mbt (and (atj-type-list-listp mv-typess)
                            (cons-listp mv-typess))))
          (mv (repeat (len args) (pseudo-term-null))
              (repeat (len args) (atj-type-irrelevant))
              nil))
         ((when (endp args)) (mv nil nil mv-typess))
         ((mv arg types mv-typess) (atj-type-annotate-term (car args)
                                                           nil ; REQUIRED-TYPES?
                                                           var-types
                                                           mv-typess
                                                           guards$
                                                           wrld))
         ((unless (= (len types) 1))
          (raise "Internal error: ~
                  the function argument ~x0 has types ~x1."
                 (car args) types)
          (mv (repeat (len args) (pseudo-term-null))
              (repeat (len args) (atj-type-irrelevant))
              nil))
         (type (car types))
         ((mv args types mv-typess) (atj-type-annotate-args (cdr args)
                                                            var-types
                                                            mv-typess
                                                            guards$
                                                            wrld)))
      (mv (cons arg args) (cons type types) mv-typess))
    :measure (two-nats-measure (pseudo-term-list-count args) 0))

  :prepwork

  ((define atj-type-annotate-mv-nth-terms ((types atj-type-listp)
                                           (indices nat-listp)
                                           (wrapped-mv pseudo-termp))
     :guard (= (len types) (len indices))
     :returns (terms pseudo-term-listp)
     (b* (((when (endp types)) nil)
          (wrapped-index (atj-type-wrap-term (pseudo-term-quote
                                              (car indices))
                                             (list (atj-type-acl2
                                                    (atj-atype-integer)))
                                             (list (atj-type-acl2
                                                    (atj-atype-integer)))))
          (mv-nth-call (pseudo-term-call 'mv-nth
                                         (list wrapped-index wrapped-mv)))
          (wrapped-mv-nth-call (atj-type-wrap-term mv-nth-call
                                                   (list (atj-type-acl2
                                                          (atj-atype-value)))
                                                   (list (car types))))
          (rest (atj-type-annotate-mv-nth-terms (cdr types)
                                                (cdr indices)
                                                wrapped-mv)))
       (cons wrapped-mv-nth-call rest))
     ///
     (defret len-of-atj-type-annotate-mv-nth-terms
       (equal (len terms)
              (len types))))

   (define atj-select-mv-term-types ((indices nat-listp)
                                     (mv-types atj-type-listp))
     :returns (selected-mv-types atj-type-listp)
     (b* (((unless (mbt (nat-listp indices)))
           (repeat (len indices) (atj-type-irrelevant)))
          ((unless (mbt (atj-type-listp mv-types)))
           (repeat (len indices) (atj-type-irrelevant)))
          ((when (endp indices)) nil)
          (index (car indices))
          ((unless (< index (len mv-types)))
           (raise "Internal error: ~
                   index ~x0 has no corresponding type in ~x1."
                  index mv-types)
           (repeat (len indices) (atj-type-irrelevant)))
          (type (nth index mv-types))
          (rest-types (atj-select-mv-term-types (cdr indices) mv-types)))
       (cons type rest-types))
     ///
     (defret len-of-atj-select-mv-term-types
       (equal (len selected-mv-types)
              (len indices))))

   (local (include-book "std/lists/top" :dir :system))

   (local (in-theory (disable pseudo-termp
                              acl2::consp-under-iff-when-true-listp))))

  :verify-guards nil ; done below

  ///

  (defrulel verify-guards-lemma-1
    (implies (>= (len x) 1)
             (consp x)))

  (defrulel verify-guards-lemma-2
    (implies (atj-type-listp x)
             (true-listp x)))

  (defrulel verify-guards-lemma-3
    (implies (symbolp x)
             (pseudo-termp x))
    :enable pseudo-termp)

  (verify-guards atj-type-annotate-term
    :hints (("Goal"
             :in-theory (enable pseudo-fn-args-p
                                pseudo-var-p
                                len-of-fty-check-mv-let-call.indices/vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-formals+body ((formals symbol-listp)
                                        (body pseudo-termp)
                                        (in-types atj-type-listp)
                                        (out-types atj-type-listp)
                                        (mv-typess atj-type-list-listp)
                                        (guards$ booleanp)
                                        (wrld plist-worldp))
  :guard (and (int= (len formals) (len in-types))
              (consp out-types)
              (cons-listp mv-typess))
  :returns (mv (annotated-formals symbol-listp)
               (annotated-body pseudo-termp)
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))))
  :short "Add ATJ type annotations to the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input and output types of the function are supplied as arguments.
     We annotate the body, using the output types as the required types.
     We initialize the variable-type alist
     to assign the input types to the formal parameters.
     We also annotate the formal parameters,
     but note that @('var-types') has non-annotated variable names.")
   (xdoc::p
    "We collect all the @(tsee mv) types in the body
     for which we will need to generate @(tsee mv) classes."))
  (b* ((var-types (pairlis$ formals in-types))
       (formals (atj-type-annotate-vars formals in-types))
       ((mv body & mv-typess)
        (atj-type-annotate-term
         body out-types var-types mv-typess guards$ wrld)))
    (mv formals body mv-typess))
  ///

  (defret len-of-atj-type-annotate-formals+body.new-formals
    (equal (len annotated-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-annotated-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (mv-var symbolp)
               (mv-term pseudo-termp)
               (vars symbol-listp)
               (indices nat-listp)
               (body-term pseudo-termp))
  :short "Recognize and decompose type-annotated @(tsee mv-let)s."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type annotation pre-translation step recognizes @(tsee mv-let)s
     and transforms them as explained in @(tsee atj-type-annotate-term).
     So the resulting term should have the form")
   (xdoc::codeblock
    "([reqinf>reqinf]"
    " ((lambda ([types]mv)"
    "          ([reqinf>reqinf]"
    "           ((lambda ([type1]var1 ... [typen]varn)"
    "                    ([...>reqinf] body-term))"
    "            ([AV>type1] (mv-nth ([AI>AI] '0)"
    "                                ([types>types] [types]mv)))"
    "            ..."
    "            ([AV>typen] (mv-nth ([AI>AI] 'n-1)"
    "                                ([types>types] [types]mv))))))"
    "  ([types>types] mv-term)))")
   (xdoc::p
    "where @('mv') may not be the symbol `@('mv')' but some other symbol.
     Because of the pre-translation step that removes unused variables,
     the formals and arguments of the inner lambda
     may be fewer than the elements of @('types');
     i.e. some @(tsee mv-nth) indices may be skipped.")
   (xdoc::p
    "This code recognizes terms of the form above,
     returning some of the constituents if successful.
     The @('mv-var') result is @('[types]mv'),
     i.e. the annotated multi-value variable.
     The @('mv-term') result is @('([types>types] mv-term)'),
     i.e. the wrapped multi-value term.
     The @('vars') result is @('([type1]var1 ... [typen]varn)')
     (possibly skipping some indices),
     i.e. the list of formals of the inner lambda expression,
     all annotated.
     The @('indices') result is the ordered list of @(tsee mv-nth) indices
     actually present; these are 0-based.
     The @('body-term') result is @('([...>reqinf] body-term)'),
     i.e. the wrapped body of the inner lambda expression.."))
  (b* (((mv outer-lambda-call reqinf reqinf2) (atj-type-unwrap-term term))
       ((unless (equal reqinf reqinf2)) (mv nil nil nil nil nil nil))
       ((mv okp mv-var wrapped-inner-lambda-call mv-term)
        (check-unary-lambda-call outer-lambda-call))
       ((unless okp) (mv nil nil nil nil nil nil))
       ((mv & types) (atj-type-unannotate-var mv-var))
       ((unless (> (len types) 1)) (mv nil nil nil nil nil nil))
       ((mv & src-types dst-types) (atj-type-unwrap-term mv-term))
       ((unless (and (equal src-types types)
                     (equal dst-types types)))
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       ((mv inner-lambda-call src-types dst-types)
        (atj-type-unwrap-term wrapped-inner-lambda-call))
       ((unless (and (equal src-types reqinf)
                     (equal dst-types reqinf))) (mv nil nil nil nil nil nil))
       ((mv okp vars body-term args) (check-lambda-call inner-lambda-call))
       ((unless okp)
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       ((mv & & dst-types) (atj-type-unwrap-term body-term))
       ((unless (equal dst-types reqinf))
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       (indices (atj-check-annotated-mv-let-call-aux
                 args vars types mv-var)))
    (mv t mv-var mv-term vars indices body-term))
  :guard-hints (("Goal"
                 :in-theory
                 (enable acl2::len-of-check-lambda-calls.formals-is-args)))

  :prepwork

  ((define atj-check-annotated-mv-let-call-aux ((args pseudo-term-listp)
                                                (vars symbol-listp)
                                                (types atj-type-listp)
                                                (mv-var symbolp))
     :guard (and (= (len vars) (len args))
                 (consp types))
     :returns (indices nat-listp)
     (b* (((when (endp args)) nil)
          ((mv arg arg-src arg-dst) (atj-type-unwrap-term (car args)))
          ((unless (and (not (variablep arg))
                        (not (fquotep arg))
                        (eq (ffn-symb arg) 'mv-nth)
                        (= (len (fargs arg)) 2)
                        (equal (fargn arg 2)
                               (atj-type-wrap-term mv-var types types))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          ((mv index index-src index-dst) (atj-type-unwrap-term (fargn arg 1)))
          ((unless (and (quotep index)
                        (equal index-src (list (atj-type-acl2
                                                (atj-atype-integer))))
                        (equal index-dst (list (atj-type-acl2
                                                (atj-atype-integer))))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          (index (unquote-term index))
          ((unless (integer-range-p 0 (len types) index))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          ((unless (and (equal arg-src (list (atj-type-acl2 (atj-atype-value))))
                        (equal arg-dst (list (nth index types)))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          (var (car vars))
          ((mv & var-types) (atj-type-unannotate-var var))
          ((unless (equal var-types (list (nth index types))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0)))
       (cons index (atj-check-annotated-mv-let-call-aux (cdr args)
                                                        (cdr vars)
                                                        types
                                                        mv-var)))

     :prepwork

     ((local (include-book "std/typed-lists/nat-listp" :dir :system))

      (defrulel verify-guards-lemma
        (implies (and (pseudo-termp term)
                      (not (variablep term))
                      (not (fquotep term)))
                 (pseudo-termp (fargn term 1)))
        :expand ((pseudo-termp term))))

     ///

     (defret len-of-atj-check-annotated-mv-let-call-aux
       (equal (len indices) (len args)))))

  ///

  (defret len-of-atj-check-annotated-mv-let.vars/indices
    (equal (len indices)
           (len vars))
    :hints (("Goal"
             :in-theory
             (enable acl2::len-of-check-lambda-calls.formals-is-args))))

  (in-theory (disable len-of-atj-check-annotated-mv-let.vars/indices))

  (defret atj-check-annotated-mv-let-mv-term-smaller
    (implies yes/no
             (< (acl2-count mv-term)
                (acl2-count term)))
    :rule-classes :linear
    :hints (("Goal"
             :use (acl2-count-of-atj-type-unwrap-term-linear
                   (:instance acl2::acl2-count-of-check-unary-lambda-call.arg
                    (term (mv-nth 0 (atj-type-unwrap-term term)))))
             :in-theory (disable
                         acl2-count-of-atj-type-unwrap-term-linear
                         acl2::acl2-count-of-check-unary-lambda-call.arg))))

  (defret atj-check-annotated-mv-let-body-term-smaller
    (implies yes/no
             (< (acl2-count body-term)
                (acl2-count term)))
    :rule-classes :linear
    :hints (("Goal"
             :use (acl2-count-of-atj-type-unwrap-term-linear
                   (:instance acl2::acl2-count-of-check-unary-lambda-call.arg
                    (term (mv-nth 0 (atj-type-unwrap-term term))))
                   (:instance acl2-count-of-atj-type-unwrap-term-linear
                    (term (mv-nth 2 (check-unary-lambda-call
                                     (mv-nth 0 (atj-type-unwrap-term term))))))
                   (:instance acl2::acl2-count-of-check-lambda-call.body
                    (term
                     (mv-nth 0 (atj-type-unwrap-term
                                (mv-nth 2 (check-unary-lambda-call
                                           (mv-nth 0 (atj-type-unwrap-term
                                                      term)))))))))
             :in-theory (disable
                         acl2-count-of-atj-type-unwrap-term-linear
                         acl2::acl2-count-of-check-unary-lambda-call.arg
                         acl2::acl2-count-of-check-lambda-call.body)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-array-analysis
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          single-threadedness analysis of Java primitive arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to generate Java code
     that correctly destructively updates (primitive) arrays,
     we perform a " (xdoc::seetopic "acl2::stobj" "stobj") "-like analysis
     to establish that arrays are treated single-threadedly
     in the ACL2 functions that are translated to Java.")
   (xdoc::p
    "Unlike the other pre-translation steps,
     this analysis does not modify the ACL2 function bodies.
     However, this analysis is best carried out
     between the type annotation pre-translation step
     and the variable reuse pre-translation step.
     The reason why this analysis should be carried
     after the type annotation step
     is that we need the type annotations to determine where the arrays are,
     and subject them to the analysis.
     The reason why this analysis should be carried before
     the variable reuse step
     is that this step may mark and differentiate array variables
     that the analysis needs to ensure that the denote the same array
     and that the array is treated single-threadedly.")
   (xdoc::p
    "This array analysis is similar to ACL2's stobj analysis
     in the sense that it imposes the same draconian constraints
     on the use of arrays,
     namely that the same name is consistently used for each array,
     that functions with array inputs are passed those names,
     that every array possibly modified by a function
     is bound to the same name and is also returned by the surrounding function,
     and so on.")
   (xdoc::p
    "However, this array analysis also differs from the stobj analysis,
     because stobjs are global variables
     whose names must be consistently used by all the functions
     that manipulate them.
     In contrast, (representations of) Java arrays in ACL2 functions
     do not have global names, but their names are local to the functions.
     Consider a function @('f') that takes two arrays and as inputs
     and returns them (possibly modified) as outputs,
     and a function @('g') that takes two array inputs @('a') and @('b')
     and calls @('g') with them:
     we need to know how the two array outputs of @('g')
     correspond to the array inputs of @('g'),
     so that we can check that @('f') properly binds
     the possibly modified array @('a') to the variable @('a')
     and the possibly modified array @('b') to the variable @('b').
     In ACL2's stobj analysis, @('g') will have the @('stobjs-out') property
     that says which results are which stobjs, using their global names
     (except the case in which @('g') is
     the same as or mutually recursive with @('f'),
     in which case ACL2 presumably uses the non-recursive branches of the clique
     to determine the output stobjs of the functions).
     In our array analysis, we need something like the @('stobjs-out') property:
     we do that beforehand (i.e. before the array analysis) via
     @(tsee atj-main-function-type) and @(tsee atj-other-function-type),
     which allow the specification of output array names.
     But since array names are not global as pointed out above,
     output array names in the ATJ function type tables alone do not suffice.
     We need to take into account the ``mapping'' between input array names
     (which are the formal parameters of a function)
     and the output array names.
     For the example @('f') above,
     perhaps its two array formal arguments are @('x') and @('y'):
     based on which output array has name @('x') vs. @('y'),
     we can determine the mapping.
     Thus, when we analyze @('g'), which passes @('a') and @('b') to @('f'),
     we match @('a') and @('b') to @('x') and @('y'),
     and we determine which results of @('f')
     must be bound to @('a') and @('b') in @('g').
     Note that this approach works also if @('g')
     is mutually recursive with or the same as @('f')
     (in the latter case the variables @('a') and @('b')
     would be the same as @('x') and @('y') then),
     because all functions must have type and array name information
     before the array analysis takes place.
     If the type and array name information is incorrect/inconsistent,
     the array analysis will reveal that.")
   (xdoc::p
    "Another complication of this array analysis,
     which does not happen with stobjs,
     is that some functions may create new arrays (directly or indirectly).
     These are arrays not passed as inputs, but returned as outputs afresh.
     As such, they do not correspond to any inputs,
     so there is no name mapping.
     This is why
     @(tsee atj-main-function-type) and @(tsee atj-other-function-type)
     allow unnamed array outputs,
     whose meaning is that they must be newly created arrays;
     the array analysis checks that.
     If @('f') returns new arrays,
     and @('g') calls @('f'),
     then the array analysis must ensure that these new arrays
     are bound to variables distinct from each other
     and from the ones of the input arrays.
     In contrast, stobjs are not really created by functions;
     they are declared, essentially as global variables,
     and created beforehand."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-analyze-arrays-in-term
  :short "Array analysis of ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The array analysis assigns to each term a non-empty list of array names,
     corresponding to the array types returned by the term.
     Recall that the type annotation pre-translation step
     assigns a non-empty list of ATJ types to every term;
     the list is a singleton if the term is single-valued,
     otherwise the list's length is the number of results returned by the term.
     Some of these result types may be (Java primitive) arrays:
     in that case, the array analysis assigns
     array names to the corresponding results,
     while it assigns @('nil') to non-array results:
     the list of symbols inferred by the array analysis
     has always the same length as
     the list of types inferred by the type annotations,
     i.e. every term's result gets an array name.
     The array names are the names of the variables that hold the arrays.
     When a term returns a newly created array
     that is not yet bound to any variable,
     its array name, inferred by array analysis, is @('nil').
     All of this is, of course,
     related to the array names that can be specified in
     @(tsee atj-main-function-type) and @(tsee atj-other-function-type):
     see their documentation and implementation.")
   (xdoc::p
    "As the array analysis calculates these array names for terms,
     it also checks that arrays are treated single-threadedly,
     similarly to stobjs.
     The constraints to be satisfied are fairly draconian, like stobjs.
     Each modified array must be
     always bound to the same array name inside a function.
     Different functions may use different names,
     also because array variables are not global.
     A function that takes an array argument can only be passed an array name,
     not a term whose value is an array.
     The exact constraints are explained below.
     If any of these constraints is not satisfied,
     the array analysis fails,
     causing an error that stops the analysis and ATJ.
     Currently these are hard errors,
     but they are distinct from the `internal errors'
     that are so indicated in the error messages of some ATJ code.
     The internal errors are expected to never happen;
     if they do, the reason is an implementation bug.
     On the other hand, errors from the array analysis are expected to happen:
     they are a form of input validation,
     but one that is ``semantically deep'' and can only be performed
     during pre-translation, and not as part of input processing.")
   (xdoc::p
    "Recall that this array analysis takes place
     after the type annotations.
     Thus, terms are unwrapped as they are analyzed.")
   (xdoc::p
    "Besides the list of array names,
     the analysis of a term also returns the list of types of the term.
     This is simply obtained from the type annotations,
     but it is used by the array analysis,
     and so returning it explicitly is useful in the recursive calls
     of the analysis code.")
   (xdoc::p
    "If the term being analyzed is a variable,
     we look at its type.
     Since we handle @(tsee mv-let) specially (see below),
     we expect that all the variables that we encounter ``directly''
     (i.e. not the @(tsee mv-let) variable @('mv'))
     will have singleton type lists:
     we use @(tsee atj-type-list-to-type)
     to convert singletons to single types,
     which causes an error should the type list not be a singleton
     (this would be an implementation error).
     If the type of the variable is an array,
     the result of the array analysis is
     the singleton list with the name of the variable.
     Otherwise, the result of the array analysis is
     the singleton list with @('nil').")
   (xdoc::p
    "If the term being analyzed is a quoted constant,
     we return the singleton list with @('nil').
     A quoted constant is never an array:
     we exclusively use ACL2 functions like @(tsee byte-array-of-length)
     to construct arrays;
     a quoted constant always has an @(':acl2') type,
     according to the type annotations.")
   (xdoc::p
    "If the term being analyzed is neither a variable nor a quoted constant,
     we check whether it is a (type-annotated) @(tsee mv-let) call.
     This is handled by the separate function @('atj-analyze-arrays-in-mv-let'),
     whose first result is a boolean flag that indicates success of failure.
     In case of success,
     the calling function @('atj-analyze-arrays-in-term')
     forwards the second result of @('atj-analyze-arrays-in-mv-let');
     in case of failure, @('atj-analyze-arrays-in-term')
     handles the other kinds of function calls,
     including calls of lambda expressions other than @(tsee mv-let)s,
     which are already handled by @('atj-analyze-arrays-in-mv-let').")
   (xdoc::p
    "If the term being analyzed is neither a variable nor a quoted constant,
     we check whether it is a call of @(tsee mv-let),
     in which case we handle it as described below,
     but first we explain the handling of the other kinds of function calls.")
   (xdoc::p
    "If the term being analyzed is an @(tsee if) call,
     we recursively analyze its three arguments.
     If the test returns an array, the analysis fails:
     we do not allow arrays as @(tsee if) tests.
     The `then' and `else' branches must have the same inferred arrays,
     otherwise the analysis fails;
     that is, no matter which branch is taken,
     the same arrays must be returned.")
   (xdoc::p
    "If the term being analyzed is a call of a function other than @(tsee if),
     we recursively analyze all the arguments.
     We do so with a separate function, @('atj-analyze-arrays-in-args'),
     mutually recursive with @('atj-analyze-arrays-in-term').
     Each of these arguments must be necessarily single-valued
     (see also @(tsee atj-type-annotate-term)),
     so the two lists returned by @('atj-analyze-arrays-in-args')
     are interpreted differently from @('atj-analyze-arrays-in-term'):
     the former are the concatenations of the singleton lists
     inferred for each of the arguments,
     while the latter are lists that apply to the whole term.
     The array analysis fails if two of arguments have the same array name:
     this situation means that the same array is aliased (in Java)
     and possibly subjected to different modifications through the aliases.")
   (xdoc::p
    "If the term being analyzed is an @(tsee mv) call,
     we just return the list of array arguments.
     This is a multi-valued term.")
   (xdoc::p
    "If the term being analyzed is a call
     of a function other than @(tsee if) and @(tsee mv),
     we look up its formals, function type, and output arrays.
     The function type is chosen based on the types of the arguments,
     in the same way as in @(tsee atj-type-annotate-term).
     We match the array formal parameters of the function
     to the array names inferred for the actual arguments
     (see the discussion in @(tsee atj-pre-translation-array-analysis)),
     creating an alist.
     Then we go through the function's output arrays
     (whose names match the array formal parameters
     that may be modified by the function and returned,
     and we use the alist mentioned just above
     to compute the output arrays of the call.
     For example, suppose that we have a call of @('f'),
     and that @('f') has two array formal parameters @('x') and @('y').
     Suppose that the array names inferred
     for the corresponding actual arguments are @('a') and @('b').
     Then we construct first the alist @('((x . a) (y. b))'),
     and then we go through the output arrays of $('f'),
     which may include @('x') and @('y') (not necessarily in that order),
     and for each element of the list we generate
     @('a') if the element is @('x'),
     @('b') if the element is @('y'),
     and @('nil') otherwise.
     The latter @('nil') may indicate
     either a non-array result
     or an array newly created by @('f') (directly or indirectly).
     Note that all of this works also when @('a') and/or @('b') is @('nil'),
     which means that we are passing newly created arrays to @('f'):
     the results corresponding to @('x') and @('y') may then be @('nil'),
     which indicates arrays that have been
     newly created, possibly modified, and not given names yet
     (names are given then they are bound to variables).")
   (xdoc::p
    "If the term being analyzed is a call of a lambda expression
     (but not of the @(tsee mv-let) form, which is explained below),
     we ensure that each array argument with a non-@('nil') name
     is assigned (in the sense of @(tsee let))
     to a variable with the same name:
     the variables are the formal parameters of the lambda expression.
     That is, we go through argument arrays and lambda's formal parameters,
     and ensure that they match as just explained.
     This is an important constraint checked by the array analysis,
     namely that (within each function), each array has a unique name.
     One cannot ``rename'' an array, just like one cannot ``rename'' a stobj:
     a stobj has the same name everywhere (not only within each function).
     It is of course permitted to assign non-arrays to variables liberally.
     Then we return the result of recursively analyzing
     the body of the lambda expression.
     Note that, because of the array naming consistency checks explained above,
     in the body of the lambda expressions the arrays have
     the same names as they did outside the body.
     Some newly created arrays outside the body may have a name inside the body,
     so that their single-threaded use can be checked inside the body.")
   (xdoc::p
    "To handle @(tsee mv-let), we decompose it into its constituents.
     We recursively analyze the subterm that returns a multiple value,
     obtaining a list of output arrays.
     We ensure that all the non-@('nil') elements of this list
     are bound to some variable in the @(tsee mv-let);
     we ensure that by going through the list,
     with a variable that holds the current position in the list,
     and checking that for every non-@('nil') element
     its position is among the indices returned by
     the decomposition of the @(tsee mv-let).
     If some named array were modified and then dropped
     (i.e. not assigned to any variable by the @(tsee mv-let)),
     then its modifications could not be returned
     and it would mean that it may not be used single-threadedly.
     As we perform the above check that no arrays are dropped,
     we also check that the arrays with non-@('nil') names
     are assigned to variables with the same names,
     as with other lambda expressions.
     Then, as with other lambda expressions, we return the result
     of recursively analyzing the body of the @(tsee mv-let)."))

  (define atj-analyze-arrays-in-term ((term pseudo-termp) (wrld plist-worldp))
    :returns (mv (arrays symbol-listp)
                 (types atj-type-listp))
    (b* ((wrapped-term term)
         ((mv term & dst-types) (atj-type-unwrap-term term))
         ((when (pseudo-term-case term :null))
          (raise "Internal error: null term.")
          (mv (list nil) (list (atj-type-irrelevant))))
         ((when (pseudo-term-case term :var))
          (b* ((typed-var (pseudo-term-var->name term))
               ((mv var types) (atj-type-unannotate-var typed-var))
               (type (atj-type-list-to-type types)))
            (if (atj-type-case type :jprimarr)
                (mv (list var) (list type))
              (mv (list nil) dst-types))))
         ((when (pseudo-term-case term :quote))
          (mv (list nil) dst-types))
         ((mv success arrays types)
          (atj-analyze-arrays-in-mv-let wrapped-term wrld))
         ((when success) (mv arrays types))
         (fn (pseudo-term-call->fn term))
         ((when (eq fn 'if))
          (b* ((args (pseudo-term-call->args term))
               ((unless (and (consp args)
                             (consp (cdr args))
                             (consp (cddr args))))
                (raise "Internal error: ~
                        IF call ~x0 does not have three arguments."
                       term)
                (mv (list nil) (list (atj-type-irrelevant))))
               (test (first args))
               (then (second args))
               (else (third args))
               ((mv & test-types) (atj-analyze-arrays-in-term test wrld))
               ((mv then-arrays then-types) (atj-analyze-arrays-in-term then
                                                                        wrld))
               ((mv else-arrays else-types) (atj-analyze-arrays-in-term else
                                                                        wrld))
               ((unless (= (len then-types) (len else-types)))
                (raise "Internal error: ~
                        the branches of ~x0 have ~
                        different numbers of types ~x1 and ~x2."
                       term then-types else-types)
                (mv (list nil) (list (atj-type-irrelevant))))
               (test-type (atj-type-list-to-type test-types))
               ((when (atj-type-case test-type :jprimarr))
                (raise "Array analysis failure: ~
                        an array cannot be used as the test of ~x0."
                       term)
                (mv (list nil) (list (atj-type-irrelevant))))
               ((unless (equal then-arrays else-arrays))
                (raise "Array analysis failure: ~
                        the branches of ~x0 have ~
                        different arrays ~x1 and ~x2."
                       term then-arrays else-arrays)
                (mv (list nil) (list (atj-type-irrelevant)))))
            (mv then-arrays dst-types)))
         (args (pseudo-term-call->args term))
         ((mv arg-arrays arg-types) (atj-analyze-arrays-in-args args wrld))
         ((unless (no-duplicatesp-eq (remove-eq nil arg-arrays)))
          (raise "Array analysis failure: ~
                  the arguments of the call ~x0 ~
                  contain duplicate arrays ~x1."
                 term (remove-eq nil arg-arrays))
          (mv (list nil) (list (atj-type-irrelevant))))
         ((when (and (eq fn 'mv)
                     (>= (len args) 2))) ; always true
          (mv arg-arrays arg-types))
         ((when (pseudo-term-case term :fncall))
          (b* ((formals (formals+ fn wrld))
               ((unless (= (len arg-arrays) (len formals)))
                (raise "Internal error: ~
                        the number of formals ~x0 of ~x1 differs from ~
                        the number of inferred argument arrays ~x2."
                       formals fn arg-arrays)
                (mv (list nil) (list (atj-type-irrelevant))))
               (fn-info (atj-get-function-type-info fn t wrld))
               (main-fn-type (atj-function-type-info->main fn-info))
               (other-fn-types (atj-function-type-info->others fn-info))
               (all-fn-types (cons main-fn-type other-fn-types))
               (fn-type? (atj-function-type-of-min-input-types arg-types
                                                               all-fn-types))
               (fn-type (or fn-type? main-fn-type))
               (fn-out-arrays (atj-function-type->arrays fn-type))
               ((unless (consp fn-out-arrays))
                (raise "Internal error: ~
                        empty list of output arrays for ~x0."
                       fn)
                (mv (list nil) (list (atj-type-irrelevant))))
               (in-arrays
                (atj-analyze-arrays-input-alist formals arg-arrays arg-types))
               (out-arrays
                (atj-analyze-arrays-output-list fn-out-arrays in-arrays)))
            (mv out-arrays dst-types)))
         (formals (pseudo-lambda->formals fn))
         (formals (atj-type-unannotate-vars formals))
         (- (atj-analyze-arrays-check-lambda arg-arrays formals)))
      (atj-analyze-arrays-in-term (pseudo-lambda->body fn) wrld))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-ANALYZE-ARRAYS-MV-LET decreases:
    :measure (two-nats-measure (pseudo-term-count term) 1))

  (define atj-analyze-arrays-in-args ((args pseudo-term-listp)
                                      (wrld plist-worldp))
    :returns (mv (arrays (and (symbol-listp arrays)
                              (equal (len arrays) (len args))))
                 (types (and (atj-type-listp types)
                             (equal (len types) (len args)))))
    (b* (((when (endp args)) (mv nil nil))
         ((mv first-arrays first-types) (atj-analyze-arrays-in-term (car args)
                                                                    wrld))
         (first-array (car first-arrays))
         (first-type (atj-type-list-to-type first-types))
         ((mv rest-arrays rest-types) (atj-analyze-arrays-in-args (cdr args)
                                                                  wrld)))
      (mv (cons first-array rest-arrays)
          (cons first-type rest-types)))
    :measure (two-nats-measure (pseudo-term-list-count args) 0))

  (define atj-analyze-arrays-in-mv-let ((term pseudo-termp) (wrld plist-worldp))
    :returns (mv (success booleanp)
                 (arrays symbol-listp)
                 (types atj-type-listp))
    (b* (((mv mv-let-p & mv-term vars indices body-term)
          (atj-check-annotated-mv-let-call term))
         ((unless mv-let-p) (mv nil nil nil))
         ((unless ; temporary check for termination, will be removed:
              (and (< (pseudo-term-count mv-term)
                      (pseudo-term-count term))
                   (< (pseudo-term-count body-term)
                      (pseudo-term-count term))))
          (raise "Internal error: ~
                  one or both of the terms ~x0 and ~x1 ~
                  are not smaller than the term ~x2."
                 mv-term body-term term)
          (mv nil nil nil))
         ((mv mv-arrays &) (atj-analyze-arrays-in-term mv-term wrld))
         ((when (= (len mv-arrays) 1)) (mv nil nil nil))
         (vars (atj-type-unannotate-vars vars))
         (- (atj-analyze-arrays-check-mv-lambda mv-arrays 0 vars indices))
         ((mv arrays types)
          (atj-analyze-arrays-in-term body-term wrld)))
      (mv t arrays types))
    :measure (two-nats-measure (pseudo-term-count term) 0))

  :prepwork

  ((define atj-analyze-arrays-input-alist ((formals symbol-listp)
                                           (arg-arrays symbol-listp)
                                           (arg-types atj-type-listp))
     :guard (and (= (len arg-arrays) (len formals))
                 (= (len arg-types) (len formals)))
     :returns (alist symbol-symbol-alistp :hyp (and (symbol-listp formals)
                                                    (symbol-listp arg-arrays)))
     (cond ((endp formals) nil)
           ((atj-type-case (car arg-types) :jprimarr)
            (acons (car formals)
                   (car arg-arrays)
                   (atj-analyze-arrays-input-alist (cdr formals)
                                                   (cdr arg-arrays)
                                                   (cdr arg-types))))
           (t (atj-analyze-arrays-input-alist (cdr formals)
                                              (cdr arg-arrays)
                                              (cdr arg-types))))
     :prepwork ((local (include-book "std/lists/len" :dir :system))))

   (define atj-analyze-arrays-output-list ((fn-out-arrays symbol-listp)
                                           (in-arrays symbol-symbol-alistp))
     :returns (list symbol-listp :hyp :guard)
     (cond ((endp fn-out-arrays) nil)
           (t (cons (cdr (assoc-eq (car fn-out-arrays) in-arrays))
                    (atj-analyze-arrays-output-list (cdr fn-out-arrays)
                                                    in-arrays))))
     ///
     (more-returns
      (list consp
            :hyp (consp fn-out-arrays)
            :rule-classes :type-prescription))
     (defret len-of-atj-analyze-arrays-output-list
       (equal (len list)
              (len fn-out-arrays))))

   (define atj-analyze-arrays-check-lambda ((arg-arrays symbol-listp)
                                            (formals symbol-listp))
     :guard (= (len formals) (len arg-arrays))
     :returns (nothing null)
     (b* (((when (endp arg-arrays)) nil)
          (arg-array (car arg-arrays))
          ((when (not arg-array))
           (atj-analyze-arrays-check-lambda (cdr arg-arrays) (cdr formals)))
          ((when (eq arg-array (car formals)))
           (atj-analyze-arrays-check-lambda (cdr arg-arrays) (cdr formals))))
       (raise "Array analysis failure: ~
               cannot assign the array ~x0 to the variable ~x1."
              arg-array (car formals))))

   (define atj-analyze-arrays-check-mv-lambda ((mv-arrays symbol-listp)
                                               (mv-index natp)
                                               (vars symbol-listp)
                                               (indices nat-listp))
     :guard (= (len vars) (len indices))
     :returns (nothing null)
     (b* (((when (endp mv-arrays)) nil)
          (mv-array (car mv-arrays))
          ((when (not mv-array))
           (atj-analyze-arrays-check-mv-lambda (cdr mv-arrays)
                                               (1+ mv-index)
                                               vars
                                               indices))
          (pos-of-index (index-of mv-index indices))
          ((unless (natp pos-of-index))
           (raise "Array analysis failure: ~
                   the array ~x0 must be assigned to a variable."
                  mv-array))
          (var-at-pos (nth pos-of-index vars))
          ((unless (eq var-at-pos mv-arrays))
           (raise "Array analysis failure: ~
                   the array ~x0 is assigned to variable ~x1."
                  mv-array var-at-pos)))
       (atj-analyze-arrays-check-mv-lambda (cdr mv-arrays)
                                           (1+ mv-index)
                                           vars
                                           indices))
     :prepwork ((local
                 (include-book "std/typed-lists/symbol-listp" :dir :system))))

   (local (in-theory (disable pseudo-termp))))

  :verify-guards nil ; done below

  ///

  (defret-mutual consp-of-atj-analyze-arrays-in-term.arrays
    (defret consp-of-atj-analyze-arrays-in-term.arrays
      (consp arrays)
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-term)
    (defret consp-of-atj-analyze-arrays-in-args.arrays
      (consp arrays)
      :hyp (consp args)
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-args)
    (defret consp-of-atj-analyze-arrays-in-mv-let.arrays
      (consp arrays)
      :hyp (mv-nth 0 (atj-analyze-arrays-in-mv-let term wrld))
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-mv-let))

  (defret-mutual consp-of-atj-analyze-arrays-in-term.types
    (defret consp-of-atj-analyze-arrays-in-term.types
      (consp types)
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-term)
    (defret consp-of-atj-analyze-arrays-in-args.types
      (consp types)
      :hyp (consp args)
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-args)
    (defret consp-of-atj-analyze-arrays-in-mv-let.types
      (consp types)
      :hyp (mv-nth 0 (atj-analyze-arrays-in-mv-let term wrld))
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-mv-let))

  (local (include-book "std/typed-lists/symbol-listp" :dir :system))

  (verify-guards atj-analyze-arrays-in-term
    :hints (("Goal"
             :in-theory
             (enable len-of-atj-check-annotated-mv-let.vars/indices)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-analyze-arrays-in-formals+body ((formals symbol-listp)
                                            (body pseudo-termp)
                                            (out-arrays symbol-listp)
                                            (wrld plist-worldp))
  :returns (nothing null)
  :short "Array analysis of ACL2 function bodies."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top level of the array analysis.
     We analyze the body of the function,
     and compare the inferred arrays
     with the ones declared for the function
     (via @(tsee atj-main-function-type) and @(tsee atj-other-function-type)).
     The inferred arrays must be the same as the declared ones,
     except that the inferred ones may have names for newly created arrays.
     More precisely, for each position in the lists:
     if the declared array name at that position is not @('nil')
     then the inferred array name at that position must be the same;
     if the declared array name at that position is @('nil'),
     then the inferred array name at that position may be either @('nil')
     or a new array name that is not among the function's formal parameters.
     In the latter case, it means that the function body has
     directly or indirectly created a new array and assigned it to a variable,
     which is then returned as result of array analysis,
     but the declared array names are only the ones
     that match some formal parameter names.")
   (xdoc::p
    "These checks tie the intraprocedural array analysis
     (performed by @(tsee atj-analyze-arrays-in-term))
     with the output arrays assigned by the user to the functions.
     Recall that
     @(tsee atj-main-function-type) and @(tsee atj-other-function-type)
     check the correctness of the declared types
     but not of the declared output arrays,
     aside from relatively simple constraints such as the fact that
     the non-@('nil') output arrays are unique,
     correspond to some formal parameters with the same array types,
     etc.
     By checking that the inferred arrays are consistent with the declared ones,
     which are used to analyze the callers of the function,
     we ensure that all the arrays potentially modified by the function
     are returned by the function,
     so that the callers have to receive them and return them as well.
     This is similar to ACL2's stobj analysis.")
   (xdoc::p
    "This @('atj-analyze-arrays-in-formals+body') returns nothing,
     but its execution stops with a hard error if the array analysis fails."))
  (b* (((mv arrays &) (atj-analyze-arrays-in-term body wrld))
       ((unless (= (len arrays) (len out-arrays)))
        (raise "Internal error: ~
                the length of the inferred arrays ~x0 ~
                differs from the length of the declared arrays ~x1."
               arrays out-arrays))
       (pass
        (atj-analyze-arrays-in-formals+body-aux formals arrays out-arrays)))
    (if pass
        nil
      (raise "Array analysis failure: ~
              the function with formals ~x0 and body ~x1 ~
              returns the inferred arrays ~x2, ~
              which are inconsistent with the declared arrays ~x3."
             formals body arrays out-arrays)))

  :prepwork
  ((define atj-analyze-arrays-in-formals+body-aux ((formals symbol-listp)
                                                   (inferred symbol-listp)
                                                   (declared symbol-listp))
     :guard (= (len inferred) (len declared))
     :returns (yes/no booleanp)
     (or (endp inferred)
         (b* ((inf (car inferred))
              (decl (car declared)))
           (and (or (eq inf decl)
                    (and (null decl)
                         (not (member-eq inf formals))))
                (atj-analyze-arrays-in-formals+body-aux formals
                                                        (cdr inferred)
                                                        (cdr declared))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-var-reuse
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          marking of reusable lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "Consider a function body of the form")
   (xdoc::codeblock
    "(let ((x ...))"
    "  (let ((x ...))"
    "    (f x)))")
   (xdoc::p
    "The second @('x') bound by @(tsee let)
     ``overwrites'' the first one completely,
     because in the rest of the term (namely, @('(f x)'))
     only the second one is referenced, not the first one.")
   (xdoc::p
    "In contrast, consider a function body of the form")
   (xdoc::codeblock
    "(let ((x ...))"
    "  (f (let ((x ...)) (f x)) (g x)))")
   (xdoc::p
    "Here, the second @('x') bound by @(tsee let)
     ``overwrites'' the second one only partially, namely in @('(f x)'),
     but other parts of the rest of the term, namely @('(g x)'),
     reference the first one.")
   (xdoc::p
    "When we translate ACL2 to Java,
     @(tsee let)-bound variables become Java local variables.
     In the first example above,
     provided that the two @('x') variables have the same type,
     the Java code can use the same local variable for both:
     for the first binding, the Java code declares and initializes the variable;
     for the second binding, the Java code assigns to the variable,
     destructively updating it,
     which is safe because the old value is no longer needed.
     However, in the second example above,
     there have to be two distinct Java local variables,
     say @('x1') and @('x2'),
     corresponding to the two bound variables:
     both are declared and initialized,
     none can be safely destructively updated.")
   (xdoc::p
    "This pre-translation step analyzes terms
     to find out which lambda-bound (i.e. @(tsee let)-bound) variables
     can be reused and destructively updated.
     The lambda-bound variables are marked as either `new' or `old':
     the first marking means that
     the variable must be a new Java local variable
     that is declared and initilized;
     the second marking means that
     the variable can be an old Java local variable
     that is destructively assigned.
     These markings provide ``instructions'' to the ACL2-to-Java translation.")
   (xdoc::p
    "In the first example above the markings would be")
   (xdoc::codeblock
    "(let (([n]x ...))"
    "  (let (([o]x ...))"
    "    (f [o]x)))")
   (xdoc::p
    "while in the second example above the markings would be")
   (xdoc::codeblock
    "(let (([n]x ...))"
    "  (f (let (([n]x ...)) (f [n]x)) (g [n]x)))")
   (xdoc::p
    "Note that, as we mark the lambda-bound variables,
     we must mark in the same way the occurrences in the lambda bodies,
     to maintain the well-formedness of the ACL2 terms.")
   (xdoc::p
    "This pre-translation step must be performed after the "
    (xdoc::seetopic "atj-pre-translation-type-annotation"
                    "type annotation step")
    ", so that types are kept into account:
      a variable can be reused only if
      it has the same type in both lambda formal parameters.
      Since the type annotation step adds types to variable names,
      by comparing names for equality we also compare their types for equality.
      If two variables have different types,
      they also have different names (since the name includes the type).")
   (xdoc::p
    "After this translation step, the "
    (xdoc::seetopic "atj-pre-translation-var-renaming"
                    "variable renaming step")
    " takes care of renaming apart ACL2 variables with the same name
      that are both marked as `new'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-var-new ((var symbolp))
  :returns (marked-var symbolp)
  :short "Mark a variable as `new'."
  (packn-pos (list "[N]" var) var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-vars-new ((vars symbol-listp))
  :returns (marked-vars symbol-listp)
  :short "Lift @(tsee atj-mark-var-new) to lists."
  (cond ((endp vars) nil)
        (t (cons (atj-mark-var-new (car vars))
                 (atj-mark-vars-new (cdr vars)))))
  ///

  (defret len-of-atj-mark-vars-new
    (equal (len marked-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-var-old ((var symbolp))
  :returns (marked-var symbolp)
  :short "Mark a variable as `old'."
  (packn-pos (list "[O]" var) var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-unmark-var ((var symbolp))
  :returns (mv (unmarked-var symbolp)
               (new? booleanp))
  :short "Decompose a marked variable into its marking and its unmarked name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The marking is a boolean: @('t') for `new', @('nil') for `old'."))
  (b* ((string (symbol-name var))
       ((unless (and (>= (length string) 5)
                     (member-equal (subseq string 0 3) '("[N]" "[O]"))))
        (raise "Internal error: ~x0 has the wrong format." var)
        (mv nil nil))
       (new? (eql (char string 1) #\N))
       (unmarked-string (subseq string 3 (length string)))
       (unmarked-var (intern-in-package-of-symbol unmarked-string var)))
    (mv unmarked-var new?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-unmark-vars ((vars symbol-listp))
  :returns (mv (unmarked-vars symbol-listp)
               (new?s boolean-listp))
  :short "Lift @(tsee atj-unmark-var) to lists."
  (b* (((when (endp vars)) (mv nil nil))
       ((mv var new?) (atj-unmark-var (car vars)))
       ((mv vars new?s) (atj-unmark-vars (cdr vars))))
    (mv (cons var vars) (cons new? new?s)))
  ///

  (defret len-of-atj-unmark-vars.unmarked-vars
    (equal (len unmarked-vars)
           (len vars)))

  (defret len-of-atj-unmark-vars.new?s
    (equal (len new?s)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-mark-term
  :short "Mark the variables in a term as `new' or `old'."
  :long
  (xdoc::topstring
   (xdoc::p
    "Marking a variable as `new' is always ``safe'',
     because it is always safe to introduce a new Java local variable.
     On the other hand, marking a variable as `old' requires care,
     to prevent a Java local variable to be erroneously reused.
     To understand this marking algorithm,
     one has to keep in mind how ACL2 terms are translated to Java:
     see @(tsee atj-gen-shallow-term) and companions.
     This is a delicate algorithm:
     a proof of correctness would be very beneficial.")
   (xdoc::p
    "Two conditions are necessary for reusing a variable:
     (i) the variable must be in scope (i.e. exist and be accessible); and
     (ii) the previous value of the variable must not be used afterwards.
     The parameters @('vars-in-scope') and @('vars-used-after')
     support the checking of these conditions.")
   (xdoc::p
    "The parameter @('vars-in-scope') consists of the variables in scope
     at the point where the term under consideration occurs.
     At the top level (see @(tsee atj-mark-formals+body)),
     it is intialized with the (unmarked) formal parameters
     of the ACL2 function whose formal parameters and body are being marked:
     indeed, the formal parameters of a function are in scope for the body.
     As we descend into subterms, when we encounter a lambda expression,
     we extend @('vars-in-scope') with its (unmarked) formal parameters;
     only the ones that are marked as `new' actually extend the scope,
     while the ones marked as `old' were already in @('vars-in-scope').
     The generated Java code evaluates functions' actual arguments
     left-to-right:
     thus, local variables introduced (for lambda expressions in) an argument
     are generally (see exception shortly) in scope for successive arguments.
     Therefore, @('vars-in-scope') is threaded through the marking functions
     (i.e. passed as argument and returned, possibly updated, as result).
     When processing a lambda expression applied to arguments,
     @('vars-in-scope') is threaded first through the arguments,
     and then through the body (which is evaluated after the argument),
     after augmenting it with the formal parameters.
     The exception mentioned above is for @(tsee if),
     which is turned into a Java @('if')
     whose branches are Java blocks:
     Java variables declared inside these blocks
     have a more limited scope (namely, the respective block),
     and therefore should not be added to the @('vars-in-scope')
     that is passed to mark terms after the @(tsee if).
     The variables introduced in the test of the @(tsee if)
     are declared outside the branches' blocks,
     and so they are threaded through.
     The @('vars-in-scope') resulting from marking the test of the @(tsee if)
     is passed to mark both branches,
     but their returned @('vars-in-scope') is ignored.
     The code for @(tsee if) is a bit more complicated
     because of the special treatment of @('(if a a b)') terms,
     which are treated as @('(or a b)'):
     the Java code generated for this case is a little different
     (see @(tsee atj-gen-shallow-or-call)),
     but the treatment of @('vars-in-scope')
     is essentially the same as just explained
     (there is no `then' branch to mark, because it is the same as the test,
     which has already been marked).")
   (xdoc::p
    "The parameter @('vars-used-after') consists of the variables
     that occur free (i.e. whose current value is used)
     ``after'' the term under consideration.
     At the top level (see @(tsee atj-mark-formals+body)),
     it is initialized with @('nil'),
     because no variables are used after evaluating the body of the function.
     As we descend into subterms,
     @('vars-used-after') is extended as needed,
     based on the ``neighboring'' subterms
     that will be evaluated (in the generated Java code)
     after the subterm under consideration.
     In particular, when marking an actual argument of a function call,
     @('vars-used-after') is extended with all the free variables
     of the actual arguments of the same function call
     that occur after the one being marked;
     recall that arguments are evaluated left-to-right
     in the generated Java code.
     The function @('atj-mark-terms'),
     which is used to mark the actual arguments of a function call,
     augments @('vars-used-after') with the free variables
     in the @(tsee cdr) of the current list of arguments;
     this is somewhat inefficient,
     as the same free variables are collected repeatedly
     as the argument terms are processed,
     but terms are not expected to be too large in the near future;
     this may be eventually optimized when needed.
     Calls of @(tsee if) are treated a little differently,
     because the arguments are not evaluated left-to-right
     in the generated Java code:
     when marking the test, we augment @('vars-used-after')
     with all the free variables in the branches;
     when marking either branch, we use the same @('vars-used-after')
     that was passed for the @(tsee if),
     because the two branches are independent.
     The @(tsee or) form of @(tsee if) is treated slightly differently as usual,
     but the essence is the same.
     Unlike @('vars-in-scope'), @('var-used-after') is not threaded through;
     it is simply passed down, and augmented as needed.
     The body of a lambda expression is evaluated after its actual arguments:
     thus, when marking the actual arguments of a lambda expression
     we must augment @('vars-used-after')
     with the free variables of the lambda expression,
     i.e. the free variables in the body minus the formal parameters.")
   (xdoc::p
    "As we mark the formal parameters of a lambda expression,
     we need to mark in the same way
     all the references to these variables in the body of the lambda expression.
     For this purpose, we pass around a mapping, @('vars-to-mark-new'),
     from (unmarked) variables to markings:
     this could be an alist from symbols to booleans,
     but we isomorphically use lists (treated as sets) of symbols instead,
     which are the variable marked as `new',
     while the variables not in the list are marked as `old'.
     When the term to be marked is a variable,
     we look it up in this list, and mark it accordingly.")
   (xdoc::p
    "When the term to be marked is a quoted constant,
     it is obviously left unchanged.")
   (xdoc::p
    "When the term to be marked is a function call,
     we first treat the @(tsee if) (and @(tsee or)) case separately.
     We mark the test, and after that the two branches.
     The handling of @('vars-in-scope') and @('vars-used-after') for this case
     has been explained above.")
   (xdoc::p
    "For all other function calls, which are strict,
     we first mark the actual arguments,
     treating @('vars-in-scope') and @('vars-used-after')
     as explained above.
     For calls of named functions, we are done at this point:
     we put the named function in front of the marked arguments and return.
     For calls of lambda expression,
     we use the auxiliary function @('atj-mark-lambda-formals')
     to decide which formal parameters should be marked as `new' or `old'.
     We mark the parameter as `old' (indicating that the variable can be reused)
     iff the following three conditions hold.
     The first condition is that the variable must be in scope;
     note that variables have already been annotated with types at this point,
     and so by testing variable names we also test their types,
     which is needed for Java
     (i.e. we could not reuse a Java variable of type @('Acl2Symbol')
     to store a value of type @('Acl2String')).
     The second condition is that the variable is not used
     after the lambda call term, i.e. it is not in @('vars-used-after'):
     otherwise, we would overwrite something that was supposed to be used later,
     with incorrect results in general.
     The third condition is that the variable is not free
     in any of the actual arguments that correspond to
     the formal parameters of the lambda expression
     that come just after the one being marked:
     this is because, in the generated Java code,
     the lambda variables are assigned one after the other,
     and therefore we should not overwrite a variable
     that may be needed afterwards.
     For instance, consider a swap @('(let ((x y) (y x)) ...)'):
     @('x') cannot be reused
     (even if it is in scope and not used after the @(tsee let))
     because it must be assigned to @('y') after @('y') is assigned to @('x')
     (Java does not support parallel assignment);
     on the other hand, @('y') could be reused,
     if it is in scope and not used after the @(tsee let),
     because at the time of assigning to @('y')
     its (previous) value has already been assigned to @('x').")
   (xdoc::p
    "When analyzing the arguments of a call of a lambda expression,
     we need to extend @('vars-used-after') with
     the free variables in the lambda expression
     (i.e. the free variables in the body minus the formal arguments).
     This is because the body of the lambda expression
     is evaluated after the arguments of the call.
     We store the extended list into @('vars-used-after-args').
     But when we process the body of the lambda expression after that,
     we go back to using @('vars-used-after'),
     which excludes the variables used in the lambda expression,
     and only includes the variables used
     after the call of the lambda expression."))

  (define atj-mark-term ((term pseudo-termp)
                         (vars-in-scope symbol-listp)
                         (vars-used-after symbol-listp)
                         (vars-to-mark-new symbol-listp))
    :returns (mv (marked-term pseudo-termp)
                 (new-vars-in-scope symbol-listp))
    (b* (((unless (mbt (pseudo-termp term))) (mv nil nil))
         ((unless (mbt (symbol-listp vars-in-scope))) (mv nil nil))
         ((unless (mbt (symbol-listp vars-used-after))) (mv nil nil))
         ((unless (mbt (symbol-listp vars-to-mark-new))) (mv nil nil))
         ((when (variablep term))
          (if (member-eq term vars-to-mark-new)
              (mv (atj-mark-var-new term) vars-in-scope)
            (mv (atj-mark-var-old term) vars-in-scope)))
         ((when (fquotep term)) (mv term vars-in-scope))
         (fn (ffn-symb term))
         ((when (eq fn 'if))
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3)))
            (if (equal test then)
                (b* ((vars-used-after-test (union-eq vars-used-after
                                                     (all-vars-open else)))
                     ((mv test
                          vars-in-scope) (atj-mark-term test
                                                        vars-in-scope
                                                        vars-used-after-test
                                                        vars-to-mark-new))
                     ((mv else &) (atj-mark-term else
                                                 vars-in-scope
                                                 vars-used-after
                                                 vars-to-mark-new)))
                  (mv `(if ,test ,test ,else)
                      vars-in-scope))
              (b* ((vars-used-after-test (union-eq vars-used-after
                                                   (all-vars-open-lst
                                                    (list then else))))
                   ((mv test
                        vars-in-scope) (atj-mark-term test
                                                      vars-in-scope
                                                      vars-used-after-test
                                                      vars-to-mark-new))
                   ((mv then &) (atj-mark-term then
                                               vars-in-scope
                                               vars-used-after
                                               vars-to-mark-new))
                   ((mv else &) (atj-mark-term else
                                               vars-in-scope
                                               vars-used-after
                                               vars-to-mark-new)))
                (mv `(if ,test ,then ,else)
                    vars-in-scope)))))
         (args (fargs term))
         (vars-used-after-args
          (if (symbolp fn)
              vars-used-after
            (union-eq vars-used-after
                      (set-difference-eq (all-vars-open (lambda-body fn))
                                         (lambda-formals fn)))))
         ((mv marked-args vars-in-scope) (atj-mark-terms args
                                                         vars-in-scope
                                                         vars-used-after-args
                                                         vars-to-mark-new))
         ((when (symbolp fn)) (mv (fcons-term fn marked-args)
                                  vars-in-scope))
         (formals (lambda-formals fn))
         ((mv marked-formals
              vars-to-mark-new) (atj-mark-lambda-formals formals
                                                         args
                                                         vars-in-scope
                                                         vars-used-after
                                                         vars-to-mark-new))
         (vars-in-scope (union-eq formals vars-in-scope))
         ((mv marked-body
              vars-in-scope) (atj-mark-term (lambda-body fn)
                                            vars-in-scope
                                            vars-used-after
                                            vars-to-mark-new)))
      (mv (fcons-term (make-lambda marked-formals marked-body)
                      marked-args)
          vars-in-scope)))

  (define atj-mark-terms ((terms pseudo-term-listp)
                          (vars-in-scope symbol-listp)
                          (vars-used-after symbol-listp)
                          (vars-to-mark-new symbol-listp))
    :returns (mv (marked-terms (and (pseudo-term-listp marked-terms)
                                    (equal (len marked-terms)
                                           (len terms))))
                 (new-vars-in-scope symbol-listp))
    (b* (((unless (mbt (pseudo-term-listp terms)))
          (mv (repeat (len terms) nil) nil))
         ((unless (mbt (symbol-listp vars-in-scope)))
          (mv (repeat (len terms) nil) nil))
         ((unless (mbt (symbol-listp vars-used-after)))
          (mv (repeat (len terms) nil) nil))
         ((unless (mbt (symbol-listp vars-to-mark-new)))
          (mv (repeat (len terms) nil) nil))
         ((when (endp terms)) (mv nil vars-in-scope))
         (first-term (car terms))
         (rest-terms (cdr terms))
         (vars-used-after-first-term (union-eq vars-used-after
                                               (all-vars-open-lst rest-terms)))
         ((mv marked-first-term
              vars-in-scope) (atj-mark-term first-term
                                            vars-in-scope
                                            vars-used-after-first-term
                                            vars-to-mark-new))
         ((mv marked-rest-terms
              vars-in-scope) (atj-mark-terms rest-terms
                                             vars-in-scope
                                             vars-used-after
                                             vars-to-mark-new)))
      (mv (cons marked-first-term marked-rest-terms)
          vars-in-scope)))

  :prepwork

  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))

   (define atj-mark-lambda-formals ((formals symbol-listp)
                                    (actuals pseudo-term-listp)
                                    (vars-in-scope symbol-listp)
                                    (vars-used-after symbol-listp)
                                    (vars-to-mark-new symbol-listp))
     :guard (= (len formals) (len actuals))
     :returns (mv (marked-formals (and (symbol-listp marked-formals)
                                       (equal (len marked-formals)
                                              (len formals))))
                  (new-vars-to-mark-new
                   symbol-listp
                   :hyp (and (symbol-listp formals)
                             (symbol-listp vars-to-mark-new))))
     (b* (((when (endp formals)) (mv nil vars-to-mark-new))
          (formal (car formals))
          (new? (or (not (member-eq formal vars-in-scope))
                    (member-eq formal vars-used-after)
                    (dumb-occur-var-open-lst formal (cdr actuals))))
          (marked-formal (if new?
                             (atj-mark-var-new formal)
                           (atj-mark-var-old formal)))
          (vars-to-mark-new (if new?
                                (cons formal vars-to-mark-new)
                              (remove-eq formal vars-to-mark-new)))
          ((mv marked-formals
               vars-to-mark-new) (atj-mark-lambda-formals (cdr formals)
                                                          (cdr actuals)
                                                          vars-in-scope
                                                          vars-used-after
                                                          vars-to-mark-new)))
       (mv (cons marked-formal marked-formals)
           vars-to-mark-new))
     ///

     (more-returns
      (marked-formals true-listp :rule-classes :type-prescription)
      (new-vars-to-mark-new true-listp
                            :hyp (true-listp vars-to-mark-new)
                            :rule-classes :type-prescription))

     (defret len-of-atj-mark-lambda-formals.marked-formals
       (equal (len marked-formals)
              (len formals)))))

  :verify-guards nil ; done below

  ///

  (defrulel true-listp-when-symbol-listp
    (implies (symbol-listp x)
             (true-listp x)))

  (verify-guards atj-mark-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-formals+body ((formals symbol-listp) (body pseudo-termp))
  :returns (mv (new-formals symbol-listp)
               (new-body pseudo-termp :hyp :guard))
  :short "Mark all the variables
          in the formal parameters and body of an ACL2 function definition
          as `new' or `old'"
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top level of the marking algorithm;
     this top level is discussed in @(tsee atj-mark-term)."))
  (b* ((marked-formals (atj-mark-vars-new formals))
       ((mv marked-body &) (atj-mark-term body formals nil formals)))
    (mv marked-formals marked-body))
  ///

  (defret len-of-atj-mark-formals+body.new-formals
    (equal (len new-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-var-renaming
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          renaming of the ACL2 variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "We systematically rename all the ACL2 variables
     so that their new names are valid Java variable names
     and so that different ACL2 variables with the same name are renamed apart,
     unless the variables have been marked for reuse
     by the previous pre-translation step.
     This simplifies the ACL2-to-Java translation,
     which can just turn each ACL2 variable
     into a Java variable with the same name."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-init-indices*
  :short "Initial variable index alist."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we rename ACL2 variables to Java variables,
     we must avoid the names in @(tsee *atj-disallowed-jvar-names*).
     We do that by initializing the alist from variables to indices
     to associate index 1 to all the disallowed names.
     That is, we pretend that
     variables with the disallowed names have already been used,
     so that an index 1 (or greater) will be appended to any variable
     that would otherwise happen to be a disallowed name.
     Appending an index to a disallowed name always yields an allowed name.")
   (xdoc::p
    "Note that @(tsee *atj-disallowed-jvar-names*) is a list of strings,
     but the keys of the index map must be symbols.
     We use @(tsee str::intern-list) to convert them.
     It is critical to use the same package (currently @('\"JAVA\"'))
     used by @(tsee atj-var-to-jvar)."))
  (pairlis$ (str::intern-list *atj-disallowed-jvar-names* (pkg-witness "JAVA"))
            (repeat (len *atj-disallowed-jvar-names*) 1))
  ///
  (assert-event (symbol-pos-alistp *atj-init-indices*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formal ((var symbolp)
                           (indices symbol-pos-alistp)
                           (curr-pkg stringp)
                           (vars-by-name string-symbollist-alistp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-var symbolp)
               (new-indices symbol-pos-alistp
                            :hyp (and (symbol-pos-alistp indices)
                                      (symbolp var))))
  :short "Rename a formal parameters of
          a defined function or lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-rename-formals),
     the renaming of a variable is established
     when the variable is encountered as a formal parameter.
     This motivates the name of this function.")
   (xdoc::p
    "This function is called only on formal parameters marked as `new'.
     Formal parameters marked as `old' are just renamed
     according to the existing renaming map @('renaming-old').")
   (xdoc::p
    "Each ACL2 function is turned into a Java method,
     whose body is a shallowly embedded representation
     of the ACL2 function body.
     The ACL2 function body may reference the ACL2 function's parameter,
     as well as @(tsee let)-bound variables (via lambda expressions).
     Thus, the same variable symbol may in fact denote different variables
     in different parts of an ACL2 function body.
     Java does not allow different local variables with the same name
     in (nested scopes in) the same method,
     and so we need to map homonymous but different ACL2 variables
     in the same ACL2 function
     to differently named Java variables
     in the same Java method.
     We use numeric indices, one for each variable name,
     which is appended (as explained below) to the Java variable name
     to make it unique within the Java mehtod.")
   (xdoc::p
    "Another need for disambiguation arises because of package prefixes.
     An ACL2 variable is a symbol,
     which consists of a name and also a package name:
     two distinct variables may have the same name
     but different package names.
     However, when we append the package name and the name of the symbol,
     we have unique Java variable names.")
   (xdoc::p
    "We use @(tsee atj-var-to-jvar) to turn @('var')
     into a new symbol whose name is a valid Java variable name.
     Then we ensure its uniqueness by retrieving and using the next index,
     from the parameter @('indices'); more on this below.
     In general, as mentioned in @(tsee atj-var-to-jvar),
     we append the index after the result of @(tsee atj-var-to-jvar);
     but if the index is 0, we do not append it, to improve readability;
     in particular, if there is just one variable with a certain name,
     since we start with index 0, no index is ever added to the name.
     When this function is called,
     the indices alist always associates non-0 indices to
     the symbols whose names are in @(tsee *atj-disallowed-jvar-names*):
     see @(tsee *atj-init-indices*).")
   (xdoc::p
    "The name obtained by optionally appending the index
     may not be a valid Java identifier:
     this happens if it is a Java keyword or literal, or if it is empty.
     (This may actually happen only if no index is appended.)
     If this is the case, we add a single @('$') at the end,
     which makes the name valid and unambiguous.")
   (xdoc::p
    "The index to use for this variable
     is retrieved from the @('indices') parameter,
     which is an alist that associates each variable to its next index to use.
     If a variable is not in the alist, it is as if it had index 0,
     and in that case no index is added, as explained above.
     The alist is updated
     by incrementing the next index to use for the variable,
     and returned along with the new variable.")
   (xdoc::p
    "The keys of the alist are not the original ACL2 variables,
     but the renamed variables resulting from @(tsee atj-var-to-jvar).
     This gives us more flexibility,
     by obviating the requirement that @(tsee atj-var-to-jvar) be injective:
     if this function is not injective,
     then different ACL2 variables may become the same Java variable,
     and the next index must be the same for all of these variables,
     so that they can be properly disambiguated.")
   (xdoc::p
    "This pre-translation step is performed
     after the type annotation and new/old marking steps,
     but the caller of this function decomposes the marked annotated variable
     into its unmarked unannotated name, type, and marking,
     and only passes the unannotated name @('var') to this function.
     The @('vars-by-name') parameter of this function
     consists of variable names without annotations and markings."))
  (b* ((jvar (atj-var-to-jvar var curr-pkg vars-by-name))
       (jvar+index? (assoc-eq jvar indices))
       (index (if jvar+index? (cdr jvar+index?) 0))
       (indices (acons jvar (1+ index) indices))
       (jvar (atj-var-add-index jvar index)))
    (mv jvar indices))

  :prepwork
  ((defrulel returns-lemma
     (implies (posp x)
              (posp (1+ x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formals ((formals symbol-listp)
                            (renaming-new symbol-symbol-alistp)
                            (renaming-old symbol-symbol-alistp)
                            (indices symbol-pos-alistp)
                            (curr-pkg stringp)
                            (vars-by-name string-symbollist-alistp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-formals symbol-listp
                            :hyp (and (symbol-listp formals)
                                      (symbol-symbol-alistp renaming-new)))
               (new-renaming-new symbol-symbol-alistp
                                 :hyp (and (symbol-listp formals)
                                           (symbol-symbol-alistp renaming-new)))
               (new-renaming-old symbol-symbol-alistp
                                 :hyp (and (symbol-listp formals)
                                           (symbol-symbol-alistp renaming-old)))
               (new-indices symbol-pos-alistp
                            :hyp (and (symbol-listp formals)
                                      (symbol-pos-alistp indices))))
  :short "Rename the formal parameters of
          a defined function or lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-rename-formal),
     the shallowly embedded ACL2 variables are made unique via indices.
     There is an independent index for each ACL2 variable,
     so we use an alist from symbols to natural numbers
     to keep track of these indices.
     This alist is threaded through the functions
     that rename all the variables in ACL2 terms.
     This pre-translation step happens
     after the type annotation and new/old marking step,
     but the variables in this alist are without annotations and markings,
     because annotations and markings are discarded
     when generating Java variables,
     and thus two ACL2 variables that only differ in annotations or markings
     must be renamed apart and must share the same index in the alist.")
   (xdoc::p
    "In ACL2, a variable is ``introduced''
     as a formal parameter of a function or lambda expression,
     and then referenced in the body of the function or lambda expression.
     The choice and use of the index must be done at this introduction time,
     and not at every reference to the variable after its introduction.
     Thus, when we encounter the formals of a function or lambda expression,
     we generate the Java variable names for these ACL2 variables,
     using the current indices, and update and return the indices.
     This is the case only if the formal parameter is marked as `new';
     if instead it is marked as `old',
     we look it up in a renaming map,
     which is an alist from the old variable names to the new variable names,
     i.e. it expresses the current renaming of variables.
     There are actually two renaming alists:
     one for the variables marked as `new',
     and one for the variables marked as `old':
     see @(tsee atj-rename-term) for more information.
     This function takes both renaming maps,
     and augments both of them with the renamings for the formal parameters
     that are marked as `new'.
     The variables in the renaming maps are all type-annotated,
     for faster lookup when renaming variables in terms.
     The variables in the renaming maps are not marked as `new' or `old';
     as mentioned above, we have two separate maps for new and old variables.")
   (xdoc::p
    "Each ACL2 formal parameter in the input list
     is processed differently based on whether it is marked `new' or `old'.
     If it is marked `old',
     it is simply renamed according to the @('renaming-old') alist,
     which must include an entry for the variable.
     When it is marked as `new',
     it is unmarked and unannotated and passed to @(tsee atj-rename-formal),
     which uses and updates the index associated to the variable.")
   (xdoc::p
    "The formals @('formals') being renamed are annotated,
     because this pre-translation step happens after the type annotation step.
     Thus, the type annotations are removed prior to the renaming
     and added back after the renaming."))
  (b* (((when (endp formals)) (mv nil renaming-new renaming-old indices))
       (formal (car formals))
       ((mv uformal new?) (atj-unmark-var formal))
       ((when (not new?)) ; i.e. old
        (b* ((renaming-pair (assoc-eq uformal renaming-old))
             ((unless (consp renaming-pair))
              (raise "Internal error: ~x0 has no renaming." formal)
              (mv (true-list-fix formals)
                  renaming-new
                  renaming-old
                  indices))
             (new-uformal (cdr renaming-pair))
             (new-formal (atj-mark-var-old new-uformal))
             ((mv new-formals
                  renaming-new
                  renaming-old
                  indices) (atj-rename-formals (cdr formals)
                                               renaming-new
                                               renaming-old
                                               indices
                                               curr-pkg
                                               vars-by-name)))
          (mv (cons new-formal new-formals) renaming-new renaming-old indices)))
       ((mv uuformal types) (atj-type-unannotate-var uformal))
       ((mv new-uuformal indices)
        (atj-rename-formal uuformal indices curr-pkg vars-by-name))
       (new-uformal (atj-type-annotate-var new-uuformal types))
       (renaming-new (acons uformal new-uformal renaming-new))
       (renaming-old (acons uformal new-uformal renaming-old))
       (new-formal (atj-mark-var-new new-uformal))
       ((mv new-formals
            renaming-new
            renaming-old
            indices) (atj-rename-formals (cdr formals)
                                         renaming-new
                                         renaming-old
                                         indices
                                         curr-pkg
                                         vars-by-name)))
    (mv (cons new-formal new-formals) renaming-new renaming-old indices))

  ///

  (more-returns
   (new-formals true-listp :rule-classes :type-prescription))

  (defret len-of-atj-rename-formals.new-formals
    (equal (len new-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-rename-term
  :short "Rename all the ACL2 variables in an ACL2 term to their Java names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The alist from variables to indices
     is threaded through this function and its mutually recursive companion,
     in the same way as the renaming alist for the `old' variables;
     thus different variables in different Java scopes may have the same index.
     This alist contains variables without annotations or markings;
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "The renaming alist for variables marked as `new'
     is not threaded through:
     it is just passed down, according to ACL2's scoping.
     This alist contains variables with type annotations
     but without markings for `old' or `new';
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "The renaming alist for variables marked as `old'
     is threaded through instead,
     in the same way as the set of variables in scope in @(tsee atj-mark-term)
     (see that function for details).
     This is because variables are marked for reuse
     based (also) on that threading of the variables in scope:
     when we encounter a variable to rename that is marked for reuse,
     we must have its name available in the renaming alist.
     This alist contains variables with type annotations
     but without markings for `old' or `new';
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "If the term is a variable,
     it is unmarked,
     looked up in the appropriate renaming alist based on the marking,
     and replaced with the renamed variable, which is re-marked.
     Recall that variable names are generated
     via @(tsee atj-rename-formals) when variables are introduced,
     i.e. from formal parameters of defined functions and lambda expressions.")
   (xdoc::p
    "If the term is a quoted constant, it is obviously left unchanged.")
   (xdoc::p
    "If the term is a function call,
     its actual arguments are recursively processed,
     renaming all their variables.
     If the function is a named one, it is of course left unchanged.
     If instead it is a lambda expression,
     we process the renaming of its formal parameters,
     which in general augments the two renaming alists,
     and then recursively process the body of the lambda expression."))

  (define atj-rename-term ((term pseudo-termp)
                           (renaming-new symbol-symbol-alistp)
                           (renaming-old symbol-symbol-alistp)
                           (indices symbol-pos-alistp)
                           (curr-pkg stringp)
                           (vars-by-name string-symbollist-alistp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (new-term pseudo-termp)
                 (new-renaming-old symbol-symbol-alistp)
                 (new-indices symbol-pos-alistp))
    (b* (((unless (mbt (pseudo-termp term))) (mv nil nil nil))
         ((unless (mbt (symbol-symbol-alistp renaming-new))) (mv nil nil nil))
         ((unless (mbt (symbol-symbol-alistp renaming-old))) (mv nil nil nil))
         ((unless (mbt (symbol-pos-alistp indices))) (mv nil nil nil))
         ((unless (mbt (stringp curr-pkg))) (mv nil nil nil))
         ((unless (mbt (string-symbollist-alistp vars-by-name)))
          (mv nil nil nil))
         ((when (variablep term))
          (b* (((mv var new?) (atj-unmark-var term))
               (renaming-pair (assoc-eq var (if new?
                                                renaming-new
                                              renaming-old)))
               ((unless (consp renaming-pair))
                (raise "Internal error: no renaming found for variable ~x0."
                       term)
                (mv nil nil nil))
               (new-var (cdr renaming-pair))
               (new-term (if new?
                             (atj-mark-var-new new-var)
                           (atj-mark-var-old new-var))))
            (mv new-term renaming-old indices)))
         ((when (fquotep term)) (mv term renaming-old indices))
         (fn (ffn-symb term))
         ((when (eq fn 'if))
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3)))
            (if (equal test then)
                (b* (((mv new-test
                          renaming-old
                          indices) (atj-rename-term test
                                                    renaming-new
                                                    renaming-old
                                                    indices
                                                    curr-pkg
                                                    vars-by-name))
                     ((mv new-else
                          &
                          &) (atj-rename-term else
                                              renaming-new
                                              renaming-old
                                              indices
                                              curr-pkg
                                              vars-by-name)))
                  (mv `(if ,new-test ,new-test ,new-else)
                      renaming-old
                      indices))
              (b* (((mv new-test
                        renaming-old
                        indices) (atj-rename-term test
                                                  renaming-new
                                                  renaming-old
                                                  indices
                                                  curr-pkg
                                                  vars-by-name))
                   ((mv new-then
                        &
                        &) (atj-rename-term then
                                            renaming-new
                                            renaming-old
                                            indices
                                            curr-pkg
                                            vars-by-name))
                   ((mv new-else
                        &
                        &) (atj-rename-term else
                                            renaming-new
                                            renaming-old
                                            indices
                                            curr-pkg
                                            vars-by-name)))
                (mv `(if ,new-test ,new-then ,new-else)
                    renaming-old
                    indices)))))
         (args (fargs term))
         ((mv new-args
              renaming-old
              indices) (atj-rename-terms args
                                         renaming-new
                                         renaming-old
                                         indices
                                         curr-pkg
                                         vars-by-name))
         ((when (symbolp fn)) (mv (fcons-term fn new-args)
                                  renaming-old
                                  indices))
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         ((mv new-formals
              renaming-new
              renaming-old
              indices) (atj-rename-formals formals
                                           renaming-new
                                           renaming-old
                                           indices
                                           curr-pkg
                                           vars-by-name))
         ((mv new-body
              renaming-old
              indices) (atj-rename-term body
                                        renaming-new
                                        renaming-old
                                        indices
                                        curr-pkg
                                        vars-by-name)))
      (mv (fcons-term (make-lambda new-formals new-body)
                      new-args)
          renaming-old
          indices)))

  (define atj-rename-terms ((terms pseudo-term-listp)
                            (renaming-new symbol-symbol-alistp)
                            (renaming-old symbol-symbol-alistp)
                            (indices symbol-pos-alistp)
                            (curr-pkg stringp)
                            (vars-by-name string-symbollist-alistp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (new-terms (and (pseudo-term-listp new-terms)
                                 (equal (len new-terms) (len terms))))
                 (new-renaming-old symbol-symbol-alistp)
                 (new-indices symbol-pos-alistp))
    (b* (((unless (mbt (pseudo-term-listp terms)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (symbol-symbol-alistp renaming-new)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (symbol-symbol-alistp renaming-old)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (symbol-pos-alistp indices)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (stringp curr-pkg)))
          (mv (repeat (len terms) nil) nil nil))
         ((unless (mbt (string-symbollist-alistp vars-by-name)))
          (mv (repeat (len terms) nil) nil nil)))
      (cond ((endp terms) (mv nil renaming-old indices))
            (t (b* (((mv new-term
                         renaming-old
                         indices) (atj-rename-term (car terms)
                         renaming-new
                         renaming-old
                         indices
                         curr-pkg
                         vars-by-name))
                    ((mv new-terms
                         renaming-old
                         indices) (atj-rename-terms (cdr terms)
                         renaming-new
                         renaming-old
                         indices
                         curr-pkg
                         vars-by-name)))
                 (mv (cons new-term new-terms)
                     renaming-old
                     indices))))))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-rename-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formals+body ((formals symbol-listp)
                                 (body pseudo-termp)
                                 (curr-pkg stringp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-formals symbol-listp :hyp :guard)
               (new-body pseudo-termp :hyp :guard))
  :short "Rename all the ACL2 variables to their Java names,
          in the formal parameters and body of an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect all the variables in the formals and body,
     remove their markings and annotations
     (recall that the type annotation and new/old marking pre-translation steps
     take place before this renaming step),
     and organize them by symbol name:
     the resulting alist is passed to the renaming functions.")
   (xdoc::p
    "Starting with the empty alist of indices and the empty renaming alists,
     we introduce renamed variables for the formal parameters,
     and we use the resulting renaming alists to process the body."))
  (b* ((vars (union-eq formals (all-free/bound-vars body)))
       ((mv vars &) (atj-unmark-vars vars))
       (vars (atj-type-unannotate-vars vars))
       (vars-by-name (organize-symbols-by-name vars))
       ((mv new-formals renaming-new renaming-old indices)
        (atj-rename-formals
         formals nil nil *atj-init-indices* curr-pkg vars-by-name))
       ((mv new-body & &)
        (atj-rename-term
         body renaming-new renaming-old indices curr-pkg vars-by-name)))
    (mv new-formals new-body))
  ///

  (defret len-of-atj-rename-formals+body.new-formals
    (equal (len new-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-pre-translate ((fn symbolp)
                           (formals symbol-listp)
                           (body pseudo-termp)
                           (in-types atj-type-listp)
                           (out-types atj-type-listp)
                           (out-arrays symbol-listp)
                           (mv-typess atj-type-list-listp)
                           (deep$ booleanp)
                           (guards$ booleanp)
                           (wrld plist-worldp))
  :guard (and (= (len formals) (len in-types))
              (consp out-types)
              (cons-listp mv-typess))
  :returns (mv (new-formals symbol-listp :hyp :guard)
               (new-body pseudo-termp :hyp :guard)
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))))
  :parents (atj-pre-translation)
  :short "Pre-translate the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done before the translation from ACL2 to Java proper.
     The pre-translation steps are described "
    (xdoc::seetopic "atj-pre-translation" "here")
    ".")
   (xdoc::p
    "We collect all the @(tsee mv) types in the body
     for which we will need to generate @(tsee mv) classes.
     This is only relevant to the shallow embedding."))
  (b* ((body (atj-remove-return-last body guards$))
       (body (remove-dead-if-branches body))
       (body (remove-unused-vars body))
       ((when deep$) (mv formals body nil))
       (body (remove-trivial-vars body))
       (body (atj-restore-mv-calls-in-body body out-types wrld))
       ((mv formals body mv-typess)
        (atj-type-annotate-formals+body
         formals body in-types out-types mv-typess guards$ wrld))
       ((run-when guards$) (atj-analyze-arrays-in-formals+body formals
                                                               body
                                                               out-arrays
                                                               wrld))
       ((mv formals body) (atj-mark-formals+body formals body))
       ((mv formals body) (atj-rename-formals+body
                           formals body (symbol-package-name fn))))
    (mv formals body mv-typess))
  ///

  (defret len-of-atj-pre-translate.new-formals
    (equal (len new-formals)
           (len formals))))
