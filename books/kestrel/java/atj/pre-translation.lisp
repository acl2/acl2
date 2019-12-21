; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "name-translation")
(include-book "types")

(include-book "kestrel/std/system/all-free-bound-vars" :dir :system)
(include-book "kestrel/std/system/all-vars-open" :dir :system)
(include-book "kestrel/std/system/dumb-occur-var-open" :dir :system)
(include-book "kestrel/std/system/remove-dead-if-branches" :dir :system)
(include-book "kestrel/std/system/remove-mbe" :dir :system)
(include-book "kestrel/std/system/remove-progn" :dir :system)
(include-book "kestrel/std/system/remove-trivial-vars" :dir :system)
(include-book "kestrel/std/system/remove-unused-vars" :dir :system)
(include-book "kestrel/std/system/unquote-term" :dir :system)
(include-book "std/alists/remove-assocs" :dir :system)
(include-book "std/strings/symbols" :dir :system)
(include-book "std/typed-alists/symbol-pos-alistp" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)

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
     (xdoc::seetopic "atj-pre-translation-remove-last" "here")
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
     "We annotate terms with ATJ type information.
      See "
     (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
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

(defxdoc+ atj-pre-translation-remove-last
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
     where @('src') identifies the ATJ type of the term
     and @('dst') identifies an ATJ type to which the term must be converted to;
     (ii) each ACL2 variable @('var') in a term is renamed to @('[type]var'),
     where @('type') identifies the ATJ type of the variable.")
   (xdoc::p
    "These annotations facilitate the ACL2-to-Java translation,
     which uses the type annotations as ``instructions'' for
     (i) which types to declare Java local variables with, and
     (ii) which Java conversion code to insert around expressions.")
   (xdoc::p
    "The annotated terms are still ACL2 terms (with a specific structure).
     This should let us prove, in ACL2,
     the equality of the annotated terms with the original terms,
     under suitable variable rebinding,
     and by introducing the @('[src>dst]') functions as identities.
     (This has not been done yet.)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-id ((type atj-typep))
  :returns (id stringp :hyp :guard)
  :short "Short string identifying an ATJ type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use a short two-letter string to identify each ATJ type.
     For the ATJ types that correspond to AIJ's public classes,
     the first letter is @('A') and the second letter is from the class name.
     For the Java primitive types,
     the first letter is @('J') and the second letter is from [JVMS:4.3.2].
     For the Java primitive array types,
     the first letter is @('Y') (which is the ending letter of `array')
     and the second letter is from [JVMS:4.3.2]."))
  (case type
    (:ainteger "AI")
    (:arational "AR")
    (:anumber "AN")
    (:acharacter "AC")
    (:astring "AS")
    (:asymbol "AY")
    (:acons "AP")
    (:avalue "AV")
    (:jboolean "JZ")
    (:jchar "JC")
    (:jbyte "JB")
    (:jshort "JS")
    (:jint "JI")
    (:jlong "JJ")
    (:jboolean[] "YZ")
    (:jchar[] "YC")
    (:jbyte[] "YB")
    (:jshort[] "YS")
    (:jint[] "YI")
    (:jlong[] "YJ")
    (otherwise (impossible)))
  ///

  (defrule atj-type-id-injective
    (implies (and (atj-typep x)
                  (atj-typep y))
             (equal (equal (atj-type-id x)
                           (atj-type-id y))
                    (equal x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-of-id ((id stringp))
  :returns (type atj-typep)
  :short "ATJ type identified by a short string."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-type-id).")
  (cond ((equal id "AI") :ainteger)
        ((equal id "AR") :arational)
        ((equal id "AN") :anumber)
        ((equal id "AC") :acharacter)
        ((equal id "AS") :astring)
        ((equal id "AY") :asymbol)
        ((equal id "AP") :acons)
        ((equal id "AV") :avalue)
        ((equal id "JZ") :jboolean)
        ((equal id "JC") :jchar)
        ((equal id "JB") :jbyte)
        ((equal id "JS") :jshort)
        ((equal id "JI") :jint)
        ((equal id "JJ") :jlong)
        ((equal id "YZ") :jboolean[])
        ((equal id "YC") :jchar[])
        ((equal id "YB") :jbyte[])
        ((equal id "YS") :jshort[])
        ((equal id "YI") :jint[])
        ((equal id "YJ") :jlong[])
        (t (prog2$
            (raise "Internal error: ~x0 does not identify a type." id)
            :avalue))) ; irrelevant
  ///

  (defrule atj-type-of-id-of-atj-type-id
    (implies (atj-typep x)
             (equal (atj-type-of-id (atj-type-id x))
                    x))
    :enable atj-type-id))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-conv ((src-type atj-typep) (dst-type atj-typep))
  :returns (name symbolp)
  :short "ATJ type conversion function names used to annotate ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
    ", each ACL2 term is wrapped with a function named @('[src>dst]'),
     where @('src') identifies the ATJ type of the term
     and @('dst') identifies an ATJ type
     to which the term must be converted to.")
   (xdoc::p
    "These function names are all in the @('\"JAVA\"') package.
     For now we do not need these functions to actually exist in the ACL2 world,
     because annotated terms are only created ephemerally as data
     manipulated by the ATJ code generation functions.
     However, in order to prove that the type annotation process
     preserves the ACL2 meaning of terms,
     these functions will need to exist and be defined as identify functions,
     which can be easily done with a macro."))
  (intern$ (str::cat "[" (atj-type-id src-type) ">" (atj-type-id dst-type) "]")
           "JAVA"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-of-conv ((conv symbolp))
  :returns (mv (src-type atj-typep)
               (dst-type atj-typep))
  :short "Source and destination ATJ types of a conversion function."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-type-conv).")
  (b* ((string (symbol-name conv))
       ((unless (and (int= (length string) 7)
                     (eql (char string 0) #\[)
                     (eql (char string 3) #\>)
                     (eql (char string 6) #\])))
        (raise "Internal error: ~x0 is not a conversion function." conv)
        (mv :avalue :avalue)) ; irrelevant
       (src-id (subseq string 1 3))
       (dst-id (subseq string 4 6))
       (src-type (atj-type-of-id src-id))
       (dst-type (atj-type-of-id dst-id)))
    (mv src-type dst-type))
  ///

  (defrule atj-types-of-conv-of-atj-type-conv
    (implies (and (atj-typep x)
                  (atj-typep y))
             (equal (atj-types-of-conv (atj-type-conv x y))
                    (list x y)))
    :enable (atj-type-conv atj-type-id)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-wrap-term ((term pseudo-termp)
                            (src-type atj-typep)
                            (dst-type? atj-maybe-typep))
  :returns (wrapped-term pseudo-termp :hyp (pseudo-termp term))
  :short "Wrap an ACL2 term with a type conversion function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conversion is from the source to the destination type.
     If the destination type is absent,
     it is treated as if it were equal to the source type,
     i.e. the conversion is a no-op."))
  (b* ((conv (if dst-type?
                 (atj-type-conv src-type dst-type?)
               (atj-type-conv src-type src-type))))
    (fcons-term* conv term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unwrap-term ((term pseudo-termp))
  :returns (mv (unwrapped-term pseudo-termp :hyp :guard)
               (src-type atj-typep)
               (dst-type atj-typep))
  :short "Unwrap an ACL2 term wrapped by @(tsee atj-type-wrap-term)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially the inverse function,
     except that it always returns a destination type, never @('nil')."))
  (b* (((when (or (variablep term)
                  (fquotep term)
                  (flambda-applicationp term)))
        (raise "Internal error: the term ~x0 has the wrong format." term)
        (mv nil :avalue :avalue)) ; irrelevant
       (fn (ffn-symb term))
       ((when (flambdap fn))
        (raise "Internal error: the term ~x0 has the wrong format." term)
        (mv nil :avalue :avalue)) ; irrelevant
       ((mv src-type dst-type) (atj-types-of-conv fn)))
    (mv (fargn term 1) src-type dst-type))
  ///

  (defrule acl2-count-of-atj-type-unwrap-term-linear
    (implies (mv-nth 0 (atj-type-unwrap-term term))
             (< (acl2-count (mv-nth 0 (atj-type-unwrap-term term)))
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-term ((term pseudo-termp)
                              (src-type atj-typep)
                              (dst-type? atj-maybe-typep))
  :returns (rewrapped-term pseudo-termp :hyp (pseudo-termp term)
                           :hints (("Goal" :expand ((pseudo-termp term)))))
  :short "Re-wrap an ACL2 term with a type conversion function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when annotating @(tsee if) terms,
     in the shallow embedding approach.
     These terms are initially wrapped with a type conversion function,
     but in general may need to be wrapped with a different one.
     So here we replace the wrapper.
     See @(tsee atj-type-annotate-term) for details."))
  (b* (((when (or (variablep term)
                  (fquotep term)
                  (not (consp (fargs term)))))
        (raise "Internal error: the term ~x0 has the wrong format." term)))
    (atj-type-wrap-term (fargn term 1) src-type dst-type?))
  :guard-hints (("Goal" :expand ((pseudo-termp term)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-terms ((terms pseudo-term-listp)
                               (src-types atj-type-listp)
                               (dst-types? atj-maybe-type-listp))
  :guard (and (= (len terms) (len src-types))
              (= (len terms) (len dst-types?)))
  :returns (rewrapped-terms pseudo-term-listp :hyp (pseudo-term-listp terms))
  :short "Lift @(tsee atj-type-rewrap-term) to lists."
  (cond ((endp terms) nil)
        (t (cons (atj-type-rewrap-term (car terms)
                                       (car src-types)
                                       (car dst-types?))
                 (atj-type-rewrap-terms (cdr terms)
                                        (cdr src-types)
                                        (cdr dst-types?))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-var ((var symbolp) (type atj-typep))
  :returns (annotated-var symbolp)
  :short "Annotate an ACL2 variable with a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
    ", we systematically add type information to each ACL2 variable.
     We do so by adding @('[type]') before the variable name,
     where @('type') identifies an ATJ type."))
  (packn-pos (list "[" (atj-type-id type) "]" var) var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unannotate-var ((var symbolp))
  :returns (mv (unannotated-var symbolp)
               (type atj-typep))
  :short "Decompose an annotated ACL2 variable into
          its unannotated counterpart and its type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee atj-type-annotate-var).")
   (xdoc::p
    "It is used when translating from ACL2 to Java,
     because the name of the Java variable is the one of the ACL2 variable
     without the type annotation."))
  (b* ((string (symbol-name var))
       ((unless (and (>= (length string) 4)
                     (eql (char string 0) #\[)
                     (eql (char string 3) #\])))
        (raise "Internal error: ~x0 has the wrong format." var)
        (mv nil :avalue)) ; irrelevant
       (unannotated-string (subseq string 4 (length string)))
       (unannotated-var (intern-in-package-of-symbol unannotated-string var))
       (type-id (subseq string 1 3))
       (type (atj-type-of-id type-id)))
    (mv unannotated-var type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-vars ((vars symbol-listp)
                                (types atj-type-listp))
  :guard (int= (len vars) (len types))
  :returns (new-vars symbol-listp)
  :short "Lift @(tsee atj-type-annotate-var) to lists."
  (cond ((endp vars) nil)
        (t (cons (atj-type-annotate-var (car vars) (car types))
                 (atj-type-annotate-vars (cdr vars) (cdr types)))))
  ///

  (defret len-of-atj-type-annotate-vars
    (equal (len new-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unannotate-vars ((vars symbol-listp))
  :returns (mv (unannotated-vars symbol-listp)
               (types atj-type-listp))
  :short "Lift @(tsee atj-type-unannotate-var) to lists."
  (b* (((when (endp vars)) (mv nil nil))
       ((mv var type) (atj-type-unannotate-var (car vars)))
       ((mv vars types) (atj-type-unannotate-vars (cdr vars))))
    (mv (cons var vars) (cons type types)))
  ///

  (defret len-of-atj-type-unannotate-vars.unannotated-vars
    (equal (len unannotated-vars)
           (len vars)))

  (defret len-of-atj-type-unannotate-vars.types
    (equal (len types)
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
    "The @('required-type?') input specifies
     the type required for the term, if any.
     At the top level (see @(tsee atj-type-annotate-formals+body)),
     this is the output type of the function:
     the body of the function must have the output type of the function.
     The recursive function @('atj-type-annotate-terms')
     that operates on lists of terms
     does not take a list of required types as input:
     if it did, it would be always consist of @('nil')s,
     so we simply avoid it.")
   (xdoc::p
    "The result of annotating a term is not only the annotated term,
     but also the type of the wrapped term.
     This is always the same as the required type when there is a required type;
     when there is no required type,
     the resulting type is the one inferred for the term.")
   (xdoc::p
    "The type inferred for a variable is the one assigned by @('var-types').
     We annotate the variable with its type;
     note that the variable names in @('var-types')
     do not have type annotations.
     We wrap the variable with a type conversion function
     from the inferred type to the required type if supplied,
     or to the inferred type (i.e. no-op conversion) if not supplied.")
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
     The type of the Java local variable is @('required-type?') if supplied:
     in this case, when @('required-type?') is recursively passed
     to the second and third argument of the @(tsee if),
     both terms will be wrapped so that they have the required type.
     However, if @('required-type?') is @('nil'),
     the recursive annotation of the `then' and `else' subterms
     may produce different types,
     and so in this case we re-wrap those terms
     with the least upper bound of the two types,
     according to the partial order on ATJ types.
     The case of a term of the form @('(if a a b)')
     is treated a little differently,
     but there is no substantial difference.
     In the general case @('(if a b c)') with @('a') different from @('b'),
     there is never any required type for the test @('a'),
     because in the Java code it is just used
     to generate the test of the @('if').
     In all cases, the @(tsee if) is wrapped with
     the identify conversion function for the overall type,
     for uniformity and to readily indicate the type
     of the Java local variable to generate.")
   (xdoc::p
    "For a lambda expression,
     the argument terms are annotated without required types.
     The inferred types are then assigned to the formal parameters
     when the body of the lambda expression is annotated.
     We annotate all the formal parameters of the lambda expression;
     but note that the new @('var-types') has non-annotated variable names.")
   (xdoc::p
    "For a named function call, the function's types are obtained.
     We first try annotating the argument terms without required types
     (as done for a lambda expression as explained above),
     thus inferring types for the arguments.
     Then we look for the function types (of the named function)
     whose input types are wider than or the same as
     the inferred argument types.
     If there are some, we select the one whose input types are the least
     (this always exists because of the closure property
     checked by @(tsee def-atj-other-function-type);
     see the documentation of that macro and supporting functions for details);
     we then use the output type of the selected function type
     as the type inferred for the function call
     (if the function has multiple output types,
     it means that it returns an @(tsee mv) result,
     which for now we regard just as a non-empty list,
     and thus we ``adjust'' the non-singleton type list
     to a single type @(':acons') in this case),
     and wrap it to adapt to the required type for the function call if any.
     The successful selection of such a function type means that,
     in the translated Java code, an overloaded method will be called
     based on the argument types inferred by the Java compiler.
     If there are no function types satisfying the above condition,
     we look at the primary function type (which always exists),
     and its input types become the required ones for the argument terms,
     while the output types are used to infer the type for the call,
     which is then wrapped as needed to match the required type if any;
     if the output types are not a singleton list,
     they are turned into a single @(':acons') type as explained above.")
   (xdoc::p
    "An annotated term is still a regular term,
     but it has a certain structure."))

  (define atj-type-annotate-term ((term pseudo-termp)
                                  (required-type? atj-maybe-typep)
                                  (var-types atj-symbol-type-alistp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :returns (mv (annotated-term pseudo-termp :hyp :guard)
                 (resulting-type atj-typep :hyp :guard))
    (b* (((when (variablep term))
          (b* ((var term)
               (var+type (assoc-eq var var-types))
               ((unless (consp var+type))
                (prog2$
                 (raise "Internal error: the variable ~x0 has no type." term)
                 (mv nil :avalue))) ; irrelevant
               (type (cdr var+type))
               (var (atj-type-annotate-var var type)))
            (mv (atj-type-wrap-term var type required-type?)
                (or required-type? type))))
         ((when (fquotep term))
          (b* ((value (unquote-term term))
               (type (atj-type-of-value value)))
            (mv (atj-type-wrap-term term type required-type?)
                (or required-type? type))))
         (fn (ffn-symb term))
         ((when (and (eq fn 'if)
                     (int= (len (fargs term)) 3))) ; should be always true
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3)))
            (if (equal test then) ; it's an OR
                (b* ((first test)
                     (second else)
                     ((mv first
                          first-type) (atj-type-annotate-term first
                                                              required-type?
                                                              var-types
                                                              guards$
                                                              wrld))
                     ((mv second
                          second-type) (atj-type-annotate-term second
                                                               required-type?
                                                               var-types
                                                               guards$
                                                               wrld))
                     (type (or required-type?
                               (atj-type-join first-type second-type)))
                     (first (if required-type?
                                first
                              (atj-type-rewrap-term first first-type type)))
                     (second (if required-type?
                                 second
                               (atj-type-rewrap-term second second-type type)))
                     (term (acl2::fcons-term* 'if first first second)))
                  (mv (atj-type-wrap-term term type type)
                      type))
              (b* (((mv test &) (atj-type-annotate-term test
                                                        nil
                                                        var-types
                                                        guards$
                                                        wrld))
                   ((mv then
                        then-type) (atj-type-annotate-term then
                                                           required-type?
                                                           var-types
                                                           guards$
                                                           wrld))
                   ((mv else
                        else-type) (atj-type-annotate-term else
                                                           required-type?
                                                           var-types
                                                           guards$
                                                           wrld))
                   (type (or required-type?
                             (atj-type-join then-type else-type)))
                   (then (if required-type?
                             then
                           (atj-type-rewrap-term then then-type type)))
                   (else (if required-type?
                             else
                           (atj-type-rewrap-term else else-type type)))
                   (term (fcons-term* 'if test then else)))
                (mv (atj-type-wrap-term term type type)
                    type)))))
         (args (fargs term))
         ((mv args types) (atj-type-annotate-terms args
                                                   var-types
                                                   guards$
                                                   wrld))
         ((when (symbolp fn))
          (b* ((fn-info (atj-get-function-type-info fn guards$ wrld))
               (main-fn-type (atj-function-type-info->main fn-info))
               (other-fn-types (atj-function-type-info->others fn-info))
               (all-fn-types (cons main-fn-type other-fn-types))
               (types?
                (atj-output-types-of-min-input-types types all-fn-types)))
            (if types?
                (b* ((type (if (= (len types?) 1)
                               (car types?)
                             :acons)))
                  (mv (atj-type-wrap-term (fcons-term fn args)
                                          type
                                          required-type?)
                      (or required-type? type)))
              (b* ((in-types (atj-function-type->inputs main-fn-type))
                   (out-types (atj-function-type->outputs main-fn-type))
                   ((unless (= (len in-types)
                               (len args))) ; should be always true
                    (raise "Internal error: ~
                            the function ~x0 has ~x1 arguments ~
                            but a different number of input types ~x2."
                           fn (len args) (len in-types))
                    (mv nil :avalue)) ; irrelevant
                   (args (atj-type-rewrap-terms args types in-types))
                   ((unless (consp out-types))
                    (raise "Internal error: ~
                            the function ~x0 has an empty list of output types."
                           fn)
                    (mv nil :avalue)) ; irrelevant
                   (out-type (if (= (len out-types) 1)
                                 (car out-types)
                               :acons)))
                (mv (atj-type-wrap-term (fcons-term fn args)
                                        out-type
                                        required-type?)
                    (or required-type? out-type))))))
         (formals (lambda-formals fn))
         (var-types (append (pairlis$ formals types) var-types))
         (formals (atj-type-annotate-vars formals types))
         ((mv body type) (atj-type-annotate-term (lambda-body fn)
                                                 required-type?
                                                 var-types
                                                 guards$
                                                 wrld))
         (term (fcons-term (make-lambda formals body) args)))
      (mv (atj-type-wrap-term term type required-type?)
          (or required-type? type))))

  (define atj-type-annotate-terms ((terms pseudo-term-listp)
                                   (var-types atj-symbol-type-alistp)
                                   (guards$ booleanp)
                                   (wrld plist-worldp))
    :returns (mv (annotated-terms (and (pseudo-term-listp annotated-terms)
                                       (equal (len annotated-terms)
                                              (len terms)))
                                  :hyp :guard)
                 (resulting-types (and (atj-type-listp resulting-types)
                                       (equal (len resulting-types)
                                              (len terms)))
                                  :hyp :guard))
    (b* (((when (endp terms)) (mv nil nil))
         ((mv term type) (atj-type-annotate-term (car terms)
                                                 nil ; REQUIRED-TYPE?
                                                 var-types
                                                 guards$
                                                 wrld))
         ((mv terms types) (atj-type-annotate-terms (cdr terms)
                                                    var-types
                                                    guards$
                                                    wrld)))
      (mv (cons term terms) (cons type types))))

  :prepwork ((local (in-theory (e/d (atj-maybe-typep)
                                    (atj-type-iff-when-atj-maybe-typep)))))

  :verify-guards nil ; done below
  ///

  (defret-mutual atj-type-annotate-term
    (defret true-listp-of-atj-type-annotate-term.annotated-terms-aux
      t
      :rule-classes nil
      :fn atj-type-annotate-term)
    (defret true-listp-of-atj-type-annotate-term.annotated-terms
      (true-listp annotated-terms)
      :rule-classes :type-prescription
      :fn atj-type-annotate-terms))

  (defret-mutual atj-type-annotate-term
    (defret true-listp-of-atj-type-annotate-term.resulting-types-aux
      t
      :rule-classes nil
      :fn atj-type-annotate-term)
    (defret true-listp-of-atj-type-annotate-term.resulting-types
      (true-listp resulting-types)
      :rule-classes :type-prescription
      :fn atj-type-annotate-terms))

  (verify-guards atj-type-annotate-term
    :hints (("Goal" :expand ((pseudo-termp term))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-formals+body ((formals symbol-listp)
                                        (body pseudo-termp)
                                        (in-types atj-type-listp)
                                        (out-type atj-typep)
                                        (guards$ booleanp)
                                        (wrld plist-worldp))
  :guard (int= (len formals) (len in-types))
  :returns (mv (annotated-formals symbol-listp :hyp :guard)
               (annotated-body pseudo-termp :hyp :guard))
  :short "Add ATJ type annotations to the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input and output types of the function are supplied as arguments.
     We annotate the body, using the output type as the required type.
     We initialize the variable-type alist
     to assign the input types to the formal parameters.
     We also annotate the formal parameters,
     but note that @('var-types') has non-annotated variable names."))
  (b* ((var-types (pairlis$ formals in-types))
       (formals (atj-type-annotate-vars formals in-types))
       ((mv body &)
        (atj-type-annotate-term body out-type var-types guards$ wrld)))
    (mv formals body))
  ///

  (defret len-of-atj-type-annotate-formals+body.new-formals
    (equal (len annotated-formals)
           (len formals))))

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
        (mv nil nil)) ; irrelevant
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
     to prevent a Java local variable may be erroneously reused.
     To understand this marking algorithm,
     one has to keep in mind how ACL2 terms are translated to Java:
     see @(tsee atj-gen-shallow-term) and companions.
     This is a delicate algorithm:
     a proof of correctness would be very beneficial.")
   (xdoc::p
    "Two conditions are necessary for reusing a variable:
     (i) the variable must be in scope (i.e. exists and be accessible); and
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
     (see @(tsee atj-gen-shallow-or-app)),
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
     but terms are not expected to be too large in the short term;
     this will be optimized when needed.
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
     For this purpose, we pass around a mapping
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
    "When the term to be marked is a function application,
     we first treat the @(tsee if) (and @(tsee or)) case separately.
     We mark the test, and after that the two branches.
     The handling of @('vars-in-scope') and @('vars-used-after') for this case
     has been explained above.")
   (xdoc::p
    "For all other function applications, which are strict,
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
     after the lambda application term, i.e. it is not in @('vars-used-after'):
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
     its (previous) value has already been assigned to @('x')."))

  (define atj-mark-term ((term pseudo-termp)
                         (vars-in-scope symbol-listp)
                         (vars-used-after symbol-listp)
                         (vars-to-mark-new symbol-listp))
    :returns (mv (marked-term pseudo-termp :hyp :guard)
                 (new-vars-in-scope symbol-listp :hyp :guard))
    (b* (((when (variablep term))
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
         (vars-used-after
          (if (symbolp fn)
              vars-used-after
            (union-eq vars-used-after
                      (set-difference-eq (all-vars-open (lambda-body fn))
                                         (lambda-formals fn)))))
         ((mv marked-args vars-in-scope) (atj-mark-terms args
                                                         vars-in-scope
                                                         vars-used-after
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
                                           (len terms)))
                               :hyp :guard)
                 (new-vars-in-scope symbol-listp :hyp :guard))
    (b* (((when (endp terms)) (mv nil vars-in-scope))
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
              ;; irrelevant:
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
       ((mv uuformal type) (atj-type-unannotate-var uformal))
       ((mv new-uuformal indices)
        (atj-rename-formal uuformal indices curr-pkg vars-by-name))
       (new-uformal (atj-type-annotate-var new-uuformal type))
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
    "If the term is a function application,
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
    :returns (mv (new-term pseudo-termp :hyp :guard)
                 (new-renaming-old symbol-symbol-alistp :hyp :guard)
                 (new-indices symbol-pos-alistp :hyp :guard))
    (b* (((when (variablep term))
          (b* (((mv var new?) (atj-unmark-var term))
               (renaming-pair (assoc-eq var (if new?
                                                renaming-new
                                              renaming-old)))
               ((unless (consp renaming-pair))
                (raise "Internal error: no renaming found for variable ~x0."
                       term)
                (mv nil nil nil)) ; irrelevant
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
                                 (equal (len new-terms) (len terms)))
                            :hyp :guard)
                 (new-renaming-old symbol-symbol-alistp :hyp :guard)
                 (new-indices symbol-pos-alistp :hyp :guard))
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
                   indices)))))

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
       ((mv vars &) (atj-type-unannotate-vars vars))
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
                           (out-type atj-typep)
                           (deep$ booleanp)
                           (guards$ booleanp)
                           (wrld plist-worldp))
  :guard (= (len formals) (len in-types))
  :returns (mv (new-formals symbol-listp :hyp :guard)
               (new-body pseudo-termp :hyp :guard))
  :parents (atj-pre-translation)
  :short "Pre-translate the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done before the translation from ACL2 to Java proper.
     The pre-translation steps are described "
    (xdoc::seetopic "atj-pre-translation" "here")
    "."))
  (b* ((body (atj-remove-return-last body guards$))
       (body (remove-dead-if-branches body))
       (body (remove-unused-vars body))
       ((when deep$) (mv formals body))
       (body (remove-trivial-vars body))
       ((mv formals body) (atj-type-annotate-formals+body
                           formals body in-types out-type guards$ wrld))
       ((mv formals body) (atj-mark-formals+body formals body))
       ((mv formals body) (atj-rename-formals+body
                           formals body (symbol-package-name fn))))
    (mv formals body))
  ///

  (defret len-of-atj-pre-translate.new-formals
    (equal (len new-formals)
           (len formals))))
