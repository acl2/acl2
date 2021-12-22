; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "remove-return-last")
(include-book "remove-dead-if-branches")
(include-book "unused-vars")
(include-book "trivial-vars")
(include-book "multiple-values")
(include-book "no-aij-types-analysis")
(include-book "type-annotation")
(include-book "array-analysis")
(include-book "var-reuse")
(include-book "var-renaming")
(include-book "conjunctions")
(include-book "disjunctions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation
  :parents (atj-code-generation)
  :short "Pre-translation performed by ATJ, as part of code generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(see atj-code-generation),
     prior to generating Java code,
     ATJ performs an ACL2-to-ACL2 pre-translation.
     Currently, this pre-translation consists of the following steps.
     The first three steps apply to both the deep and the shallow embedding;
     the others apply only to the shallow embedding.")
   (xdoc::ol
    (xdoc::li
     "We remove @(tsee return-last).
      See @(see atj-pre-translation-remove-return-last).")
    (xdoc::li
     "We remove dead @(tsee if) branches.
      See @(see atj-pre-translation-remove-dead-if-branches).")
    (xdoc::li
     "We remove the unused lambda-bound variables.
      See @(see atj-pre-translation-unused-vars).")
    (xdoc::li
     "We remove the trivial lambda-bound variables.
      See @(see atj-pre-translation-trivial-vars).")
    (xdoc::li
     "We replace @(tsee list) calls with @(tsee mv) calls
      in functions that return multiple results.
      See @(see atj-pre-translation-multiple-values).")
    (xdoc::li
     "We check (on the ACL2 code translated to Java)
      that the generated Java code does not use AIJ types.
      See @(see atj-pre-translation-no-aij-types-analysis).")
    (xdoc::li
     "We annotate terms with ATJ type information.
      See @(see atj-pre-translation-type-annotation).")
    (xdoc::li
     "We perform a single-threadedness analysis of the Java primitive arrays,
      but only if @(':guards') is @('t').
      See @(see atj-pre-translation-array-analysis).")
    (xdoc::li
     "We mark the lambda-bound variables
      that can be reused and destructively updated in Java.
      See @(see atj-pre-translation-var-reuse).")
    (xdoc::li
     "We rename variables
      so that their names are valid Java variable names
      and so that different variables with the same name are renamed apart,
      unless they have been marked for reuse in the previous step.
      See @(see atj-pre-translation-var-renaming).")
    (xdoc::li
     "We replace calls of the form @('(if a b nil)')
      with calls of the form @('(and a b)').
      See @(see atj-pre-translation-conjunctions).")
    (xdoc::li
     "We replace calls of the form @('(if a a b)')
      with calls of the form @('(or a b)').
      See @(see atj-pre-translation-disjunctions).")))
  :order-subtopics t
  :default-parent t)

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
                           (no-aij-types$ booleanp)
                           (wrld plist-worldp))
  :guard (and (= (len formals) (len in-types))
              (consp out-types)
              (cons-listp mv-typess))
  :returns (mv (new-formals symbol-listp :hyp :guard)
               (new-body pseudo-termp :hyp :guard)
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))))
  :short "Pre-translate the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done before the translation from ACL2 to Java proper.
     The pre-translation steps are described in @(see atj-pre-translation).")
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
       ((run-when no-aij-types$) (atj-check-no-aij-types+body in-types
                                                              out-types
                                                              body
                                                              fn))
       ((mv formals body mv-typess)
        (atj-type-annotate-formals+body
         formals body in-types out-types mv-typess guards$ wrld))
       ((run-when guards$) (atj-analyze-arrays-in-formals+body formals
                                                               body
                                                               out-arrays
                                                               wrld))
       ((mv formals body) (atj-mark-formals+body formals body))
       ((mv formals body) (atj-rename-formals+body
                           formals body (symbol-package-name fn)))
       (body (atj-restore-and-calls-in-term body))
       (body (atj-restore-or-calls-in-term body)))
    (mv formals body mv-typess))
  ///

  (defret len-of-atj-pre-translate.new-formals
    (equal (len new-formals)
           (len formals))))
