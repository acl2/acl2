; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "type-annotation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-disjunctions
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          replacement of @('(if a a b)') calls with @(tsee or) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in the shallow embedding.")
   (xdoc::p
    "ACL2 turns untranslated calls of the form @('(or a b)')
     into translated calls of the form @('(if a a b)').
     This pre-translation step performs the inverse transformation,
     so that the ACL2-to-Java translation step can
     more readily recognize this kind of calls
     and treat them specially.")
   (xdoc::p
    "Note that this pre-translation step
     turns @('(if a a b)') into @('(or a b)')
     even when the original untranslated term was @('(if a a b)').
     But this is harmelss, as the two untranslated terms are equivalent,
     at least functionally (assuming that @('a') has no side effects)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-restore-or-calls-in-term
  :short "Restore @(tsee or) calls in a translated term."
  :long
  (xdoc::topstring
   (xdoc::p
    "Recall that, at this point, terms have already been type-annotated.
     Thus, we must take the type annotations into account here,
     as we recognize and transform the terms.")
   (xdoc::p
    "In general, the test of an @(tsee if)
     may be type-annotated differently from its branches,
     even when the unannotated test is the same as a branch.
     The reason is that the type annotation step ensures that
     the branches have the same type
     (by inserting suitable type conversions).
     Thus, even though an untranslated @('(or a b)')
     is translated to an unannotated @('(if a a b)'),
     then its annotated version may be @('(C1 (if (C2 a) (C3 a) (C4 b)))')
     where @('C2') and @('C3') are different conversions.
     Thus, we need to unwrap the annotated test and `then' branch
     before comparing them for equality.")
   (xdoc::p
    "When the unwrapped test is equal to the unwrapped `then' branch,
     we generate the annotated @('(C1 (or (C3 a) (C4 b)))').
     It is important that we take the annotated `then' branch,
     not the annotated test,
     because it is the type of the annotated `then' branch that matters
     with regard to the result of the disjunction."))

  (define atj-restore-or-calls-in-term ((term pseudo-termp))
    :returns (new-term pseudo-termp)
    (b* (((mv uterm src-types dst-types) (atj-type-unwrap-term term)))
      (pseudo-term-case
       uterm
       :null (raise "Internal error: null term.")
       :var (pseudo-term-fix term)
       :quote (pseudo-term-fix term)
       :fncall (b* ((fn (pseudo-term-fncall->fn uterm)))
                 (if (and (eq fn 'if)
                          (int= 3 ; this should be always true
                                (len (pseudo-term-fncall->args uterm)))
                          (b* (((mv test & &)
                                (atj-type-unwrap-term
                                 (nth 0 (pseudo-term-fncall->args uterm))))
                               ((mv then & &)
                                (atj-type-unwrap-term
                                 (nth 1 (pseudo-term-fncall->args uterm)))))
                            (equal test then)))
                     (atj-type-wrap-term
                      (pseudo-term-fncall
                       'or
                       (list (atj-restore-or-calls-in-term
                              (nth 1 (pseudo-term-fncall->args uterm)))
                             (atj-restore-or-calls-in-term
                              (nth 2 (pseudo-term-fncall->args uterm)))))
                      src-types
                      dst-types)
                   (atj-type-wrap-term
                    (pseudo-term-fncall fn
                                        (atj-restore-or-calls-in-terms
                                         (pseudo-term-fncall->args uterm)))
                    src-types
                    dst-types)))
       :lambda (atj-type-wrap-term
                (pseudo-term-lambda (pseudo-term-lambda->formals uterm)
                                    (atj-restore-or-calls-in-term
                                     (pseudo-term-lambda->body uterm))
                                    (atj-restore-or-calls-in-terms
                                     (pseudo-term-lambda->args uterm)))
                src-types
                dst-types)))
    :measure (pseudo-term-count term))

  (define atj-restore-or-calls-in-terms ((terms pseudo-term-listp))
    :returns (new-terms pseudo-term-listp)
    (cond ((endp terms) nil)
          (t (cons (atj-restore-or-calls-in-term (car terms))
                   (atj-restore-or-calls-in-terms (cdr terms)))))
    :measure (pseudo-term-list-count terms)
    ///
    (defret len-of-atj-restore-or-calls-in-terms
      (equal (len new-terms)
             (len terms))))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-restore-or-calls-in-term))
