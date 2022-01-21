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

(defxdoc+ atj-pre-translation-conjunctions
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          replacement of @('(if a b nil)') calls with @(tsee and) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in the shallow embedding.")
   (xdoc::p
    "ACL2 turns untranslated calls of the form @('(and a b)')
     into translated calls of the form @('(if a b nil)').
     This pre-translation step performs the inverse transformation,
     so that the ACL2-to-Java translation step can
     more readily recognize this kind of calls
     and treat them specially.")
   (xdoc::p
    "Note that this pre-translation step
     turns @('(if a b nil)') into @('(and a b)')
     even when the original untranslated term was @('(if a b nil)').
     But this is harmelss, as the two untranslated terms are equivalent."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-restore-and-calls-in-term
  :short "Restore @(tsee and) calls in a translated term."
  :long
  (xdoc::topstring
   (xdoc::p
    "Recall that, at this point, terms have already been type-annotated.
     Thus, we must take the type annotations into account here,
     as we recognize and transform the terms."))

  (define atj-restore-and-calls-in-term ((term pseudo-termp))
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
                          (b* (((mv else & &)
                                (atj-type-unwrap-term
                                 (nth 2 (pseudo-term-fncall->args uterm)))))
                            (pseudo-term-equiv else
                                               (pseudo-term-quote nil))))
                     (atj-type-wrap-term
                      (pseudo-term-fncall
                       'and
                       (list (atj-restore-and-calls-in-term
                              (nth 0 (pseudo-term-fncall->args uterm)))
                             (atj-restore-and-calls-in-term
                              (nth 1 (pseudo-term-fncall->args uterm)))))
                      src-types
                      dst-types)
                   (atj-type-wrap-term
                    (pseudo-term-fncall fn
                                        (atj-restore-and-calls-in-terms
                                         (pseudo-term-fncall->args uterm)))
                    src-types
                    dst-types)))
       :lambda (atj-type-wrap-term
                (pseudo-term-lambda (pseudo-term-lambda->formals uterm)
                                    (atj-restore-and-calls-in-term
                                     (pseudo-term-lambda->body uterm))
                                    (atj-restore-and-calls-in-terms
                                     (pseudo-term-lambda->args uterm)))
                src-types
                dst-types)))
    :measure (pseudo-term-count term))

  (define atj-restore-and-calls-in-terms ((terms pseudo-term-listp))
    :returns (new-terms pseudo-term-listp)
    (cond ((endp terms) nil)
          (t (cons (atj-restore-and-calls-in-term (car terms))
                   (atj-restore-and-calls-in-terms (cdr terms)))))
    :measure (pseudo-term-list-count terms)
    ///
    (defret len-of-atj-restore-and-calls-in-terms
      (equal (len new-terms)
             (len terms))))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-restore-and-calls-in-term))
