; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../types")
(include-book "../java-primitives")
(include-book "../java-primitive-arrays")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-no-aij-types-analysis
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          analysis for the @(':no-aij-types') option."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the @(':no-aij-types') input is @('t'),
     the ACL2 code translated to Java must satisfy a number of requirements,
     described in the user documentation.
     These requirements must be checked after
     the pre-translation steps that may remove code,
     because the requirements only need to hold for
     ACL2 code that is actually translated to Java.
     Performing these checks earlier would reject ACL2 code
     that would be translated to Java code
     that does not use any AIJ types.")
   (xdoc::p
    "We perform these checks after
     @(see atj-pre-translation-multiple-values),
     so that we can more easily identify translated calls of @(tsee mv).")
   (xdoc::p
    "We perform these checks before
     @(see atj-pre-translation-type-annotation),
     so that we can perform the checks
     without worrying about the type conversion functions and type annotations,
     which would make the checks more complicated to perform."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-no-aij-type ((type atj-typep) (fn symbolp))
  :returns (yes/no booleanp)
  :short "Check that an ATJ type is not mapped to an AIJ type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The allowed ATJ types for this are
     @(':aboolean'), @(':acharacter'), and the @(':j...') types;
     see the user documentation.")
   (xdoc::p
    "This is used on the input and output types of
     the function passed as argument,
     which justifies the form of the error message.")
   (xdoc::p
    "If the check fails, we stop with an error."))
  (b* ((pass (atj-type-case type
                            :acl2 (or (atj-atype-case type.get :boolean)
                                      (atj-atype-case type.get :character))
                            :jprim t
                            :jprimarr t)))
    (or pass
        (raise "The function ~x0 has ~x1 among its input and output types, ~
                which violates the checks required by :NO-AIJ-TYPES T. ~
                You may need to use JAVA::ATJ-MAIN-FUNCTION-TYPE ~
                to record appropriate types for the function ~x0."
               fn type)))
  ///
  ;; for (STD::DEFLIST ATJ-CHECK-NO-AIJ-TYPE-LIST ...) below:
  (defrule not-atj-check-no-aij-type-of-nil
    (not (atj-check-no-aij-type nil fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atj-check-no-aij-type-list (x fn)
  :guard (and (atj-type-listp x) (symbolp fn))
  :short "Lift @(tsee atj-check-no-aij-type) to lists."
  (atj-check-no-aij-type x fn)
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-check-no-aij-term
  :short "Check that a term does not use any AIJ types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The check fails for all quoted constants except @('t') and @('nil'),
     which are translated to Java booleans.
     Other quoted constants are only allowed
     as arguments of the functions in @(tsee *atj-jprim-constr-fns*),
     and those calls are checked as a whole,
     without recursively descending in their arguments.")
   (xdoc::p
    "We disallow calls of the ACL2 functions natively implemnted in AIJ,
     except for @(tsee equal), @(tsee if), and @(tsee not).
     In the context of the other checks,
     these do not cause the use of AIJ types.
     We disallow the Java primitive value deconstructors
     except @(tsee boolean-value->bool):
     the former return AIJ types and thus cause their use;
     the latter is translated to a no-op in Java,
     and it is needed to convert ACL2 terms that represent Java booleans
     to actual ACL2 booleans (e.g. in @(tsee if) tests).
     We disallow the Java primitive array conversions with lists,
     because they involve AIJ types.
     Calls of all the other functions are allowed,
     in particular the other functions translated to Java,
     which are all checked to satisfy the requirement of not using AIJ types."))

  (define atj-check-no-aij-term ((term pseudo-termp) (fn symbolp))
    :returns (yes/no booleanp)
    (b* (((when (pseudo-term-case term :null))
          (raise "Internal error: null term."))
         ((when (pseudo-term-case term :var)) t)
         ((when (pseudo-term-case term :quote))
          (or (equal term acl2::*t*)
              (equal term acl2::*nil*)
              (raise "The function ~x0 includes the quoted constant ~x1, ~
                      which violates the checks required by :NO-AIJ-TYPES T."
                     fn term)))
         (args (pseudo-term-call->args term))
         (fn/lambda (pseudo-term-call->fn term))
         ((when (member-eq fn/lambda *atj-jprim-constr-fns*))
          (b* (((unless (= (len args) 1))
                (raise "Internal error: ~x0 has arguments ~x1."
                       fn/lambda args)))
            (or (pseudo-term-case (car args) :quote)
                (raise "The function ~x0 calls ~x1 on a term ~x2, ~
                        which violates the checks required by :NO-AIJ-TYPES T."
                       fn fn/lambda (car args)))))
         ((when (member-eq fn/lambda *atj-jprimarr-new-init-fns*))
          (b* (((unless (= (len args) 1))
                (raise "Internal error: ~x0 has arguments ~x1."
                       fn/lambda args))
               ((mv okp terms) (fty-check-list-call (car args)))
               ((unless okp)
                (raise "The function ~x0 calls ~x1 on a term ~x2, ~
                        which violates the checks ~
                        required by :NO-AIJ-TYPES T."
                       fn fn/lambda (car args))))
            (atj-check-no-aij-term-list terms fn)))
         (- (atj-check-no-aij-term-list args fn))
         ((when (pseudo-lambda-p fn/lambda))
          (atj-check-no-aij-term (pseudo-lambda->body fn/lambda) fn))
         ((when (or (and (member-eq fn/lambda *aij-natives*)
                         (not (eq fn/lambda 'equal))
                         (not (eq fn/lambda 'if))
                         (not (eq fn/lambda 'not)))
                    (and (member-eq fn/lambda *atj-jprim-deconstr-fns*)
                         (not (eq fn/lambda 'boolean-value->bool$inline)))
                    (member-eq fn/lambda *atj-jprimarr-conv-tolist-fns*)
                    (member-eq fn/lambda *atj-jprimarr-conv-fromlist-fns*)))
          (raise "The function ~x0 calls the function ~x1, ~
                  which violates the checks required by :NO-AIJ-TYPES T."
                 fn fn/lambda)))
      t)
    :measure (pseudo-term-count term))

  (define atj-check-no-aij-term-list ((terms pseudo-term-listp) (fn symbolp))
    :returns (yes/no booleanp)
    (or (endp terms)
        (and (atj-check-no-aij-term (car terms) fn)
             (atj-check-no-aij-term-list (cdr terms) fn)))
    :measure (pseudo-term-list-count terms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-no-aij-types+body ((in-types atj-type-listp)
                                     (out-types atj-type-listp)
                                     (body pseudo-termp)
                                     (fn symbolp))
  :returns (yes/no booleanp)
  :short "Check that a function to translate to Java
          does not use any AIJ types."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the argument and result types,
     as well as the body."))
  (and (atj-check-no-aij-type-list in-types fn)
       (atj-check-no-aij-type-list out-types fn)
       (atj-check-no-aij-term body fn)))
