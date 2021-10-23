; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "language/top")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ outcomes
  :parents (language)
  :short "Syntheto outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the possible outcomes of submitting a Syntheto top-level
     constract to ACL2 through the ACL2 Bridge."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum outcome
    :short "Fixtype of Syntheto outcomes."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each type of top-level definition, when submitted to ACL2,
       will be accepted or rejected.  The success or failure
       of the submission is modeled by an outcome, which is returned
       to the submitter.")
     (xdoc::p
      "A function or clique of mutually-recursive functions, when
       submitted successfully to ACL2, is represented by @('function-success').
       Similarly, a type definition or clique of mutually-recursive type
       definitions is represented by @('type-success').  Specifications,
       theorems, and transformations also have success types.")
     (xdoc::p
      "Since a successful transformation results in new submitted top-level
       definitions, those are returned as part of the success outcome.")
     (xdoc::p
      "For submission of a top-level definition to be accepted,
       there are certain implicit proof obligations such as termination and
       guard verification.  If one of these fails, a
       @('proof-obligation-failure') outcome is returned, containing
       an expression that could not be proved. This failure may result for a
       number of different reasons, and may result from a number of different
       top-level constructs including failure to prove the applicability
       condition of a transformation.")
     (xdoc::p
      "If a theorem is submitted that is not mechanically proved by ACL2,
       a @('theorem-failure') outcome is returned.")
     (xdoc::p
      "If a transformation is submitted that is applicable, but fails
       due to some other reason, potentially a @('transformation-failure')
       outcome is returned.")
     (xdoc::p
      "Any other submission failure results in a @('unexpected-failure')
       outcome, which might have been expected but is at least not otherwise
       classified."))
    (:function-success ((message stringp)))
    (:type-success ((message stringp)))
    (:specification-success ((message stringp)))
    (:theorem-success ((message stringp)))
    (:transformation-success ((message stringp)
                              (toplevels toplevel-listp)))
    (:proof-obligation-failure ((message stringp)
                                (obligation-expr expressionp)
                                ;; (source-expr expressionp)
                                ;; (toplevel-name stringp)
                                ))
    (:theorem-failure ((message stringp)))
    (:transformation-failure ((message stringp)))
    (:unexpected-failure ((message stringp)))
    :pred outcomep)

;; Defines outcome--make-myself (see language/make-myself.lisp)
(make-mm-sum outcome
  ( (:function-success . ((message . string)))
    (:type-success . ((message . string)))
    (:specification-success . ((message . string)))
    (:theorem-success . ((message . string)))
    (:transformation-success . ((message . string)
                                (toplevels . toplevel-list)))
    (:proof-obligation-failure . ((message . string)
                                  (obligation-expr . expression)
                                  ;; (source-expr . expression)
                                  ;; (toplevel-name . string)
                                  ))
    (:theorem-failure . ((message . string)))
    (:transformation-failure . ((message . string)))
    (:unexpected-failure . ((message . string))) ))

(fty::deflist outcome-list
  :short "Fixtype of lists of Syntheto Ocutomes"
  :elt-type outcome
  :true-listp t
  :elementp-of-nil nil
  :pred outcome-listp)

(acl2::assert-equal (outcome--make-myself
                     (syntheto::make-outcome-proof-obligation-failure
                      :message "could not prove this"
                      :obligation-expr (syntheto::make-expression-call
                                        :function (syntheto::make-identifier :name "myfun")
                                        :types (list)
                                        :arguments (list (syntheto::make-expression-literal
                                                          :get (syntheto::make-literal-integer :value 1))))
                      ;; :source-expr (syntheto::make-expression-call
                      ;;                   :function (syntheto::make-identifier :name "myfun2")
                      ;;                   :types (list)
                      ;;                   :arguments (list (syntheto::make-expression-literal
                      ;;                                     :get (syntheto::make-literal-integer :value 1))))
                      ;; :toplevel-name "Foo"
                      ))
                    '(syntheto::make-outcome-proof-obligation-failure
                      :message "could not prove this"
                      :obligation-expr (syntheto::make-expression-call
                                        :function (syntheto::make-identifier :name "myfun")
                                        :types (list)
                                        :arguments (list (syntheto::make-expression-literal
                                                          :get (syntheto::make-literal-integer :value 1))))
                      ;; :source-expr (syntheto::make-expression-call
                      ;;                   :function (syntheto::make-identifier :name "myfun2")
                      ;;                   :types (list)
                      ;;                   :arguments (list (syntheto::make-expression-literal
                      ;;                                     :get (syntheto::make-literal-integer :value 1))))
                      ;; :toplevel-name "Foo"
                      ))

(define tops-from-transform-outcomes ((outcomes outcome-listp))
  :returns (l toplevel-listp)
  (if (endp outcomes)
      ()
    (let ((r (tops-from-transform-outcomes (cdr outcomes))))
      (if (equal (outcome-kind (car outcomes))
                 ':transformation-success)
          (append (outcome-transformation-success->toplevels (car outcomes))
                  r)
        r))))
