; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Quan Luu (quan.luu@kestrel.edu)
;          Sarah Johnson

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "expression-values-and-environments")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitives-evaluation-on-types
  :parents (dynamic-semantics)
  :short "Evaluation of Remora primitives on types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Remora primitives, like other Remora functions,
     may be applied to types, ispaces, or expressions,
     according to the stages implied by their curried function types.
     See @(tsee primop-value) for a discussion of the stages.")
   (xdoc::p
    "Here we define the application of primitives to types;
     more precisely, the application of
     primitive operation values satisfying @(tsee primop-value-tfunop)
     to type values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-primop-tfun ((op primop-valuep) (tval type-valuep))
  :guard (primop-value-tfunp op)
  :returns (val expr-value-resultp)
  :short "Evaluate the application of a primitive operation value
          to a type value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart, for primitive operations,
     of applying a type lambda abstraction to a type value:
     it is called by @(tsee eval-tapp)
     on a scalar primitive operation value
     and the type argument value.")
   (xdoc::p
    "The guard requires the value to be applicable to type values
     (see @(tsee primop-value-tfunp)).
     We check that the type value matches, in kind,
     the type parameter of the operation,
     i.e. the one in the operation's type in @(tsee primop-types);
     then we construct the next instantiation stage of the operation,
     which stores the type value received.
     Anything else is an error."))
  (primop-value-case
   op
   :head (b* (((unless (type-values-match-type-vars-p
                        (list tval)
                        (list (type-var-atom "t"))))
               (reserr nil)))
           (expr-value-primop (primop-value-head-t tval)))
   :tail (b* (((unless (type-values-match-type-vars-p
                        (list tval)
                        (list (type-var-atom "t"))))
               (reserr nil)))
           (expr-value-primop (primop-value-tail-t tval)))
   :length (b* (((unless (type-values-match-type-vars-p
                          (list tval)
                          (list (type-var-atom "t"))))
                 (reserr nil)))
             (expr-value-primop (primop-value-length-t tval)))
   :append (b* (((unless (type-values-match-type-vars-p
                          (list tval)
                          (list (type-var-atom "t"))))
                 (reserr nil)))
             (expr-value-primop (primop-value-append-t tval)))
   :reverse (b* (((unless (type-values-match-type-vars-p
                           (list tval)
                           (list (type-var-atom "t"))))
                  (reserr nil)))
              (expr-value-primop (primop-value-reverse-t tval)))
   :index (b* (((unless (type-values-match-type-vars-p
                           (list tval)
                           (list (type-var-atom "t"))))
                  (reserr nil)))
            (expr-value-primop (primop-value-index-t tval)))
   :index2d (b* (((unless (type-values-match-type-vars-p
                           (list tval)
                           (list (type-var-atom "t"))))
                  (reserr nil)))
              (expr-value-primop (primop-value-index2d-t tval)))
   :reshape (b* (((unless (type-values-match-type-vars-p
                           (list tval)
                           (list (type-var-atom "t"))))
                  (reserr nil)))
              (expr-value-primop (primop-value-reshape-t tval)))
   :flatten (b* (((unless (type-values-match-type-vars-p
                           (list tval)
                           (list (type-var-atom "t"))))
                  (reserr nil)))
              (expr-value-primop (primop-value-flatten-t tval)))
   :transpose2d (b* (((unless (type-values-match-type-vars-p
                           (list tval)
                           (list (type-var-atom "t"))))
                  (reserr nil)))
              (expr-value-primop (primop-value-transpose2d-t tval)))
   :otherwise (prog2$ (impossible) (reserr nil)))
  :guard-hints (("Goal" :in-theory (enable primop-value-tfunp
                                           type-values-match-type-vars-p)))

  ///

  (defret expr-value-wfp-of-eval-primop-tfun
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hints (("Goal" :in-theory (enable expr-value-wfp
                                       check-dims-of-expr-value
                                       check-dims-of-primop-value)))))
