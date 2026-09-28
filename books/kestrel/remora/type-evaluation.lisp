; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-evaluation")
(include-book "type-values-and-environments")
(include-book "free-variable-operations")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable ispace-valuep-when-result-not-error
                          ispace-value-listp-when-result-not-error
                          type-valuep-when-result-not-error
                          type-value-listp-when-result-not-error
                          var+typevalue-p-when-result-not-error
                          var+typevalue-listp-when-result-not-error
                          typep-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-evaluation
  :parents (dynamic-semantics)
  :short "Evaluation of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is part of our interpretive operational semantics of Remora.
     Types evaluate to type values.
     The ispaces in array and bracket types are evaluated,
     via @(see ispace-evaluation),
     in the ispace dynamic environment
     that is part of the type dynamic environment."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines eval-types
  :short "Evaluate types and lists of types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-type ((type typep) (denv type-denvp))
    :returns (tval type-value-resultp)
    :parents (type-evaluation eval-types)
    :short "Evaluate a type to a type value."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the environment.")
     (xdoc::p
      "A base type evaluates to itself.")
     (xdoc::p
      "For an array type,
       we evaluate the element type and the ispace,
       we turn the ispace value into a list of dimensions,
       and we put the results together into an array type value.")
     (xdoc::p
      "A bracket type is treated similarly to an array type,
       but instead of an ispace we have a list of ispaces,
       whose values are turned into lists of dimensions,
       which are concatenated.")
     (xdoc::p
      "For a function type, we evaluate input and output types,
       and put the resulting type values together into a function type value.")
     (xdoc::p
      "Universal, product, and sum types evaluate essentially to themselves.
       They are treated like lambda abstractions.
       The resulting type values include dynamic environments
       with the bindings for
       the free ispace and type variables of these types,
       obtained by restricting the current dynamic environment
       to those variables."))
    (type-case
     type
     :var (type-denv-lookup-type type.var denv)
     :base (type-value-base type.type)
     :array (b* (((ok elem-tval) (eval-type type.elem denv))
                 ((ok ival) (eval-ispace type.ispace (type-denv->ienv denv)))
                 (dims (ispace-value-to-dims ival)))
              (make-type-value-array :elem elem-tval :dims dims))
     :bracket (b* (((ok elem-tval) (eval-type type.elem denv))
                   ((ok ivals) (eval-ispace-list type.ispaces
                                                 (type-denv->ienv denv)))
                   (natss (ispace-value-list-to-dims ivals))
                   (nats (append-all natss)))
                (make-type-value-array :elem elem-tval :dims nats))
     :fun (b* (((ok in-tval) (eval-type type.in denv))
               ((ok out-tval) (eval-type type.out denv)))
            (make-type-value-fun :in in-tval :out out-tval))
     :funn (b* (((ok in-tvals) (eval-type-list type.in denv))
                ((ok out-tval) (eval-type type.out denv)))
             (nest-function-type-values in-tvals out-tval))
     :forall (make-type-value-forall
              :param type.param
              :body type.body
              :denv (type-denv-restrict (type-free-ispace-vars type)
                                        (type-free-type-vars type)
                                        denv))
     :foralln (make-type-value-forall
               :param (car type.params)
               :body (forall-curried-body type.params type.body)
               :denv (type-denv-restrict (type-free-ispace-vars type)
                                         (type-free-type-vars type)
                                         denv))
     :pi (make-type-value-pi
          :param type.param
          :body type.body
          :denv (type-denv-restrict (type-free-ispace-vars type)
                                    (type-free-type-vars type)
                                    denv))
     :pin (make-type-value-pi
           :param (car type.params)
           :body (pi-curried-body type.params type.body)
           :denv (type-denv-restrict (type-free-ispace-vars type)
                                     (type-free-type-vars type)
                                     denv))
     :sigma (make-type-value-sigma
             :param type.param
             :body type.body
             :denv (type-denv-restrict (type-free-ispace-vars type)
                                       (type-free-type-vars type)
                                       denv))
     :sigman (make-type-value-sigma
              :param (car type.params)
              :body (sigma-curried-body type.params type.body)
              :denv (type-denv-restrict (type-free-ispace-vars type)
                                        (type-free-type-vars type)
                                        denv)))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define eval-type-list ((types type-listp) (denv type-denvp))
    :returns (tvals type-value-list-resultp)
    :parents (type-evaluation eval-types)
    :short "Evaluate a list of types to a list of type values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate each type in turn
       and return the list of results in the same order."))
    (b* (((when (endp types)) nil)
         ((ok tval) (eval-type (car types) denv))
         ((ok tvals) (eval-type-list (cdr types) denv)))
      (cons tval tvals))
    :measure (type-list-count types)

    ///

    (defret len-of-eval-type-list
      (implies (not (reserrp tvals))
               (equal (len tvals)
                      (len types)))
      :hints (("Goal"
               :induct (len types)
               :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  :flag-local nil

  :guard-hints
  (("Goal" :in-theory (enable acl2::true-list-listp-when-nat-list-listp)))

  ///

  (fty::deffixequiv-mutual eval-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-var+type? ((var+type? var+type?-p) (denv type-denvp))
  :returns (var+tval var+typevalue-resultp)
  :short "Evaluate a variable with an optional type
          to a variable with a type value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is unchanged;
     its associated type must be present, and is evaluated to a type value."))
  (b* (((ok type) (var+type?->type-or-err var+type?))
       ((ok tval) (eval-type type denv)))
    (make-var+typevalue :var (var+type?->var var+type?) :type tval)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-var+type?-list ((var+types var+type?-listp) (denv type-denvp))
  :returns (var+tvals var+typevalue-list-resultp)
  :short "Evaluate a list of variables with optional types
          to a list of variables with type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate each element in turn
     and return the list of results in the same order."))
  (b* (((when (endp var+types)) nil)
       ((ok var+tval) (eval-var+type? (car var+types) denv))
       ((ok var+tvals) (eval-var+type?-list (cdr var+types) denv)))
    (cons var+tval var+tvals))

  ///

  (defret len-of-eval-var+type?-list
    (implies (not (reserrp var+tvals))
             (equal (len var+tvals)
                    (len var+types)))
    :hints (("Goal"
             :induct (len var+types)
             :in-theory (enable len)))))
