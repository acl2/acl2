; Ethereum Library -- Scalars
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "kestrel/utilities/xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc scalars
  :parents (basics)
  :short "Modeling of scalars."
  :long
  (xdoc::topp
   "[YP:3] says that scalars are
    non-negative integers in the set @($\\mathbb{N}$),
    i.e. natural numbers.
    We use the library type <see topic='@(url fty::basetypes)'>@('nat')</see>
    to model scalars in our Ethereum model."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum nat/error
  :parents (basics)
  :short "Union of @(':error') and @(see scalars)."
  (:error :fields () :ctor-body ':error :cond (eq x :error))
  (:bytes :fields ((nat :type nat :acc-body x)) :ctor-body nat))

(defsection nat/error-ext
  :extension nat/error

  (defruled nat/error-p-alt-def
    (equal (nat/error-p x)
           (or (eq x :error)
               (natp x)))
    :enable nat/error-p)

  (defrule disjoint-nat/error
    (not (and (eq x :error)
              (natp x)))
    :rule-classes nil)

  (defrule nat/error-p-when-natp
    (implies (natp x)
             (nat/error-p x))
    :enable nat/error-p)

  (defrule nat/error-p-of-error
    (nat/error-p :error))

  (defrule natp-when-nat/error-p-and-not-error
    (implies (and (nat/error-p x)
                  (not (nat/error-case x :error)))
             (natp x))
    :enable nat/error-p))
