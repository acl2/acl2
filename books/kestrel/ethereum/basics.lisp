; Ethereum Library -- Basics
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/fixbytes/instances" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc basics
  :parents (ethereum)
  :short "Some basic Ethereum notions and utilities.")

(local (xdoc::set-default-parents basics))

(xdoc::order-subtopics basics nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bytes
  :short "Modeling of bytes."
  :long
  "<p>
   YP:B describes @($\\mathbb{O}$) as the set of 8-bit bytes.
   We use the library type @(tsee ubyte8) of unsigned 8-bit bytes
   to model bytes in our Ethereum model.
   Unless otherwise stated, in the documentation of our Ethereum model
   the unqualified term `byte' denotes an 8-bit byte.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc byte-arrays
  :short "Modeling of byte arrays."
  :long
  "<p>
   YP:3 mentions the set @($\\mathbb{B}$) of byte arrays,
   and YP:(178) defines it as consisting of all finite sequences of bytes.
   Given our modeling of @(tsee bytes),
   we use the library type @(tsee ubyte8-list) of
   true lists of unsigned 8-bit bytes
   to model byte arrays in our Ethereum model;
   the definition of this library type corresponds to YP:(178).
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc scalars
  :short "Modeling of scalars."
  :long
  "<p>
   YP:3 says that scalars are
   non-negative integers in the @($\\mathbb{N}$) set,
   i.e. natural numbers.
   We use the library type <see topic='@(url fty::basetypes)'>@('nat')</see>
   to model scalars in our Ethereum model.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum ubyte8list/error
  :short "Union of @(':error') and true lists of @(see bytes)."
  (:error :fields () :ctor-body ':error :cond (eq x :error))
  (:bytes :fields ((bytes :type ubyte8-list :acc-body x)) :ctor-body bytes)
  ///

  (defrule disjoint-ubyte8list/error
    (not (and (eq :error x)
              (ubyte8-listp x)))
    :rule-classes nil)

  (defrule ubyte8list/error-p-when-ubyte8-listp
    (implies (ubyte8-listp x)
             (ubyte8list/error-p x))
    :enable ubyte8list/error-p)

  (defrule ubyte8list/error-p-of-error
    (ubyte8list/error-p :error))

  (defrule ubyte8-listp-when-bytes/error-p-and-not-error
    (implies (and (ubyte8list/error-p x)
                  (not (ubyte8list/error-case x :error)))
             (ubyte8-listp x))
    :enable ubyte8list/error-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum nat/error
  :short "Union of @(':error') and @(see scalars)."
  (:error :fields () :ctor-body ':error :cond (eq x :error))
  (:bytes :fields ((nat :type nat :acc-body x)) :ctor-body nat)
  ///

  (defrule disjoint-nat/error
    (not (and (eq :error x)
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
