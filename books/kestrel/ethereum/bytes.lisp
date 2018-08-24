; Ethereum Library -- Bytes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/fixbytes/ubyte8" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bytes
  :parents (basics)
  :short "Modeling of bytes."
  :long
  (xdoc::topp
   "YP:B describes @($\\mathbb{O}$) as the set of 8-bit bytes.
    We use the library type @(tsee ubyte8) of unsigned 8-bit bytes
    to model bytes in our Ethereum model.
    Unless otherwise stated, in the documentation of our Ethereum model
    the unqualified term `byte' denotes an 8-bit byte."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc byte-arrays
  :parents (basics)
  :short "Modeling of byte arrays."
  :long
  (xdoc::topp
   "YP:3 mentions the set @($\\mathbb{B}$) of byte arrays,
    and YP:(178) defines it as consisting of all finite sequences of bytes.
    Given our modeling of @(tsee bytes),
    we use the library type @(tsee ubyte8-list) of
    true lists of unsigned 8-bit bytes
    to model byte arrays in our Ethereum model;
    the definition of this library type corresponds to YP:(178)."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum ubyte8list/error
  :parents (basics)
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
