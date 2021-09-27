; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/ubyte256" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ values
  :parents (dynamic-semantics)
  :short "Yul values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Yul, being generic, is parameterized over
     a collection of supported types and their values.
     For the EVM dialect of Yul, which is our initial interest,
     the only supported type is @('u256'), i.e. unsigned 256-bit integers.
     Based on discussions on Gitter,
     it is best to view this as a type of 256-bit words,
     rather than as a type of 256-bit unsigned integers,
     because the intent is to match the EVM notion of word,
     which can be operated upon as an either unsigned or signed integer.
     Nonetheless, in our ACL2 formalization,
     we represent 256-bit words as 256-bit unsigned integers,
     which can be thought of as bit vectors.
     We define values as wrapped 256-bit unsigned integers,
     meant to represent 256-bit words.
     As explained in the "
    (xdoc::seetopic "static-semantics" "static semantics")
    ", for now we do not have explicit types,
     i.e. we have just one type.
     This matches the fact that we have just one kind of values.
     We should extend and genearalize this."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod value
  :short "Fixtype of values."
  ((get ubyte256))
  :tag :value
  :pred valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist value-list
  :short "Fixtype of lists of values."
  :elt-type value
  :true-listp t
  :elementp-of-nil nil
  :pred value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-result
  :short "Fixtype of errors and values."
  :ok value
  :pred value-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-list-result
  :short "Fixtype of errors and lists of values."
  :ok value-list
  :pred value-list-resultp)
