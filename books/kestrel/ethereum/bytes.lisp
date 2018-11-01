; Ethereum Library -- Bytes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/fixbytes/defbytelist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bytes
  :parents (basics)
  :short "Bytes."
  :long
  (xdoc::topp
   "[YP:B] describes @($\\mathbb{O}$) as the set of 8-bit bytes.
    Unless otherwise stated, in the documentation of our Ethereum model,
    the unqualified `byte' denotes an 8-bit byte."))

(fty::defbyte 8
  :type byte
  :pred bytep
  :parents (bytes)
  :description "bytes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc byte-arrays
  :parents (basics)
  :short "Byte arrays."
  :long
  (xdoc::topp
   "[YP:3] mentions the set @($\\mathbb{B}$) of byte arrays,
    and [YP:(178)] defines it as consisting of all finite sequences of bytes.
    We use true lists of @(see bytes)
    to model byte arrays in our Ethereum model."))

(fty::defbytelist byte
  :pred byte-listp
  :parents (byte-arrays))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum bytelist/error
  :parents (basics)
  :short "Union of <see topic='@(url byte-arrays)'>byte arrays</see>
          and @(':error')."
  (:error :fields () :ctor-body ':error :cond (eq x :error))
  (:bytes :fields ((bytes :type byte-list :acc-body x)) :ctor-body bytes))

(defsection bytelist/error-ext
  :extension bytelist/error

  (defruled bytelist/error-p-alt-def
    (equal (bytelist/error-p x)
           (or (eq x :error)
               (byte-listp x)))
    :enable bytelist/error-p)

  (defrule disjoint-bytelist/error
    (not (and (eq x :error)
              (byte-listp x)))
    :rule-classes nil)

  (defrule bytelist/error-p-when-byte-listp
    (implies (byte-listp x)
             (bytelist/error-p x))
    :enable bytelist/error-p)

  (defrule bytelist/error-p-of-error
    (bytelist/error-p :error))

  (defrule byte-listp-when-bytelist/error-p-and-not-error
    (implies (and (bytelist/error-p x)
                  (not (bytelist/error-case x :error)))
             (byte-listp x))
    :enable bytelist/error-p))
