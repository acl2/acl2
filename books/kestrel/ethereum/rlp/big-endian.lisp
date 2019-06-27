; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/bytes-as-digits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-big-endian-representations
  :parents (rlp)
  :short "Big-endian representation of scalars in RLP."
  :long
  (xdoc::topstring
   (xdoc::p
    "The library function @(tsee nat=>bebytes*)
     corresponds to @($\\mathtt{BE}$) [YP:(181)].
     Note that no leading 0 is allowed, even for representing 0,
     which is thus represented by the empty list of digits.")
   (xdoc::p
    "We introduce two linear rules
     that relate certain specific upper bounds on
     numbers and their big-endian representations in base 256.
     These upper bounds apply to the encoding of lengths in RLP."))

  (defruled len-of-nat=>bebytes*-leq-8
    (implies (< nat (expt 2 64))
             (<= (len (nat=>bebytes* nat))
                 8))
    :rule-classes :linear
    :enable nat=>bebytes*
    :use (:instance acl2::len-of-nat=>bebytes*-leq-width (width 8)))

  (defruled bebytes->nat-lt-2^64
    (implies (<= (len digits) 8)
             (< (bebytes=>nat digits)
                (expt 2 64)))
    :rule-classes :linear
    :use (:instance acl2::len-of-nat=>bebytes*-leq-width
          (width 8) (nat (bebytes=>nat digits)))))
