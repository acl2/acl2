; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/fty/ubyte8" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-unsigned-chars
  :parents (atc-integers)
  :short "A model of C @('unsigned char')s."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a fixtype for values of the @('unsigned char') type.
     We do not define any operations (e.g. arithmetic) on these values,
     because these values are subjected to promotions and conversions
     to values of different types (e.g. @('int'))
     prior to applying the actual operations on them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uchar
  :short "Fixtype of C @('unsigned char') values [C:6.2.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We represent these are 8-bit unsigned integers.
     While [C:5.2.4.2.1/1] [C:6.2.6.1/3] allows these to have more than 8 bits,
     8 bits is an overwhelmingly common choice.
     In the future, we may generalize this model."))
  ((get acl2::ubyte8))
  :tag :uchar
  :layout :list
  :pred ucharp)
