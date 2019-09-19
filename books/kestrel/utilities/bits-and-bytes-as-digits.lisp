; Representation of Natural Numbers as Bit and Byte Digits
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "kestrel/utilities/bytes-as-digits" :dir :system)
(include-book "kestrel/utilities/digits-any-base/defdigit-grouping" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdigit-grouping bits/bytes-digit-grouping
  :smaller bits-as-digits-in-base-2
  :larger bytes-as-digits-in-base-256
  :group-bendian bits=>bebytes
  :group-lendian bits=>lebytes
  :ungroup-bendian bebytes=>bits
  :ungroup-lendian lebytes=>bits
  :parents (kestrel-utilities
            bits-as-digits-in-base-2
            bytes-as-digits-in-base-256)
  :short
  (xdoc::topstring
   "Specialized versions of "
   (xdoc::seetopic
    "digits-any-base"
    "the operations to group and ungroup digits")
   "that are bits (base 2) and bytes (base 256)."))
