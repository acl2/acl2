; Representation of Natural Numbers as Bit and Unsigned 11-Bit Byte Digits
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "kestrel/utilities/ubyte11s-as-digits" :dir :system)
(include-book "kestrel/utilities/digits-any-base/defdigit-grouping" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdigit-grouping bits/ubyte11s-digit-grouping
  :smaller bits-as-digits-in-base-2
  :larger ubyte11s-as-digits-in-base-2048
  :group-bendian bits=>beubyte11s
  :group-lendian bits=>leubyte11s
  :ungroup-bendian beubyte11s=>bits
  :ungroup-lendian leubyte11s=>bits
  :parents (kestrel-utilities
            bits-as-digits-in-base-2
            ubyte11s-as-digits-in-base-2048)
  :short
  (xdoc::topstring
   "Specialized versions of "
   (xdoc::seetopic
    "digits-any-base"
    "the operations to group and ungroup digits")
   "that are bits (base 2) and unsigned 11-bit bytes (base 2048)."))
