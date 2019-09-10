; Representation of Natural Numbers as Unsigned 11-Bit Byte Digits
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/ubyte11-list" :dir :system)
(include-book "kestrel/utilities/digits-any-base/defdigits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdigits ubyte11s-as-digits-in-base-2048
  :base 2048
  :digits-pred ubyte11-listp
  :digits-fix ubyte11-list-fix
  :bendian-to-nat beubyte11s=>nat
  :lendian-to-nat leubyte11s=>nat
  :nat-to-bendian nat=>beubyte11s
  :nat-to-lendian nat=>leubyte11s
  :digits-pred-hints (("Goal" :in-theory (enable ubyte11-listp
                                                 ubyte11p
                                                 dab-digit-listp
                                                 dab-digitp)))
  :digits-fix-hints (("Goal" :in-theory (enable ubyte11-list-fix
                                                ubyte11-fix
                                                ubyte11p
                                                dab-digit-list-fix
                                                dab-digit-fix
                                                dab-digitp)))
  :digits-description "unsigned 11-bit bytes"
  :parents (kestrel-utilities ubyte11)
  :short
  (xdoc::topstring
   "Specialized versions of "
   (xdoc::seetopic
    "digits-any-base"
    "the operations to convert between natural numbers and digits")
   " that use "
   (xdoc::seetopic "ubyte11" "unsigned 11-bit bytes")
   " as digits, in base 2048."))
