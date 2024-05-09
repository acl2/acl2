; Representation of Natural Numbers as Byte Digits
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/byte-list" :dir :system)
(include-book "kestrel/utilities/digits-any-base/defdigits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdigits bytes-as-digits-in-base-256
  :base 256
  :digit-pred bytep
  :digit-fix byte-fix
  :digits-pred byte-listp
  :digits-fix byte-list-fix
  :bendian-to-nat bebytes=>nat
  :lendian-to-nat lebytes=>nat
  :nat-to-bendian nat=>bebytes
  :nat-to-lendian nat=>lebytes
  :digit-pred-hints (("Goal" :in-theory (enable bytep
                                                dab-digitp)))
  :digit-fix-hints (("Goal" :in-theory (enable byte-fix
                                               bytep
                                               dab-digit-fix
                                               dab-digitp)))
  :digits-pred-hints (("Goal" :in-theory (enable byte-listp
                                                 bytep
                                                 dab-digit-listp
                                                 dab-digitp)))
  :digits-fix-hints (("Goal" :in-theory (enable byte-list-fix
                                                byte-fix
                                                bytep
                                                dab-digit-list-fix
                                                dab-digit-fix
                                                dab-digitp)))
  :digits-description "bytes"
  :parents (kestrel-utilities bytep)
  :short
  (xdoc::topstring
   "Specialized versions of "
   (xdoc::seetopic
    "digits-any-base"
    "the operations to convert between natural numbers and digits")
   " that use "
   (xdoc::seetopic "bytep" "bytes")
   " as digits, in base 256."))
