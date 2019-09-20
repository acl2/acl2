; Representation of Natural Numbers as Bit Digits
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/bit-list" :dir :system)
(include-book "kestrel/utilities/digits-any-base/defdigits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdigits bits-as-digits-in-base-2
  :base 2
  :digits-pred bit-listp
  :digits-fix bit-list-fix
  :bendian-to-nat bebits=>nat
  :lendian-to-nat lebits=>nat
  :nat-to-bendian nat=>bebits
  :nat-to-lendian nat=>lebits
  :digits-pred-hints (("Goal" :in-theory (enable bit-listp
                                                 bitp
                                                 dab-digit-listp
                                                 dab-digitp)))
  :digits-fix-hints (("Goal" :in-theory (enable bit-list-fix
                                                bfix
                                                bitp
                                                dab-digit-list-fix
                                                dab-digit-fix
                                                dab-digitp)))
  :digits-description "bits"
  :parents (kestrel-utilities bitp)
  :short
  (xdoc::topstring
   "Specialized versions of "
   (xdoc::seetopic
    "digits-any-base"
    "the operations to convert between natural numbers and digits")
   " that use "
   (xdoc::seetopic "bitp" "bits")
   " as digits, in base 2."))
