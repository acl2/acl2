; Standard String Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/strings/digit-to-char
  :parents (std/strings)
  :short "Theorems about the built-in @(tsee digit-to-char)."

  (defthm digit-to-char-injective
    (implies (and (integer-range-p 0 16 x)
                  (integer-range-p 0 16 y))
             (equal (equal (digit-to-char x) (digit-to-char y))
                    (equal x y)))
    :hints (("Goal" :in-theory (enable digit-to-char)))))
