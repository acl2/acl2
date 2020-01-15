; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file [books]/3BSD-mod.txt.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)
;          Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/plist-worldp-with-formals
  :parents (std/system)
  :short "Theorems about @('plist-worldp-with-formals')
          (see the ACL2 source code)."

  (defthm plist-worldp-when-plist-worldp-with-formals-cheap
    (implies (not (plist-worldp wrld))
             (not (plist-worldp-with-formals wrld)))
    :rule-classes ((:rewrite :backchain-limit-lst (0)))))

(in-theory (disable plist-worldp-with-formals))
