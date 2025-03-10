; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the community books file /3BSD-mod.txt.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/geprops
  :parents (std/system)
  :short "Theorems about @('getprops') (see the ACL2 source code)."

  (defthm alistp-of-getprops
    (alistp (getprops key world-name w))))

(in-theory (disable getprops))
