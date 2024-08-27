; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the community-books file 3BSD-mod.txt.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/w
  :parents (std/system)
  :short "Theorems about @(tsee w)."

  (defthm plist-worldp-of-w-when-state-p
    (implies (state-p state)
             (plist-worldp (w state)))
    :hints (("Goal" :in-theory (enable state-p)))))

(in-theory (disable w))
