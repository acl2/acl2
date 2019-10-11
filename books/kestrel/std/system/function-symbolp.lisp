; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/function-symbolp
  :parents (std/system/event-name-queries)
  :short "Theorems about @(tsee function-symbolp)."

  (defthm function-symbolp-forward-to-symbolp
    (implies (and (function-symbolp fn wrld)
                  (plist-worldp wrld))
             (symbolp fn))
    :rule-classes :forward-chaining))

(in-theory (disable function-symbolp))
