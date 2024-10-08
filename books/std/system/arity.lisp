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

(defsection std/system/arity
  :parents (std/system/function-queries)
  :short "Theorems about @(tsee arity)."

  (defthm arity-iff
    (iff (arity fn wrld)
         (or (consp fn)
             (function-symbolp fn wrld)))
    :hints (("Goal" :in-theory (enable arity)))))

(in-theory (disable arity))
