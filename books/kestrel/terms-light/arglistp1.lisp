; A lightweight book about the build-in function arglistp1
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm arglistp1-forward-to-symbol-listp
   (implies (arglistp1 lst)
            (symbol-listp lst))
   :rule-classes :forward-chaining)
