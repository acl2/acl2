; Theorems about make-lambda-nest
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-lambda-nest")
(include-book "lambdas-closed-in-termp")
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(defthm lambdas-closed-in-termp-of-make-lambda-nest
  (implies (and (symbol-alistp bindings)
                (pseudo-term-listp (strip-cdrs bindings))
                (lambdas-closed-in-termsp (strip-cdrs bindings))
                (pseudo-termp body)
                (lambdas-closed-in-termp body))
           (lambdas-closed-in-termp (make-lambda-nest bindings body)))
  :hints (("Goal" :in-theory (enable make-lambda-nest lambdas-closed-in-termp))))
