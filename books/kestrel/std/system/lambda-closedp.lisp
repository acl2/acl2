; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-lambdap")

(local (include-book "kestrel/std/system/all-vars" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-closedp ((lambd pseudo-lambdap))
  :returns (yes/no booleanp)
  :parents (std/system/term-queries)
  :short "Check if a lambda expression is closed,
          i.e. it has no free variables."
  (subsetp-eq (all-vars (lambda-body lambd))
              (lambda-formals lambd))
  :guard-hints (("Goal" :in-theory (enable pseudo-lambdap))))
