; APT (Automated Program Transformations) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "tools/rewrite-dollar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-call-acl2-rewriter ((matrix pseudo-termp)
                                  (method-rules symbol-listp)
                                  ctx
                                  state)
  :returns (mv erp
               (result "A tuple @('(rewritten-term used-rules)')
                        satisfying
                        @('(typed-tuplep pseudo-termp symbol-listp result)').")
               state)
  :mode :program
  :parents (solve-implementation)
  :short "Call the ACL2 rewriter on the matrix of @('old')."
  (b* (((er (list* rewritten-term used-rules pairs))
        (rewrite$ matrix :ctx ctx :in-theory `(enable ,@method-rules)))
       ((unless (null pairs))
        (value (raise "Internal error: ~
                       REWRITE$ returned non-NIL pairs ~x0 ~
                       even though it was called without forced assumptions."
                      pairs))))
    (value (list rewritten-term used-rules))))
