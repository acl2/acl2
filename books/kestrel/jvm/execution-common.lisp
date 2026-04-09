; Support for concrete and symbolic execution
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ;todo: use jvm package?

(include-book "jvm") ; todo: reduce
(include-book "th")

;; The height of the call stack of thread (TH) in state S.
(defund stack-height (s)
  (declare (xargs :guard (and (jvm::jvm-statep s)
                              (jvm::bound-in-alistp (th) (jvm::thread-table s)))))
  (jvm::call-stack-size (jvm::call-stack (th) s)))
