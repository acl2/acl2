; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "ihs/basic-definitions" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection logappn
  :parents (acl2::logapp)
  :short "N-ary version of @(tsee acl2::logapp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This supports readable appending of multiple bit chunks, e.g.")
   (xdoc::codeblock
    "(logappn 32 base"
    "         8 padding"
    "         24 offset)")
   (xdoc::p
    "This belongs to a more general library."))

  (defun logappn-fn (args)
    (cond ((endp args) 0)
          ((endp (cdr args)) 0)
          (t `(logapp ,(car args) ,(cadr args) ,(logappn-fn (cddr args))))))

  (defmacro logappn (&rest args)
    (logappn-fn args)))
