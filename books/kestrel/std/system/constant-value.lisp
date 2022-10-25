; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "constant-symbolp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constant-value ((const symbolp) (wrld plist-worldp))
  :returns val
  :parents (std/system/constant-queries)
  :short "Return the value of a named constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "An error occurs if the symbol is not a named constant in the world.")
   (xdoc::p
    "If it is a named constant in the world,
     we retrieve its @('const') property,
     which is the quoted value,
     and we unquote it and return it."))
  (b* (((unless (constant-symbolp const wrld))
        (raise "~x0 is not a named constant." const))
       (qval (getpropc const 'const nil wrld))
       ((unless (and (quotep qval)
                     (consp (cdr qval))
                     (eq (cddr qval) nil)))
        (raise "Internal error: ~
                the CONST property ~x0 of ~x1 is not a quoted constant."
               qval const)))
    (unquote qval)))
