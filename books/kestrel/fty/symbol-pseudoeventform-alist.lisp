; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-event-form-list")

(include-book "std/typed-alists/symbol-pseudoeventform-alistp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist symbol-pseudoeventform-alist
  :short "Fixtype of alists from symbols to pseudo event forms."
  :key-type symbol
  :val-type pseudo-event-form
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  :pred symbol-pseudoeventform-alistp)
