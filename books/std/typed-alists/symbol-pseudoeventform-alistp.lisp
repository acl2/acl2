; Standard Typed Alists Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defalist" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist symbol-pseudoeventform-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from symbols to pseudo event forms."
  :key (symbolp x)
  :val (pseudo-event-formp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defthmd symbol-pseudoeventform-alistp-alt-def
    (equal (symbol-pseudoeventform-alistp alist)
           (and (symbol-alistp alist)
                (pseudo-event-form-listp (strip-cdrs alist)))))

  (defthm symbol-pseudoeventform-alistp-of-pairlis$
    (implies (and (symbol-listp keys)
                  (pseudo-event-form-listp vals)
                  (equal (len vals) (len keys)))
             (symbol-pseudoeventform-alistp (pairlis$ keys vals))))

  (defthmd pseudo-event-form-listp-of-strip-cdrs-when-symbol-pseudoeventform-alistp
    (implies (symbol-pseudoeventform-alistp alist)
             (pseudo-event-form-listp (strip-cdrs alist))))

  (defthmd symbol-alistp-when-symbol-pseudoeventform-alistp
    (implies (symbol-pseudoeventform-alistp x)
             (symbol-alistp x))))
