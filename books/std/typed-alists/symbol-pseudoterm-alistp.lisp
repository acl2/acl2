; Standard Typed Alists Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defalist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist symbol-pseudoterm-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from symbols to pseudo-terms."
  :key (symbolp x)
  :val (pseudo-termp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil t
  ///

  (defthmd symbol-pseudoterm-alistp-alt-def
    (equal (symbol-pseudoterm-alistp alist)
           (and (symbol-alistp alist)
                (pseudo-term-listp (strip-cdrs alist)))))

  (defthmd symbol-pseudoterm-alistp-of-pairlis$
    (implies (and (symbol-listp keys)
                  (pseudo-term-listp vals))
             (symbol-pseudoterm-alistp (pairlis$ keys vals))))

  (defthmd pseudo-term-listp-of-strip-cdrs-when-symbol-pseudoterm-alistp
    (implies (symbol-pseudoterm-alistp alist)
             (pseudo-term-listp (strip-cdrs alist)))))
