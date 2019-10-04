; Standard Typed Alists Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
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

  (defthm pseudo-termp-of-cdr-of-assoc-equal-when-symbol-pseudoterm-alistp
    (implies (symbol-pseudoterm-alistp alist)
             (pseudo-termp (cdr (assoc-equal key alist)))))

  (defthm symbol-pseudoterm-alistp-of-put-assoc-equal
    (implies (symbol-pseudoterm-alistp alist)
             (equal (symbol-pseudoterm-alistp (put-assoc-equal key val alist))
                    (and (symbolp key)
                         (pseudo-termp val))))))
