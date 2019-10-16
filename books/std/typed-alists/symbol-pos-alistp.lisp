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

(std::defalist symbol-pos-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from symbols to positive integers."
  :key (symbolp x)
  :val (posp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defthm posp-of-cdr-of-assoc-equal-when-symbol-pos-alistp
    (implies (symbol-pos-alistp alist)
             (iff (posp (cdr (assoc-equal key alist)))
                  (assoc-equal key alist)))))
