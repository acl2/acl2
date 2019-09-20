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

(std::defalist symbol-string-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from symbols to strings."
  :key (symbolp  x)
  :val (stringp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defthm stringp-of-cdr-of-assoc-equal-when-symbol-string-alistp
    (implies (symbol-string-alistp alist)
             (iff (stringp (cdr (assoc-equal key alist)))
                  (assoc-equal key alist)))))
