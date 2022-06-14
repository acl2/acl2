; Standard Typed Alists Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defalist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist string-stringlist-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from strings to true lists of strings."
  :key (stringp x)
  :val (string-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  ///

  (defthm string-listp-of-cdr-of-assoc-equal-when-string-string/s-alistp
    (implies (string-stringlist-alistp x)
             (string-listp (cdr (assoc-equal k x))))))
