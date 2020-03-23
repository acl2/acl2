; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defalist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist keyword-truelist-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from keywords to true lists."
  :key (keywordp x)
  :val (true-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  ///

  (defthm true-listp-of-cdr-of-assoc-equal-when-keyword-truelist-alistp
    (implies (keyword-truelist-alistp alist)
             (true-listp (cdr (assoc-equal key alist))))))
