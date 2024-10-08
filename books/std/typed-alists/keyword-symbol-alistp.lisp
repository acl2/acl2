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

(std::defalist keyword-symbol-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from keywords to symbols."
  :key (keywordp x)
  :val (symbolp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  ///

  (defthmd alistp-when-keyword-symbol-alistp-rewrite
    (implies (keyword-symbol-alistp x)
             (alistp x))))
