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

(std::defalist symbol-symbol-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from symbols to symbols."
  :key (symbolp x)
  :val (symbolp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil t
  ///

  (defthmd symbol-listp-of-strip-cdrs-when-symbol-symbol-alistp
    (implies (symbol-symbol-alistp x)
             (symbol-listp (strip-cdrs x))))

  (defthmd symbol-alistp-when-symbol-symbol-alistp
    (implies (symbol-symbol-alistp x)
             (symbol-alistp x))))
