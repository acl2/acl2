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

(std::defalist symbol-symbollist-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from symbols to true lists of symbols."
  :key (symbolp x)
  :val (symbol-listp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil t
  ///

  (defthm symbol-listp-of-cdr-of-assoc-equal-when-symbol-symbollist-alistp
    (implies (symbol-symbollist-alistp alist)
             (symbol-listp (cdr (assoc-equal key alist)))))

  (defthm symbol-symbollist-alistp-of-put-assoc-equal
    (implies (symbol-symbollist-alistp alist)
             (equal (symbol-symbollist-alistp (put-assoc-equal key val alist))
                    (and (symbolp key)
                         (symbol-listp val))))))
