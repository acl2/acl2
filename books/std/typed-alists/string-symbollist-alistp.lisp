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

(std::defalist string-symbollist-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from strings to true lists of symbols."
  :key (stringp x)
  :val (symbol-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t
  ///

  (defthm symbol-listp-of-cdr-of-assoc-equal-when-string-symbollist-alistp
    (implies (string-symbollist-alistp alist)
             (symbol-listp (cdr (assoc-equal key alist)))))

  (defthm string-symbollist-alistp-of-put-assoc-equal
    (implies (string-symbollist-alistp alist)
             (equal (string-symbollist-alistp (put-assoc-equal key val alist))
                    (and (stringp key)
                         (symbol-listp val))))))
