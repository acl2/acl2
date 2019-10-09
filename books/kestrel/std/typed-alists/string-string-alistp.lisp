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

(std::defalist string-string-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from strings to strings."
  :key (stringp x)
  :val (stringp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  ///

  (defthm stringp-of-cdr-of-assoc-equal-when-string-string-alistp
    (implies (string-string-alistp alist)
             (iff (stringp (cdr (assoc-equal key alist)))
                  (assoc-equal key alist))))

  (defthm string-string-alistp-of-put-assoc-equal
    (implies (string-string-alistp alist)
             (equal (string-string-alistp (put-assoc-equal key val alist))
                    (and (stringp key)
                         (stringp val))))))
