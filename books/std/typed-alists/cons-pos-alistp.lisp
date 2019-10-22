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

(std::defalist cons-pos-alistp (x)
  :parents (std/typed-alists)
  :short "Recognize alists from @(tsee cons) pairs to positive integers."
  :key (consp x)
  :val (posp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  ///

  (defthm posp-of-cdr-of-assoc-equal-when-cons-pos-alistp
    (implies (cons-pos-alistp alist)
             (iff (posp (cdr (assoc-equal key alist)))
                  (assoc-equal key alist)))))
