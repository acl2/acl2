; Standard Basic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "std/typed-alists/string-symbollist-alistp" :dir :system)

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define organize-symbols-by-pkg ((syms symbol-listp))
  :returns (syms-by-pkg string-symbollist-alistp :hyp :guard)
  :short "Organize a list of symbols by their packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is an alist from package names (strings)
     to the non-empty lists of the symbols
     that are in the respective packages.")
   (xdoc::p
    "The alist has unique keys,
     and each of its values has no duplicates."))
  (organize-symbols-by-pkg-aux syms nil)

  :prepwork
  ((define organize-symbols-by-pkg-aux ((syms symbol-listp)
                                        (acc string-symbollist-alistp))
     :returns (syms-by-pkg string-symbollist-alistp :hyp :guard)
     :parents nil
     (b* (((when (endp syms)) acc)
          (sym (car syms))
          (pkg (symbol-package-name sym))
          (prev-syms-for-pkg (cdr (assoc-equal pkg acc))))
       (organize-symbols-by-pkg-aux (cdr syms)
                                    (put-assoc-equal
                                     pkg
                                     (add-to-set-eq sym prev-syms-for-pkg)
                                     acc))))))
