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

(define organize-symbols-by-name ((syms symbol-listp))
  :returns (syms-by-name string-symbollist-alistp :hyp :guard)
  :short "Organize a list of symbols by their names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is an alist from symbol names (strings)
     to the non-empty lists of the symbols
     that have the respective names.")
   (xdoc::p
    "The alist has unique keys,
     and each of its values has no duplicates."))
  (organize-symbols-by-name-aux syms nil)

  :prepwork
  ((define organize-symbols-by-name-aux ((syms symbol-listp)
                                         (acc string-symbollist-alistp))
     :returns (syms-by-name string-symbollist-alistp :hyp :guard)
     :parents nil
     (b* (((when (endp syms)) acc)
          (sym (car syms))
          (name (symbol-name sym))
          (prev-syms-for-name (cdr (assoc-equal name acc))))
       (organize-symbols-by-name-aux (cdr syms)
                                     (put-assoc-equal
                                      name
                                      (add-to-set-eq sym prev-syms-for-name)
                                      acc))))))
