; List Utilities -- Theorems about NTHCDR
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/lists/equiv" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nthcdr-theorems
  :parents (list-utilities nthcdr)
  :short "Some theorems about the built-in function @(tsee nthcdr)."
  :long
  (xdoc::topstring-p
   "The theorems @('nthcdr-of-append-when-leq-len-first')
    and @('nthcdr-of-append-when-gt-len-first') are disabled by default.
    They are special cases of @('nthcdr-of-append'),
    which is enabled by default and is perhaps more useful in general.")

  (defruled nthcdr-of-append-when-leq-len-first
    (implies (<= n (len a))
             (equal (nthcdr n (append a b))
                    (append (nthcdr n a) b))))

  (defruled nthcdr-of-append-when-gt-len-first
    (implies (and (natp n)
                  (> n (len a)))
             (equal (nthcdr n (append a b))
                    (nthcdr (- n (len a)) b)))
    :use (:instance nthcdr-of-nthcdr
          (a (- n (len a)))
          (b (len a))
          (x (append a b)))
    :disable nthcdr-of-nthcdr
    :enable nthcdr-of-append-when-leq-len-first)

  (defrule nthcdr-of-append
    (implies (natp n)
             (equal (nthcdr n (append a b))
                    (if (<= n (len a))
                        (append (nthcdr n a) b)
                      (nthcdr (- n (len a)) b))))
    :enable (nthcdr-of-append-when-leq-len-first
             nthcdr-of-append-when-gt-len-first))

  (defrule nthcdr-when-len
    (implies (equal n (len x))
             (list-equiv (nthcdr n x)
                         nil))))
