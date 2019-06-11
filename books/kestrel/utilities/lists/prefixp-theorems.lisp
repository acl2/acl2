; List Utilities -- Theorems about PREFIXP
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/lists/prefixp" :dir :system)
(include-book "std/lists/rcons" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection prefixp-theorems
  :parents (list-utilities prefixp)
  :short "Some theorems about the library function @(tsee prefixp)."

  (defrule same-car-when-prefixp-and-consp
    (implies (and (prefixp x y)
                  (consp x))
             (equal (car x)
                    (car y)))
    :rule-classes nil)

  (defrule same-take-when-prefixp-and-longer
    (implies (and (prefixp x y)
                  (>= (len x) (nfix n)))
             (equal (take n x)
                    (take n y)))
    :rule-classes nil
    :enable take)

  (defrule prefixp-of-cdr-cdr
    (implies (and (prefixp x y)
                  (consp x))
             (prefixp (cdr x) (cdr y))))

  (defrule prefixp-of-rcons
    (equal (prefixp x (rcons a y))
           (or (list-equiv x (rcons a y))
               (prefixp x y)))
    :enable (prefixp rcons))

  (defrule prefixp-of-butlast-1-right
    (equal (prefixp x (butlast y 1))
           (and (prefixp x y)
                (or (not (consp y))
                    (not (list-equiv x y)))))
    :enable prefixp))
