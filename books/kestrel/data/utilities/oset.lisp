; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(include-book "std/osets/top" :dir :system)

(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(include-book "total-order/total-order")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable <<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled osetp-of-append
  (implies (and (setp x)
                (setp y))
           (equal (setp (append x y))
                  (or (not x)
                      (not y)
                      (<< (car (last x)) (car y)))))
  :induct t
  :enable (append
           setp))

(defruled osetp-of-cons
  (implies (setp y)
           (equal (set::setp (cons x y))
                  (or (not y)
                      (<< x (car y)))))
  :enable setp)

(defruled cardinality-becomes-len-when-osetp
  (implies (setp oset)
           (equal (cardinality oset)
                  (len oset)))
  :induct t
  :enable (cardinality
           emptyp
           tail
           setp))
