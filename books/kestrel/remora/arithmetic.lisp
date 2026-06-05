; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ arithmetic
  :parents (library-extensions)
  :short "Library extensions for arithmetic."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled lt-to-zero-when-divided-by-pos
  :short "If a positive integer divides a natural number,
          the latter is less than the former iff it is 0."
  (implies (and (natp x)
                (posp y)
                (integerp (/ x y)))
           (equal (< x y)
                  (equal x 0)))
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pos-gte-pos-divisor
  :short "If a positive integer divides a positive integer,
          the former is not larger than the latter."
  (implies (and (posp x)
                (posp y)
                (integerp (/ x y)))
           (<= y x))
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))
