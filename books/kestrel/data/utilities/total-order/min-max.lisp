; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/defrule" :dir :system)

(include-book "max-defs")
(include-book "min-defs")
(include-book "total-order-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "min"))
(local (include-book "max"))
(local (include-book "total-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled min-<<-distributes-over-max-<<
  (equal (min-<< x (max-<< y z))
         (max-<< (min-<< x y)
                 (min-<< x z)))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (min-<<
           max-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule max-<<-distributes-over-min-<<
  (equal (max-<< x (min-<< y z))
         (min-<< (max-<< x y)
                 (max-<< x z)))
  :use ((:instance acl2::<<-trichotomy
                   (acl2::x y)
                   (acl2::y x)))
  :enable (min-<<
           max-<<
           data::<<-rules)
  :disable acl2::<<-trichotomy)

(defrule min-<<-absorb-max-<<
  (equal (min-<< x (max-<< x y))
         x)
  :enable (min-<<
           max-<<))

(defrule max-<<-absorb-min-<<
  (equal (max-<< x (min-<< x y))
         x)
  :enable (min-<<
           max-<<))

(defrule <<-of-max-<<-and-min-<<
  (not (<< (max-<< x y) (min-<< x y)))
  :enable (min-<<
           max-<<
           data::<<-rules))
