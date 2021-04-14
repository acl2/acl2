; A lightweight book about the built-in function min.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthmd min-when-<=-1
  (implies (and (<= x y)
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (min x y)
                  x)))

(defthmd min-when-<=-2
  (implies (<= y x)
           (equal (min x y)
                  y)))

(defthm <-of-min-arg1
  (equal (< (min x y) z)
         (or (< x z)
              (< y z))))

(defthm <-of-min-arg2
  (equal (< z (min x y))
         (and (< z x)
              (< z y))))
