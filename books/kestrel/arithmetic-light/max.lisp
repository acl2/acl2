; A lightweight book about the built-in function max.
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

(defthmd max-when-<=-1
  (implies (<= x y)
           (equal (max x y)
                  y)))

(defthmd max-when-<=-2
  (implies (and (<= y x)
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (max x y)
                  x)))

(defthm <-of-max-arg1
  (equal (< (max x y) z)
         (and (< x z)
              (< y z))))

(defthm <-of-max-arg2
  (equal (< z (max x y))
         (or (< z x)
             (< z y))))
