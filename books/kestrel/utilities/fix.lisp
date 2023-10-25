; A lightweight book about the built-in function fix
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthmd fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x)))

(defthmd fix-when-integerp
  (implies (integerp x)
           (equal (fix x)
                  x)))
