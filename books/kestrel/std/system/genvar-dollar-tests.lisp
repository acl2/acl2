; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "genvar-dollar")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (genvar (pkg-witness "ACL2")
                      "VAR"
                      nil
                      nil)
              'var)

(assert-equal (genvar (pkg-witness "ACL2")
                      "VAR"
                      nil
                      '(var))
              'var0)

(assert-equal (genvar (pkg-witness "ACL2-USER")
                      "XYZ"
                      17
                      '(var))
              'acl2-user::xyz17)

(assert-equal (genvar (pkg-witness "ACL2-USER")
                      "XYZ"
                      17
                      '(acl2-user::xyz17
                        acl2-user::xyz18))
              'acl2-user::xyz19)
