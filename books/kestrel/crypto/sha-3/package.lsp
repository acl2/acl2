; SHA3 package
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defpkg "SHA3"
  (append '(all-unsigned-byte-p
            all-integerp
            all-true-listp
            repeat
            items-have-len
            group
            ungroup
            bitxor
            bitxor$
            bitand
            bitand$
            lg
            bvxor-list
            memberp
            assert-equal ; for testing
            hex-string-to-bytes! ; for testing
            )
          *acl2-exports*))
