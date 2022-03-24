; SALSA package
;
; Copyright (C) 2019-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defpkg "SALSA"
  (append '(byte-listp
            packbv-little
            unpackbv-little
            bvchop
            leftrotate
            bvxor
            bvplus
            defopeners)
          *acl2-exports*))
