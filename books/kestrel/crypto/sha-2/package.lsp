; SHA2 package
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defpkg "SHA2"
  (append '(packbv
            map-packbv
            unpackbv
            group
            repeat
            bvchop
            slice
            rightrotate32
            rightrotate64
            bvxor
            bvand
            bvnot
            bvplus
            acl2::shr
            and32
            xor32
            not32
            plus32
            and64
            xor64
            not64
            plus64
            bv-array-read
            bv-array-write
            bv-arrayp
            append-arrays
            firstn
            all-unsigned-byte-p
            all-integerp
            bytes-to-bits
            pad-to-448
            pad-to-896
            defopeners)
          *acl2-exports*))
