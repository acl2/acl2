; Keccak Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "KECCAK"
  (append '(
            all-integerp
            all-unsigned-byte-p
            assert-equal
            b*
            bit-listp
            bits-to-bytes-little
            bitxor
            bvand
            bvnot
            bvxor
            bytes-to-bits-little
            chars=>nats
            define
            defxdoc
	    defmap-simple
            firstn
            flatten
            getbit
            group
            leftrotate
            len-mult-of-8p
            map-hexstring-to-num
            packbv
            patbind-unless
            patbind-when
            repeat
            reverse-list
            putbit
            shr
            slice
            string=>nats
            two-nats-measure
            unpackbv
            )
          *acl2-exports*))
