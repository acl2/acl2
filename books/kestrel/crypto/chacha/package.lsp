; CHACHA package
;
; Copyright (C) 2019-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defpkg "CHACHA"
  (append '(bvplus
            bvxor
            slice
            leftrotate
            unsigned-byte-listp
            unpackbv-little
            packbv-little
            map-packbv-little
            map-unpackbv-little
            group
            ungroup
            bvplus-list
            bvxor-list
            firstn
            subrange)
          (set-difference-eq
            *acl2-exports*
            ;; exclude state because chacha has its own notion of state:
            '(state))))
