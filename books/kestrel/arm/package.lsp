; The ARM package
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We can rename this if someone else is using the ARM package.  Perhaps we
;; should rename this to ARM32 anyway.

(defpkg "ARM"
  (append '(bvnot bvor bvand bvxor slice getbit bvchop bvplus bvminus bvcat bvsx bvcount repeatbit putbit
            logext logtail
            defstobj+
            lookup-eq
            lookup-equal
            lookup-eq-safe
            array ; for defstobj ; todo: add to *acl2-exports* ?
            b*
            patbind-when
            pack-in-package
            must-be-redundant
            keyword-listp
            )
          (set-difference-eq *acl2-exports*
                             '(pc ; needed for the ARM program counter
                               read ; needed for our memory read function
                               ; ; we have our own
                               ))))
