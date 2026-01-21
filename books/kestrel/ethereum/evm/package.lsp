; The EVM package
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "EVM" (append '(repeat strip-cadrs
                        assert-equal
                        ;; BV library functions:
                        logext
                        bvchop
                        getbit
                        bvplus
                        bvminus
                        bvmult
                        bvdiv
                        bvmod
                        sbvdiv
                        bvnot
                        bvand
                        bvor
                        bvxor
                        bvcat
                        bitnot
                        bitand
                        bitor
                        bitxor
                        bvlt
                        bvle
                        bvgt
                        bvge
                        sbvlt
                        sbvle
                        sbvgt
                        sbvge
                        bvsx
                        bv-to-sint
                        sint-to-bv
                        packbv
                        unpackbv
                        bool-to-bit
                        defforall-simple
                        defaggregate)
                      *acl2-exports*))
