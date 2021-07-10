; R1CS package
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/prime-fields/portcullis" :dir :system)

(defpkg "R1CS"
  (append '(pfield::fep
            pfield::add
            pfield::sub
            pfield::mul
            pfield::neg
            pfield::inv
            pfield::pow
            pfield::div
            pfield::fe-listp
            lookup-equal
            lookup-eq
	    b*
            keywords-to-acl2-package
            ;; some bv concepts:
            getbit
            bvchop
            slice
            bvcat
            bitxor
            bvxor
            bitnot
            bvnot
            bvshr
            bvshl
            bvplus
            power-of-2p
            pos-fix)
          *acl2-exports*))
