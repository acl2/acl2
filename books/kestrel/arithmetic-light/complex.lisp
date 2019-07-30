; A lightweight book about the built-in function complex.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Theorem complex-opener below may not hold in ACL2(r), so for now we
;; disable certification of this book in ACL2(r):
; cert_param: (non-acl2r)

(defthm complex-opener
  (equal (complex x y)
         (+ (rfix x) (* #C(0 1) (rfix y))))
  :hints (("Goal" :use (:instance complex-definition
                                  (x (rfix x))
                                  (y (rfix y))))))
