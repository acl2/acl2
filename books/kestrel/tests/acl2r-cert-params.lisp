; A test of acl2r cert_params
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; If certparam here is replaced by cert_param, the build should break, since
;; make should detect that this book requires acl2(r) and the absence of
;; acl2(r):

; certparam: (uses-acl2r, non-acl2r)
