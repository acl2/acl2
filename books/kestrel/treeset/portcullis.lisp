; Copyright (C) 2025 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This must be in the portcullis to certify books with forms like:
;;   (declare (type #.*u-fixnum-type* ...))
;; and
;;   (the #.*u-fixnum-type* ...)
;; This is because the whole book is read before any parts are evaluated.
;; Note: this is the unsigned version of acl2::*fixnum-type*.
(defconst *u-fixnum-type*
  (list 'unsigned-byte
        acl2::*fixnum-bits*))
