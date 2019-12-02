; Utilities for error (erp) values.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The forms in this book are more readable than simply using t and nil.

;; An erp value of t (indicates an error).  Consider instead using some more
;; informative non-nil value.
(defmacro erp-t () t)

;; An erp value of nil (indicates no error).
(defmacro erp-nil () nil)
