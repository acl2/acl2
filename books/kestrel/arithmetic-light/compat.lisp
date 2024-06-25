; Check for conflicts with other arithmetic libraries
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "top")

;; Check for conflicts with std:
(encapsulate ()
  (local (include-book "std/basic/arith-equivs" :dir :system)))

;; Check for conflicts with arithmetic:
(encapsulate ()
  (local (include-book "arithmetic/top" :dir :system)))

;; Check for conflicts with arithmetic-2:
(encapsulate ()
  (local (include-book "arithmetic-2/meta/top" :dir :system)))

;; Check for conflicts with arithmetic-3:
(encapsulate ()
  (local (include-book "arithmetic-3/top" :dir :system)))

;; Check for conflicts with arithmetic-5:
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system)))
