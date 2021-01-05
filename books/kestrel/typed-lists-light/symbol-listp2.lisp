; Some rules about symbol-listp
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These rules mix symbol-listp with other non-built-in functions

(include-book "symbol-listp")
(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defthm symbol-listp-of-reverse-list
  (equal (symbol-listp (acl2::reverse-list x))
         (symbol-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable acl2::reverse-list))))
