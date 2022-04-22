; A lightweight book about the built-in function true-list-listp
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm true-list-listp-of-append
  (equal (true-list-listp (append x y))
         (and (true-list-listp (true-list-fix x))
              (true-list-listp y))))

(defthm true-list-listp-of-true-list-fix
  (implies (true-list-listp x)
           (true-list-listp (true-list-fix x))))
