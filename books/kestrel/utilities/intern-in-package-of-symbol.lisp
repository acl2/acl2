; A lightweight book about intern-in-package-of-symbol
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Should usually be left disabled.
(defthmd symbol-equality-strong
  (implies (or (symbolp s1)
               (symbolp s2))
           (equal (equal s1 s2)
                  (and (equal (symbol-name s1)
                              (symbol-name s2))
                       (equal (symbol-package-name s1)
                              (symbol-package-name s2)))))
  :hints (("Goal" :use (:instance symbol-equality))))

(defthm equal-of-intern-in-package-of-symbol-and-intern-in-package-of-symbol-same-arg2
  (implies (and (stringp x1)
                (stringp x2)
                (symbolp y))
           (equal (equal (intern-in-package-of-symbol x1 y)
                         (intern-in-package-of-symbol x2 y))
                  (equal x1 x2)))
  :hints (("Goal" :use (:instance symbol-equality-strong
                                  (s1 (intern-in-package-of-symbol x1 y))
                                  (s2 (intern-in-package-of-symbol x2 y))))))
