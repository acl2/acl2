; A lightweight book about the built-in function true-list-listp
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that true-list-listp-forward-to-true-listp is built-in to ACL2.

(local (include-book "kestrel/lists-light/reverse" :dir :system))

;; TODO: Disable true-list-listp?

(defthm true-list-listp-of-append
  (equal (true-list-listp (append x y))
         (and (true-list-listp (true-list-fix x))
              (true-list-listp y))))

(defthm true-list-listp-of-true-list-fix
  (implies (true-list-listp x)
           (true-list-listp (true-list-fix x))))

;; Disabled since it introduces true-list-listp from nowhere.
(defthmd true-listp-of-car-when-true-list-listp
  (implies (true-list-listp x)
           (true-listp (car x))))

;; Disabled since it introduces true-list-listp from nowhere.
(defthmd true-listp-of-car-of-last-when-true-list-listp
  (implies (true-list-listp x)
           (true-listp (car (last x)))))

(defthm true-list-listp-of-reverse
  (implies (true-list-listp x)
           (true-list-listp (reverse x))))
