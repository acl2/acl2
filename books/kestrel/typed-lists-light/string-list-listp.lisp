; Recognize a true list of string-lists
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund string-list-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (string-listp (first x))
           (string-list-listp (rest x)))
    (null x)))

(defthm string-list-listp-forward-to-true-listp
  (implies (string-list-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable string-list-listp))))

(defthm string-list-listp-of-cdr
  (implies (string-list-listp x)
           (string-list-listp (cdr x)))
  :hints (("Goal" :in-theory (enable string-list-listp))))

;; maybe disable or add a cheap version
(defthm string-listp-of-car-when-string-listp
  (implies (string-list-listp x)
           (string-listp (car x)))
  :hints (("Goal" :in-theory (enable string-list-listp))))
