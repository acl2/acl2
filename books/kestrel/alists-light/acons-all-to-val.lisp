; Setting many keys to a value in an alist
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))

(defund acons-all-to-val (keys val alist)
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (endp keys)
      alist
    (acons-all-to-val (rest keys) val (acons (first keys) val alist))))

(defthm alistp-of-acons-all-to-val
  (implies (alistp alist)
           (alistp (acons-all-to-val keys val alist)))
  :hints (("Goal" :in-theory (enable acons-all-to-val))))

(defthm strip-cars-of-acons-all-to-val
  (equal (strip-cars (acons-all-to-val keys val alist))
         (append (reverse keys)
                 (strip-cars alist)))
  :hints (("Goal" :in-theory (enable acons-all-to-val strip-cars append))))
