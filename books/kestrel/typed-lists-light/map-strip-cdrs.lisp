; Mapping strip-cdrs over a list
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alist-listp")

(defund map-strip-cdrs (alists)
  (declare (xargs :guard (alist-listp alists)))
  (if (endp alists)
      nil
    (cons (strip-cdrs (first alists))
          (map-strip-cdrs (rest alists)))))

(defthm map-strip-cdrs-of-cons
  (equal (map-strip-cdrs (cons alist alists))
         (cons (strip-cdrs alist)
               (map-strip-cdrs alists)))
  :hints (("Goal" :in-theory (enable map-strip-cdrs))))
