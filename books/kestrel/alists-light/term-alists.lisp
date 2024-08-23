; Alists that map keys (of some type) to terms
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "map-lookup-equal")

(defthm pseudo-termp-of-lookup-equal
  (implies (pseudo-term-listp (strip-cdrs alist))
           (pseudo-termp (lookup-equal var alist)))
  :hints (("Goal" :in-theory (enable lookup-equal strip-cdrs))))

(defthm pseudo-term-listp-of-map-lookup-equal
  (implies (pseudo-term-listp (strip-cdrs alist))
           (pseudo-term-listp (map-lookup-equal vars alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal strip-cdrs))))
