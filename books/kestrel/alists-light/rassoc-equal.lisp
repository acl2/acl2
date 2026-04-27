; A lightweight book about the built-in function rassoc-equal
;
; Copyright (C) 2022-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable rassoc-equal))

(defthm consp-of-rassoc-equal
  (implies (alistp alist)
           (iff (consp (rassoc-equal x alist))
                (rassoc-equal x alist)))
  :hints (("Goal" :in-theory (enable rassoc-equal))))

(defthm rassoc-equal-of-nil
  (equal (rassoc-equal x nil)
         nil)
  :hints (("Goal" :in-theory (enable rassoc-equal))))
