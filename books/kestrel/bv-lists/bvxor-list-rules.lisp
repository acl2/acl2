; Rules about bvxor-list
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvxor-list")
(include-book "bvchop-list")

(defthm bvxor-list-of-bvxor-list-same
  (implies (equal (len x) (len y))
           (equal (bvxor-list size x (bvxor-list size x y))
                  (bvchop-list size y)))
  :hints (("Goal" :in-theory (enable bvxor-list))))
