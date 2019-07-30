; BV Lists Library: theorems about packbv and unpackbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv")
(include-book "unpackbv")
(include-book "bvchop-list")
(local (include-book "../arithmetic-light/times"))

(defthm packbv-of-unpackbv
  (implies (and (posp size)
                (natp num))
           (equal (packbv num size (unpackbv num size bv))
                  (bvchop (* size num) bv)))
  :hints (("Goal" :in-theory (enable packbv unpackbv))))

(defthm unpackbv-of-packbv
  (implies (and (posp size)
                (natp num))
           (equal (unpackbv num size (packbv num size items))
                  (bvchop-list size (take num items))))
  :hints (("Goal" :in-theory (enable packbv unpackbv))))
