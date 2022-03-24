; BV Lists Library: theorems about packbv-little and unpackbv-little
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv-little")
(include-book "unpackbv-little")
(include-book "bvchop-list")
(local (include-book "packbv-and-unpackbv"))
(local (include-book "../lists-light/reverse-list"))

(defthm packbv-little-of-unpackbv-little
  (implies (and (posp size)
                (natp num))
           (equal (packbv-little num size (unpackbv-little num size bv))
                  (bvchop (* size num) bv)))
  :hints (("Goal" :in-theory (enable packbv-little unpackbv-little))))

(defthm unpackbv-little-of-packbv-little
  (implies (and (posp size)
                (natp num)
                (equal num (len items)) ;gen?
                )
           (equal (unpackbv-little num size (packbv-little num size items))
                  (bvchop-list size (take num items))))
  :hints (("Goal" :in-theory (enable packbv-little unpackbv-little))))
