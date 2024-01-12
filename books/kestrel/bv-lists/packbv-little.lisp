; A little-endian version of packbv
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv")
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(local (include-book "kestrel/typed-lists-light/all-integerp2" :dir :system))

(defund packbv-little (itemcount itemsize items)
  (declare (xargs :guard (and (natp itemcount)
                              (natp itemsize)
                              (true-listp items)
                              (all-integerp items))
                  :split-types t)
           (type (integer 0 *) itemsize)
           (type (integer 0 *) itemcount))
  (packbv itemcount itemsize (reverse-list items)))

(defthm packbv-little-of-0-arg1
  (equal (packbv-little 0 itemsize items)
         0)
  :hints (("Goal" :in-theory (enable packbv-little))))
