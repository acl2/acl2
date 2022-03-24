; A little-endian version of packbv
;
; Copyright (C) 2021-2022 Kestrel Institute
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
  (declare (type (integer 0 *) itemsize)
           (type (integer 0 *) itemcount)
           (xargs :guard (and (true-listp items)
                              (all-integerp items))))
  (packbv itemcount itemsize (reverse-list items)))
