; A little-endian version a packbv
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv")
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(local (include-book "kestrel/typed-lists-light/all-integerp2" :dir :system))

(defun packbv-little (itemcount itemsize items)
  (declare (type (integer 0 *) itemsize)
           (type (integer 0 *) itemcount)
           (xargs :guard (and (true-listp items)
                              (acl2::all-integerp items))))
  (acl2::packbv itemcount itemsize (acl2::reverse-list items)))
