; Getting the first character of a string
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/coerce" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(defund strcar (str)
  (declare (xargs :guard (and (stringp str)
                              (not (equal "" str)))))
  (char str 0))

(defthm characterp-of-strcar
  (implies (and (stringp str)
                (not (equal "" str)))
           (characterp (strcar str)))
  :hints (("Goal" :in-theory (enable strcar))))
