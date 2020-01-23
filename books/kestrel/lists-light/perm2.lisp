; Theorems about perm and other non-built-in functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "perm")
(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defthm perm-of-reverse-list
  (perm (reverse-list x)
        x)
  :hints (("Goal" :in-theory (enable reverse-list))))
