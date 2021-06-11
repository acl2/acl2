; BV Library: leftrotate for size 64
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "leftrotate")

(defund leftrotate64 (amt val)
  (declare (type integer amt val))
  (leftrotate 64 amt val))

(defthmd leftrotate-becomes-leftrotate64
  (equal (leftrotate 64 amt val)
         (leftrotate64 amt val))
  :hints (("Goal" :in-theory (enable leftrotate64))))

(theory-invariant (incompatible (:rewrite leftrotate-becomes-leftrotate64) (:definition leftrotate64)))
