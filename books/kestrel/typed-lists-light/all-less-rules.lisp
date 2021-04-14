; Theorems about all-< and other non-built-in functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-less")
(include-book "kestrel/lists-light/repeat" :dir :system)

(defthm all-<-of-repeat
  (implies (< x bound)
           (all-< (repeat n x) bound))
  :hints (("Goal" :in-theory (enable nat-listp repeat))))
