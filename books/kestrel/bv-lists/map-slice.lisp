; BV Lists Library: map-slice
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/slice" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/sequences/defmap" :dir :system)

(defmap map-slice (high low x) (slice high low x) :fixed (high low) :declares ((xargs :guard (and (natp low) (integerp high) (<= low high) (all-integerp x)))))
