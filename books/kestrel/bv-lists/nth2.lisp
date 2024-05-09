; A variant of nth
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bvchop" :dir :system)

;we go from nth to this to bvnth - do we still?
(defund nth2 (indexsize n lst)
  (DECLARE (XARGS :GUARD (AND (INTEGERP N)
                              (natp indexsize)
                              ;(>= N 0)
                              (TRUE-LISTP Lst))))
  (nth (bvchop indexsize n) lst))
