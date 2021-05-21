; A lightweight book about the built-in function file-write-date$
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable file-write-date$))

(in-theory (disable mv-nth)) ; so these rules fire

(defthm mv-nth-0-of-file-write-date$-type
  (or (posp (mv-nth 0 (file-write-date$ file state)))
      (null (mv-nth 0 (file-write-date$ file state))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable file-write-date$))))
