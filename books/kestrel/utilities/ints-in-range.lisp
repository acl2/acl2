; Make a list of consecutive integers
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Make tail-rec?
(defun ints-in-range (startnum endnum)
  (declare (xargs :measure (nfix (+ 1 (- endnum startnum)))))
  (if (or (not (natp startnum))
          (not (natp endnum))
          (< endnum startnum))
      nil
    (cons startnum
          (ints-in-range (+ 1 startnum)
                         endnum))))
