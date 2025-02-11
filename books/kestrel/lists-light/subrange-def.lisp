; A function to extract a contiguous segment of a list.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also subseq-list, which is similar but not quite the same.

;; Return a list of the elements of LST from START (inclusive) to END
;; (inclusive), where the numbering is 0-based.
;; TODO: Make this more efficient by doing the nthcdr first.
(defund subrange (start end lst)
  (declare (xargs :guard (and (true-listp lst)
                              (natp start)
                              (natp end)
                              ;; (< end (len lst)) ; uncomment?
                              )
                  :split-types t)
           (type (integer 0 *) start end))
  (nthcdr start (take (+ 1 end) lst)))
