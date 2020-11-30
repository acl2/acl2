; A function to extract a contiguous segment of a list.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also subseq-list, which is similar but not quite the same.

;; Return a list of the elements of LST from START (inclusive) to END
;; (inclusive), where the numbering is 0-based.
(defund subrange (start end lst)
  (declare (type (integer 0 *) start)
           (type (integer 0 *) end)
           (xargs :guard (true-listp lst)))
  (nthcdr start (take (+ 1 end) lst)))
