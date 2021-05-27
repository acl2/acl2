; Keep only atoms (e.g., nodenums) in a list
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

;; Keep the nodenums from a list of nodenums and quoteps
(defund keep-atoms (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      nil
    (let ((item (first items)))
      (if (atom item)
          (cons item (keep-atoms (cdr items)))
        (keep-atoms (cdr items))))))
