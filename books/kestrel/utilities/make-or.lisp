; A utility to make an untranslated disjunction
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also make-or-nice.lisp

;; Create an untranslated term representing the disjunction of the ITEMS.
;; Special handling for 0 items and for 1 item.
(defund make-or (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      nil
    (if (endp (cdr items))
        (car items)
      `(or ,@items))))
