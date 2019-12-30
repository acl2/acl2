; A utility to make a, possibly simplified, untranslated disjunction
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "remove-duplicates-equal-dollar")

;; Make an untranslated term representing the disjunction of the ITEMS.  Makes
;; an OR unless there are 0 or 1 items.  The items need not be translated.
(defund make-or-nice (items)
  (declare (xargs :guard (true-listp items)))
  (let* ((items (remove-equal nil items))   ;remove nil
         (items (remove-equal *nil* items)) ;remove 'nil
         ;; we could make removing dups like this an option:
         (items (remove-duplicates-equal$ items)) ;keep the first member of each set of duplicates
         )
    (if (endp items)
        nil ;no need to quote this, as we are returning an untranslated term
      (if (endp (rest items))
          (first items)
        `(or ,@items)))))
