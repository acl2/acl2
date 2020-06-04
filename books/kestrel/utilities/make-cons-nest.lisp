; A utility to make symbolic list terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun make-cons-nest (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      *nil*
    `(cons ,(car items)
           ,(make-cons-nest (cdr items)))))

(defthm pseudo-termp-of-make-cons-nest
  (implies (pseudo-term-listp items)
           (pseudo-termp (make-cons-nest items)))
  :hints (("Goal" :in-theory (enable make-cons-nest))))
