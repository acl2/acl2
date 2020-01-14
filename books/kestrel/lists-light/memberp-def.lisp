; A boolean-valued membership check.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Test whether A is a member of X.  Like member-equal but returns a boolean.
(defund memberp (a x)
  (declare (xargs :guard t))
  (if (not (consp x))
      nil
    (or (equal a (car x))
        (memberp a (cdr x)))))
