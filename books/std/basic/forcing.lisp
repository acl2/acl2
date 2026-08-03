; Standard Basic Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wrap with FORCE every element (meant to be a term) of a list.
(defun force-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (cons `(force ,(car x))
                 (force-list (cdr x))))))

; Conjunction of FORCE-wrapped arguments (mean to be terms).
(defmacro forced-and (&rest x)
  `(and ,@(force-list x)))
