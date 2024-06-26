; A lightweight book about the built-in function logic-fnsp
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable logic-fnsp))

(defthm logic-fnsp-of-cons
  (equal (logic-fnsp (cons a x) wrld)
         (cond ((equal a 'quote) t)
               ((flambdap a)
                (and (logic-fnsp (lambda-body a) wrld)
                     (logic-fns-listp x wrld)))
               (t (and (not (programp a wrld))
                       (logic-fns-listp x wrld)))))
  :hints (("Goal" :in-theory (enable logic-fnsp))))
