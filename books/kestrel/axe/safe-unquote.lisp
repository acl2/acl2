; Utilities to unquote, after checking that things are quoted
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

;fixme add a way to turn this off for faster performance (maybe a macro)
(defun safe-unquote (x)
  (declare (xargs :guard t))
  (if (and (consp x)
           (eq 'quote (car x))
           (consp (cdr x)))
      (unquote x)
    (hard-error 'safe-unquote
                "Attempt to unquote the ill-formed thing ~X01 (we expected a quoted constant)."
                (acons #\0 x (acons #\1 nil nil)))))

;this one takes a tag for debugging
(defun safe-unquote2 (tag x)
  (declare (xargs :guard t))
  (if (and (consp x)
           (eq 'quote (car x))
           (consp (cdr x)))
      (unquote x)
    (hard-error 'safe-unquote2
                "Error in ~x2. Attempt to unquote the ill-formed thing ~X01 (we expected a quoted constant)."
                (acons #\0 x (acons #\1 nil (acons #\2 tag nil))))))
