; Utilities for printing (e.g., for printing large lists)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;Do I still need this?

;doesn't stack overflow when printing a large list
(defun print-list-aux (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (print-list-aux (prog2$ (cw " ~y0" (car lst))
                            (cdr lst)))))

(defun print-list (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (prog2$ (cw "(~y0" (car lst)) ;print the first element separately to avoid a space before it
              (prog2$ (print-list-aux (cdr lst))
                      (cw ")")))
    (cw "nil")))

(defun print-lists (lsts)
  (declare (xargs :guard (true-listp lsts)))
  (if (endp lsts)
      nil
    (prog2$ (print-list (first lsts))
            (print-lists (rest lsts)))))

(defun print-list-on-one-line-aux (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil ;fixme print the final cdr?
    (print-list-on-one-line-aux (prog2$ (cw " ~x0" (car lst))
                            (cdr lst)))))

;doesn't stack overflow when printing a large list
;doesn't do evisceration
(defun print-list-on-one-line (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (prog2$ (cw "(~x0" (car lst)) ;print the first element separately to avoid a space before it
              (prog2$ (print-list-on-one-line-aux (cdr lst))
                      (cw ")")))
    (cw "nil") ;fixme print lst?
    ))

(defun print-each-list-on-one-line (lsts)
  (declare (xargs :guard t))
  (if (atom lsts)
      nil
    (progn$ (print-list-on-one-line (first lsts))
            (cw "~%")
            (print-each-list-on-one-line (rest lsts)))))
