; Utilities dealing with events
;
; Copyright (C) 2014-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;If POSSIBLE-PROGN is already a progn, add ITEM to the end of it.  Otherwise,
;make a progn containing POSSIBLE-PROGN, followed by ITEM.
(defun extend-progn (possible-progn item)
  (declare (xargs :guard (true-listp possible-progn)))
  (if (and (consp possible-progn)
           (eq 'progn (ffn-symb possible-progn)))
      `(progn ,@(fargs possible-progn) ,item)
    `(progn ,possible-progn ,item)))

;If POSSIBLE-PROGN is already a progn, add ITEM to the begining of it.
;Otherwise, make a progn containing POSSIBLE-PROGN, preceded by ITEM.
(defun prepend-progn (possible-progn item)
  (declare (xargs :guard (true-listp possible-progn)))
  (if (and (consp possible-progn)
           (eq 'progn (ffn-symb possible-progn)))
      `(progn ,item ,@(fargs possible-progn))
    `(progn ,item ,possible-progn)))
