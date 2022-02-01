; Utilities to print information about theorems in the world
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Conside JSON encoding the result (see books/centaur/bridge/to-json.lisp).

(include-book "world")

(defun print-rule-classes (rule-classes)
  (declare (xargs :guard (true-listp rule-classes)))
  (if (endp rule-classes)
      nil
    (let* ((rule-class (first rule-classes))
           ;; todo: consider not doing this:
           (rule-class (if (consp rule-class) (car rule-class) rule-class))
           )
      (prog2$ (cw "~x0 " rule-class)
              (print-rule-classes (rest rule-classes))))))

(defun print-defthm-info (defthm-names wrld)
  (declare (xargs :guard (and (symbol-listp defthm-names)
                              (plist-worldp wrld))))
  (if (endp defthm-names)
      nil
    (let* ((defthm-name (first defthm-names))
           (defthm-body (defthm-body defthm-name wrld))
           (rule-classes (defthm-rule-classes defthm-name wrld)))
      (progn$ (cw "Name: ~x0~%" defthm-name)
              (cw "Body: ~x0~%" defthm-body)
              (cw "Rule-classes: (" rule-classes)
              (print-rule-classes rule-classes)
              (cw ")~%~%")
              (print-defthm-info (rest defthm-names) wrld)))))

(defun print-all-theorems (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (mv-let (defun-names defthm-names)
    (defuns-and-defthms-in-world wrld nil wrld nil nil)
    (declare (ignore defun-names)) ; todo: don't compute
    (print-defthm-info defthm-names wrld)))

;; Example of how to call the tool:
;; (include-book "../arithmetic-light/top") ; a book that includes some theorems
;; (print-all-theorems (w state)) ; print all theorems in the current ACL2 session
