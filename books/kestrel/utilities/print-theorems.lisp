; Utilities to print information about theorems in the world
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "world")
(include-book "centaur/bridge/to-json" :dir :system)

(defund print-rule-classes (rule-classes)
  (declare (xargs :guard (true-listp rule-classes)))
  (if (endp rule-classes)
      nil
    (let ((rule-class (first rule-classes)))
      (prog2$ (cw "~x0 " rule-class)
              (print-rule-classes (rest rule-classes))))))

(defund strip-rule-class-names (rule-classes)
  (declare (xargs :guard (true-listp rule-classes)))
  (if (endp rule-classes)
      nil
    (let ((rule-class (first rule-classes)))
      (cons (if (consp rule-class) (car rule-class) rule-class)
            (strip-rule-class-names (rest rule-classes))))))

(defund print-defthm-info (defthm-names as-jsonp wrld)
  (declare (xargs :guard (and (symbol-listp defthm-names)
                              (booleanp as-jsonp)
                              (plist-worldp wrld))))
  (if (endp defthm-names)
      nil
    (let* ((defthm-name (first defthm-names))
           (defthm-body (defthm-body defthm-name wrld))
           (rule-classes (defthm-rule-classes defthm-name wrld))
           ;; todo: consider not doing this:
           (rule-classes (strip-rule-class-names rule-classes)))
      (if as-jsonp
          ;; TODO: Print empty rule-classes as [] rather than NIL?
          (let ((form (acons :name defthm-name
                             (acons :body defthm-body
                                    (acons :rule-classes rule-classes
                                           nil)))))
            (progn$ (cw "~s0~%" (bridge::json-encode form))
                    (print-defthm-info (rest defthm-names) as-jsonp wrld)))
        (progn$ (cw "Name: ~x0~%" defthm-name)
                (cw "Body: ")
                (cw "~x0~%" defthm-body)
                (cw "Rule-classes: (")
                (print-rule-classes rule-classes)
                (cw ")~%~%")
                (print-defthm-info (rest defthm-names) as-jsonp wrld))))))

(defun print-all-theorems (as-jsonp wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (booleanp as-jsonp))))
  (mv-let (defun-names defthm-names)
    (defuns-and-defthms-in-world wrld nil wrld nil nil)
    (declare (ignore defun-names)) ; todo: don't compute
    (print-defthm-info defthm-names as-jsonp wrld)))

;; Example of how to call the tool:
;; (include-book "kestrel/utilities/print-theorems" :dir :system) ; include the tool
;; (include-book "kestrel/arithmetic-light/top" :dir :system) ; example of a book that includes some theorems
;; (print-all-theorems nil (w state)) ; print all theorems in the current ACL2 session
;; OR
;; (print-all-theorems t (w state)) ; print all theorems in the current ACL2 session, as JSON
