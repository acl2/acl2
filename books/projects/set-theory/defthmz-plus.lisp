; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The macro, table-redo, is useful for creating a redundant table event that
; becomes non-redundant during the second pass of an encapsulate.

; With-props takes advantage of table-redo to introduce the necessary props,
; avoiding the need to include irrelevant definitions in the desired final
; result(s).

; Defthmz+ provides a pleasing interface to with-props.

(in-package "ZF")

(defun table-redo-fn (table-name key)
  (declare (xargs :guard t))
  `(make-event
    (let ((name ',table-name)
          (key ,key))
      (let ((val (cdr (assoc-eq key (table-alist name (w state))))))
        (list 'table name (kwote key) (kwote val))))))

(defmacro table-redo (table-name key)
  (table-redo-fn table-name key))

(defun with-props-sigs (props)
  (declare (xargs :guard (true-listp props)))
  (cond ((endp props) nil)
        (t (cons `((,(car props)) => *)
                 (with-props-sigs (cdr props))))))

(defun with-props-table-redos (props)
  (declare (xargs :guard (true-listp props)))
  (cond ((endp props) nil)
        (t (cons `(table-redo zfc-table ',(car props))
                 (with-props-table-redos (cdr props))))))

(defun with-props-fn (props locals rest)
  `(encapsulate ,(with-props-sigs props)
     ,@locals
     ,@(with-props-table-redos props)
     ,@rest))

(defmacro with-props (props locals &rest rest)
  (with-props-fn props locals rest))

(defun undefined-fns (props wrld)
  (declare (xargs :guard (and (symbol-listp props)
                              (plist-worldp wrld))))
  (cond ((endp props) nil)
        ((function-symbolp (car props) wrld)
         (undefined-fns (cdr props) wrld))
        (t (cons (car props)
                 (undefined-fns (cdr props) wrld)))))

(defun defthmz+-fn (name term events props rest)
  (declare (xargs :guard (and (true-listp events)
                              (symbol-listp props))))
  `(make-event
    (list* 'with-props
           (undefined-fns ',props (w state))
           (pairlis-x1 'local (pairlis-x2 ',events nil))
           '((defthmz ,name ,term
               ,@(and props (list :props props))
               ,@rest)))))

(defmacro defthmz+ (name term &rest args &key locals props
                         &allow-other-keys)
  (declare (xargs :guard (and (true-listp locals)
                              (symbol-listp props))))
  (defthmz+-fn name term locals props
    (acl2::strip-keyword-list '(:locals :props) args)))
