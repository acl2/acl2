(in-package "ACL2")

; Sticky disabling and enabling, implementing an idea suggested by Ray
; Richards by using tables.

; Matt Kaufmann
; 12/13/05

; This book introduces the following macros:

; (sticky-disable name1 name2 ...):
; Disables the indicated names, and makes a note that they are to be
; disabled after any call of sticky-include-book.

; (sticky-enable name1 name2 ...):
; Enables the indicated names, and makes a note that they are to be
; enabled after any call of sticky-include-book.

; (sticky-include-book "book-name" ...):
; Exactly the same as include-book, except for the extra disabling and enabling
; noted above.

(program)

(defmacro add-sticky (fn &optional (disablep 't))
  (declare (xargs :guard (symbolp fn)))
  `(table sticky-disables
          nil
          (put-assoc-eq ',fn ,disablep (table-alist 'sticky-disables world))
          :clear))

(defun list-of-add-sticky-calls (fns flg)
  (if (endp fns)
      nil
    (cons `(add-sticky ,(car fns) ,flg)
          (list-of-add-sticky-calls (cdr fns) flg))))

(defmacro sticky-disable (&rest fns)
  `(progn (in-theory (disable ,@fns))
          ,@(list-of-add-sticky-calls fns t)))

(defmacro sticky-enable (&rest fns)
  `(progn (in-theory (enable ,@fns))
          ,@(list-of-add-sticky-calls fns nil)))

(defun get-sticky-enables-1 (alist acc)
  (cond ((endp alist) acc)
        ((cdar alist)
         (get-sticky-enables-1 (cdr alist) acc))
        (t (get-sticky-enables-1 (cdr alist) (cons (caar alist) acc)))))

(defun get-sticky-disables-1 (alist acc)
  (cond ((endp alist) acc)
        ((cdar alist)
         (get-sticky-disables-1 (cdr alist) (cons (caar alist) acc)))
        (t (get-sticky-disables-1 (cdr alist) acc))))

(defun get-sticky-enables (world)
  (get-sticky-enables-1 (table-alist 'sticky-disables world) nil))

(defun get-sticky-disables (world)
  (get-sticky-disables-1 (table-alist 'sticky-disables world) nil))

(defmacro sticky-include-book (&rest args)
  `(progn (include-book ,@args)
          (in-theory (set-difference-theories
                      (union-theories (current-theory :here)
                                      (get-sticky-enables world))
                      (get-sticky-disables world)))))

