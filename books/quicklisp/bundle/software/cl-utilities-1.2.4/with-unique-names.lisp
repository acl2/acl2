(in-package :cl-utilities)

;; Defined at http://www.cliki.net/WITH-UNIQUE-NAMES

(defmacro with-unique-names ((&rest bindings) &body body)
  "Executes a series of forms with each var bound to a fresh,
uninterned symbol. See http://www.cliki.net/WITH-UNIQUE-NAMES"
  `(let ,(mapcar #'(lambda (binding)
                     (multiple-value-bind (var prefix)
			 (%with-unique-names-binding-parts binding)
		       (check-type var symbol)
		       `(,var (gensym ,(format nil "~A"
					       (or prefix var))))))
                 bindings)
    ,@body))

(defun %with-unique-names-binding-parts (binding)
  "Return (values var prefix) from a WITH-UNIQUE-NAMES binding
form. If PREFIX is not given in the binding, NIL is returned to
indicate that the default should be used."
  (if (consp binding)
      (values (first binding) (second binding))
      (values binding nil)))

(define-condition list-binding-not-supported (warning)
  ((binding :initarg :binding :reader list-binding-not-supported-binding))
  (:report (lambda (condition stream)
	     (format stream "List binding ~S not supported by WITH-GENSYMS.
It will work, but you should use WITH-UNIQUE-NAMES instead."
		     (list-binding-not-supported-binding condition))))
  (:documentation "List bindings aren't supported by WITH-GENSYMS, and
if you want to use them you should use WITH-UNIQUE-NAMES instead. That
said, they will work; they'll just signal this warning to complain
about it."))


(defmacro with-gensyms ((&rest bindings) &body body)
  "Synonym for WITH-UNIQUE-NAMES, but BINDINGS should only consist of
atoms; lists are not supported. If you try to give list bindings, a
LIST-BINDING-NOT-SUPPORTED warning will be signalled, but it will work
the same way as WITH-UNIQUE-NAMES. Don't do it, though."
  ;; Signal a warning for each list binding, if there are any
  (dolist (binding (remove-if-not #'listp bindings))
    (warn 'list-binding-not-supported :binding binding))
  ;; Otherwise, this is a synonym for WITH-UNIQUE-NAMES
  `(with-unique-names ,bindings ,@body))