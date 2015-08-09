
;; Some general purpose string and symbol manipulation functions.

(in-package "ACL2")

(defun concat-str-macro (lst)
  (if (consp lst)
      (if (consp (cdr lst))
	  (cons 'concatenate
		(cons ''string (cons (car lst)
				     (cons (concat-str-macro (cdr lst))
					   'nil))))
	(car lst))
    nil))

(defmacro concat-str (&rest args)
  (concat-str-macro args))

(defun symbol-from-sym-str (sym str)
  (intern (concat-str (string sym)
                      str)
          "ACL2"))

(defun symbol-from-str-num (str n)
  (intern (concat-str str (coerce (explode-atom n 10) 'string))
          "ACL2"))

