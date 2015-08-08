(in-package "ACL2")

(defun seq-macro (st pairs)
  (if (endp pairs)
      st
    (list 's
	  (car pairs)
	  (cadr pairs)
	  (if (endp (cddr pairs))
	      st
	    (seq-macro st (cddr pairs))))))

(defmacro seq (st &rest pairs)
  (seq-macro st pairs))

(defmacro <- (x a) `(g ,a ,x))

(defmacro -> (x a v) `(s ,a ,v ,x))
