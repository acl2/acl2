(in-package "ACL2")

(defun syn::alist-binding (alist1 symbol)
  (declare (type symbol symbol))
  (if (and (symbolp alist1)
	   (equal (symbol-name alist1) (symbol-name symbol))) nil
    `((,symbol . ,symbol))))

(defun mv-equality-terms (vals fname alist-1 alist args)
  (declare (type (integer 0 *) vals)
	   (type (satisfies true-listp) args))
  (if (zp vals) nil
    (let ((vals (1- vals)))
      (let ((term `(equal (list::val ,vals (,fname ,alist-1 ,@args))
			  (list::val ,vals (,fname ,alist ,@args)))))
	(cons term
	      (mv-equality-terms vals fname alist-1 alist args))))))

(defun equality-terms (vals fname alist-1 alist args)
  (declare (type (integer 0 *) vals)
	   (type (satisfies true-listp) args))
  (if (< (nfix vals) 2)
      `(equal (,fname ,alist-1 ,@args)
	      (,fname ,alist ,@args))
    `(and ,@(mv-equality-terms vals fname alist-1 alist args))))

(defmacro syn::defignorex (defun mname alist args &rest body)
  (declare (type symbol mname alist)
	   (type (satisfies symbol-listp) args))
  (let ((ignored-alist alist)
	(fname         (symbol-fns::suffix mname '-fn)))
    `(encapsulate
      ()

      (set-ignore-ok :warn)
      (set-irrelevant-formals-ok :warn)

      (defmacro ,mname (&rest args)
	(declare (xargs :guard (not (acl2::member-equal ',ignored-alist args))))
	`(,',fname ,',ignored-alist ,@args))

      (,defun ,fname ,(cons ignored-alist args)
	,@body)

      (add-macro-alias ,mname ,fname)

      )))

(defmacro syn::defignore (&rest args)
  `(syn::defignorex defun ,@args))

(defmacro syn::defignored (&rest args)
  `(syn::defignorex defund ,@args))

(defmacro syn::defirrelevant (mname vals alist args &rest hints)
  (declare (type symbol mname alist)
	   (type (integer 1 *) vals)
	   (type (satisfies symbol-listp) args)
	   (xargs :guard (not (acl2::member-equal alist args))))
  (let ((ignored-alist alist)
	(fname         (symbol-fns::suffix mname '-fn)))
    (let ((ignored-alist-1 (symbol-fns::suffix ignored-alist '_1)))

      `(defthmd ,(symbol-fns::suffix mname '-irrelevant)
	 (implies
	  (bind-free (syn::alist-binding ,ignored-alist-1 ',ignored-alist) (,ignored-alist))
	  ,(equality-terms vals fname ignored-alist-1 ignored-alist args))
	 ,@hints))))
