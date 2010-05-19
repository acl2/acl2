#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "records")
(include-book "../symbol-fns/symbol-fns")

(defmacro defarray (&key (name 'nil) (type 'nil) (size 'nil))

  (declare (ignore size type))
  
  (let ((name-p   (symbol-fns::suffix name '-p))
	(get-name (symbol-fns::prefix 'get- name))
	(set-name (symbol-fns::prefix 'set- name))
	(new-name (symbol-fns::prefix 'new- name)))
    
    `(encapsulate
      ()
      
      (defun ,name-p (x)
	(wfr x))
      
      (defun ,get-name (a x)
	(g a x))
      
      (defun ,set-name (a v x)
	(s a v x))
      
      (defun ,new-name ()
	nil)
      
      )
    
    ))

;; Additional vfaat support

(defmacro integer-list-p (x)
  `(integer-listp ,x))

(defun index_list_rec (base off size)
  (if (zp size) nil
    (cons (ifix (+ base off))
	  (index_list_rec base (1+ off) (1- size)))))

(defthm integer-list-p-index_list_rec
  (integer-list-p (index_list_rec base off size))
  :hints (("goal" :in-theory (enable integer-listp))))

(defun index_list (base size)
  (index_list_rec base 0 size))

(defthm integer-list-p-index_list
  (integer-list-p (index_list base size)))

(defun default-integer-list-list () nil)

(defun integer-list-list-p (list)
  (declare (type t list))
  (if (consp list)
      (and (integer-listp (car list))
	   (integer-list-list-p (cdr list)))
    (null list)))

(in-theory (disable index_list))
