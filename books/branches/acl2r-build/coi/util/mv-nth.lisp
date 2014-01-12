#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

;; Include the following in your .emacs file to provide
;; reasonable indenting for met:
;;
;; (put 'met        'lisp-indent-hook 1)
;; (put 'acl2::met  'lisp-indent-hook 1)

;We make our own mv-nth function, so that we can disable it without getting theory warnings
;about how mv-nth cannot be completely disabled (since it is built-in in a deep way).
(defund val (n l)
  (declare (xargs :guard (and (integerp n)
                              (>= n 0)
                              (true-listp l))))
  (mv-nth n l))

(defthm mv-nth-to-val
  (equal (mv-nth n l)
         (val n l))
  :hints (("Goal" :in-theory (enable val))))

(theory-invariant (incompatible (:rewrite mv-nth-to-val)
                                (:definition val)))

(defthm val-of-cons
  (equal (val n (cons a l))
         (if (zp n)
             a
           (val (+ -1 n) l)))
  :hints (("Goal" :in-theory (e/d (val) ( mv-nth-to-val)))))

(defmacro v0 (x)
  `(val 0 ,x))

(defmacro v1 (x)
  `(val 1 ,x))

(defmacro v2 (x)
  `(val 2 ,x))

(defmacro v3 (x)
  `(val 3 ,x))

(defmacro v4 (x)
  `(val 4 ,x))

(defmacro met (binding &rest rst)
  (declare (xargs :guard (and (consp binding)
			      (consp (cdr binding))
			      (null  (cddr binding)))))
  `(mv-let ,(car binding) ,(cadr binding)
	   ,@rst))

;;
;; met* is useful in formulating rewrite rules involving functions
;; returning multiple values.
;;
(defun val-map (n binding var)
  (declare (type integer n))
  (if (consp binding)
      (cons `(,(car binding) (val ,n ,var))
	    (val-map (1+ n) (cdr binding) var))
    nil))

(defmacro met* (binding &rest rst)
  `(let ((val ,(cadr binding)))
     (let (,@(val-map 0 (car binding) 'val))
       ,@rst)))

;; Faux multi-vlaued functions
;; ---------------------------

;; The macro mvlist can be used in conjunction with metlist in place
;; of mv in conjunction with mv-let/met to return and bind multiple
;; values.

(defun metlist-fn (n vars)
  (if (consp vars)
      (cons `(,(car vars) (val ,n gensym::metlist))
	    (metlist-fn (1+ n) (cdr vars)))
    nil))

(defmacro metlist (binding &rest body)
  `(let ((gensym::metlist ,(cadr binding)))
     (let ,(metlist-fn 0 (car binding))
       ,@body)))

(defmacro mvlist (&rest args)
  `(list ,@args))

;; (metlist ((x y z) (foo a b c)) (mvlist x y z))


