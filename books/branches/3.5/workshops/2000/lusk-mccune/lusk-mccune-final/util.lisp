(in-package "ACL2")

;;----------------------------------------
;; a few generic utilities

(defmacro boolp (x)
  (list 'or (list 'null x) (list 'equal x 't)))

(defmacro pos-integerp (x)
  (list 'and (list 'integerp x) (list '> x 0)))

(defmacro naturalp (x)
  (list 'and (list 'integerp x) (list '>= x 0)))

(defun natural-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	(t (and (naturalp (car x))
		(natural-listp (cdr x))))))

(defun ith (n lst)              ;; counts from 1
  (declare (xargs :guard (naturalp n)
		  :measure (acl2-count lst)))
  (cond ((atom lst) nil)
	((equal n 0) nil)
	((equal n 1) (car lst))
	(t (ith (- n 1) (cdr lst)))))

(defun update-alist-cdr (key val alist)  ;; no-op if the key is not there
  (declare (xargs :guard (alistp alist)))
  (cond ((atom alist) alist)
	((equal key (caar alist)) (cons (cons key val) (cdr alist)))
	(t (cons (car alist) (update-alist-cdr key val (cdr alist))))))

(defun update-alist-member (key mem alist)  ;; no-op if the key is not there
  (declare (xargs :guard (and (alistp alist)
			      (consp mem))))
  (cond ((atom alist) alist)
	((equal key (caar alist)) (cons mem (cdr alist)))
	(t (cons (car alist) (update-alist-member key mem (cdr alist))))))

(defmacro update-first (l x)
  (list 'cons x (list 'cdr l)))

(defmacro update-second (l x)
  (list 'cons (list 'car l) (list 'cons x (list 'cddr l))))

(defmacro update-third (l x)
  (list 'cons
	(list 'car l)
	(list 'cons (list 'cadr l) (list 'cons x (list 'cdddr l)))))

(defmacro update-fourth (l x)
  (list 'cons
	(list 'car l)
	(list 'cons
	      (list 'cadr l)
	      (list 'cons (list 'caddr l) (list 'cons x (list 'cddddr l))))))

(defmacro update-fifth (l x)
  (list 'cons
	(list 'car l)
	(list 'cons
	      (list 'cadr l)
	      (list 'cons
		    (list 'caddr l)
		    (list 'cons
			  (list 'cadddr l)
			  (list 'cons x (list 'cddddr (list 'cdr l))))))))

(defun update-ith (l i x)  ;; this counts from 1
  (declare (xargs :guard (and (true-listp l)
			      (integerp i))))
  (cond ((atom l) l)
        ((equal i 1) (cons x (cdr l)))
	(t (cons (car l) (update-ith (cdr l) (- i 1) x)))))

;;-----------------------------------

(defun max-in-natural-listp (l)
  (declare (xargs :guard (natural-listp l)))
  (cond ((atom l) -1)
	(t (max (nfix (car l)) (max-in-natural-listp (cdr l))))))

(defun gen-natural (l)
  (declare (xargs :guard (natural-listp l)))
  (+ 1 (max-in-natural-listp l)))

(defthm gen-natural-naturalp
  (naturalp (gen-natural lst)))

(defun gen-pos-integer (l)
  (declare (xargs :guard (natural-listp l)))
  (let ((n (+ 1 (max-in-natural-listp l))))
    (if (equal n 0) 1 n)))

(defthm gen-pos-integer-pos-integerp
  (pos-integerp (gen-pos-integer lst)))

;; We'll probably need to prove something like the following.
;;
;; (defthm gen-natural-not-in-list
;;   (implies (natural-listp l)
;; 	   (not (member-equal (gen-natural l) l))))

(in-theory (disable gen-natural gen-pos-integer))

;;-----------------------------------

(defun intersect-equal (a b)
  (declare (xargs :guard (and (true-listp a)
			      (true-listp b))))
  (cond ((atom a) nil)
	((member-equal (car a) b) (cons (car a) (intersect-equal (cdr a) b)))
	(t (intersect-equal (cdr a) b))))

