;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;; helper functions for basic data structure manipulation
(in-package "ACL2")

;; exist
;; mrg: this is the same as the built-in function member-equal
(defun exist (elem lista)
  "exist: check if an element exist in a list"
  (if (endp lista)
      nil
    (if (equal elem (car lista))
        t
      (exist elem (cdr lista)))))

;; end
;; mrg: this is the same as (car (last lista))
(defun end (lista)
  "end: return the last element in a list"
  (if (endp (cdr lista))
      (car lista)
    (end (cdr lista))))

;; prefix
;; mrg: (prefix lst n) is the same as (take n lst)
(defun prefix (listx end)
  (if (or (zp end) (< end 0))
      nil
    (cons (car listx) (prefix (cdr listx) (1- end)))))

;; head
;; this will be faster than defined with prefix
(defun head (listx)
  (if (endp (cdr listx))
      nil
    (cons (car listx) (head (cdr listx)))))

;; sublist
(defun sublist (listx start end)
  (if (zp start)
      (prefix listx end)
    (sublist (cdr listx) (1- start) end)))

;; my-delete
(defun my-delete (listx elem)
  "my-delete: delete an element from the list. If there're duplicates, this function deletes the first one in the list."
  (if (endp listx) ;; elem does not exist in the list
      listx
      (if (equal (car listx) elem)
	  (cdr listx)
	  (cons (car listx)
		(my-delete (cdr listx) elem)))))

(defthm delete-must-reduce
    (implies (exist a listx)
	     (< (len (my-delete listx a)) (len listx))))

;; dash-to-underscore-char
(defun dash-to-underscore-char (charx)
  (if (equal charx '-)
      '_
      charx))

;; dash-to-underscore-helper
(defun dash-to-underscore-helper (name-list)
  (if (endp name-list)
      nil
      (cons (dash-to-underscore-char (car name-list))
	    (dash-to-underscore-helper (cdr name-list)))))

;; dash-to-underscore
(defun dash-to-underscore (name)
  (intern-in-package-of-symbol
   (coerce
    (dash-to-underscore-helper
     (coerce (symbol-name name)'list))
    'string)
   'ACL2))


;; and-list-logic
(defun and-list-logic (lst)
  (cond ((endp lst) t)
        ((endp (cdr lst)) (car lst))
	(t `(if ,(car lst) ,(and-list-logic (cdr lst)) 'nil))))

;; append-and-decl
(defun append-and-decl (listx listy let-type)
  "append-and-decl: append two and lists together in the underneath representation"
  (if (endp listy)
      listx
      (append-and-decl
       (list 'if (list (car let-type) (car listy)) listx ''nil)
       (cdr listy)
       (cdr let-type))))

;; append-and-hypo
(defun append-and-hypo (listx listy)
  "append-and-hypo: append two and lists together in the underneath representation"
  (if (endp listy)
      listx
      (append-and-hypo
       (list 'if (car listy) listx ''nil)
       (cdr listy))))

;; assoc-get-value
(defun assoc-get-value (listx)
  "assoc-get-value: get all values out of an associate list"
  (if (endp listx)
      nil
      (cons (cadar listx)
	    (assoc-get-value (cdr listx)))))

;; assoc-get-key
(defun assoc-get-key (listx)
  "assoc-get-key: get all keys out of an associate list"
  (if (endp listx)
      nil
      (cons (caar listx)
	    (assoc-get-key (cdr listx)))))

;; assoc-no-repeat
(defun assoc-no-repeat (assoc-list)
  "assoc-no-repeat: check if an associate list has repeated keys"
  (if (endp assoc-list)
      t
      (if (equal (assoc-equal (caar assoc-list) (cdr assoc-list)) nil)
	  (assoc-no-repeat (cdr assoc-list))
	  nil)))

;; invert-assoc
(defun invert-assoc (assoc-list)
  "invert-assoc: invert the key and value pairs in an associate list"
  (if (endp assoc-list)
      nil
      (cons (list (cadar assoc-list) (caar assoc-list))
	   (invert-assoc (cdr assoc-list)))))

;; create-assoc-helper
 (defun create-assoc-helper (list-keys list-values)
   (if (endp list-keys)
       nil
       (cons (list (car list-keys) (car list-values))
	     (create-assoc-helper (cdr list-keys) (cdr list-values)))))

;; create-assoc
(defun create-assoc (list-keys list-values)
  "create-assoc: combines two lists together to form an associate list"
  (if (equal (len list-keys) (len list-values))
      (create-assoc-helper list-keys list-values)
      (cw "Error(helper): list-keys and list-values should be of the same len.")))

;; replace-lambda-params
 (defun replace-lambda-params (expr lambda-params-mapping)
   "replace-lambda-params: replace params in the expression using the mapping"
   (if (atom expr)
       (let ((res (assoc-equal expr lambda-params-mapping)))
	 (if (equal res nil)
	     expr
	     (cadr res)))
       (cons (replace-lambda-params (car expr) lambda-params-mapping)
	     (replace-lambda-params (cdr expr) lambda-params-mapping))))

;; assoc-lambda
(defun assoc-lambda (expr lambda-params-mapping assoc-list)
  "assoc-lambda: replacing params in expression using lambda-params-mapping \
and check if the resulting term exist in assoc-list keys. Return the resulting \
pair from assoc-list."
  (let ((new-expr (replace-lambda-params expr lambda-params-mapping)))
       (assoc-equal new-expr assoc-list)))

;; combine
(defun combine (lista listb)
  "combine: takes two items, either atoms or lists, then combine them together according to some rule. E.g. if either element is nil, return the other one; if a is atom and b is list, do cons; if both are lists, do append; if a is list and b is atom, attach b at the end; if both are atoms, make a list"
  (cond ((and (atom lista) (atom listb) (not (equal lista nil)) (not (equal listb nil)))
	 (list lista listb))
	((and (atom lista) (listp listb) (not (equal lista nil)))
	 (cons lista listb))
	((and (listp lista) (atom listb) (not (equal listb nil)))
	 (append lista (list listb)))
	((and (listp lista) (listp listb))
	 (append lista listb))))

