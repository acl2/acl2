(in-package "ACL2")

;; Some shared functions

;; Recursively collect the list of unique variables (symbols) used in
;; a term or list of terms
(mutual-recursion
 (defun collect-vars (q)
   (if (atom q)
       (if (symbolp q)
	   (if (and (not (equal q nil)) (not (equal q t)))
	       (list q)
	     nil)
	 nil)
     (collect-vars-list (cdr q)))) ;; collect vars from the list of args

 (defun collect-vars-list (q-list)
   (if (atom q-list) nil
     (let ((car-syms (collect-vars (car q-list))))
       (if car-syms (union-equal car-syms (collect-vars-list (cdr q-list)))
	 (collect-vars-list (cdr q-list))))))
 )


;; Return the list of keys from an alist
(defun get-alist-keys (al)
  (if (atom al)
      nil
    (cons (caar al)
	  (get-alist-keys (cdr al)))))

;; Return the list of vals from an alist
(defun get-alist-vals (al)
  (if (atom al)
      nil
    (cons (cdar al)
	  (get-alist-vals (cdr al)))))
