(in-package "ACL2")


;; the guard may not be satified!!
;; may cause lisp hard error
;; will fix later as necessary

(defun symbol-repkg (s-in-pkg1 s-in-pkg2)
  (intern-in-package-of-symbol (symbol-name s-in-pkg1) s-in-pkg2))

(defun default-bind-free (key value pkg-witness) 
  (list (cons key (symbol-repkg value pkg-witness))))



; Matt K. mod: Renamed from symbol-name-equal.
(defun symbol-names-equal (s1 s2)
  (equal (symbol-name s1) 
         (symbol-name s2)))


(mutual-recursion 
 (defun found-symbol (symbol term)
   (if (atom term)
       (symbol-names-equal term symbol)
     (found-symbol-list symbol (cdr term))))

 (defun found-symbol-list (symbol arg-terms)
   (if (endp arg-terms) 
       nil
     (or (found-symbol symbol (car arg-terms))
         (found-symbol-list symbol (cdr arg-terms))))))


(mutual-recursion 
 (defun found-function-symbol (symbol term)
   (if (atom term) nil
     (and (atom (car term))
          (or (symbol-names-equal symbol (car term))
              (found-function-symbol-list symbol (cdr term))))))

 (defun found-function-symbol-list (symbol arg-terms)
   (if (endp arg-terms) 
       nil
     (or (found-function-symbol symbol (car arg-terms))
         (found-function-symbol-list symbol (cdr arg-terms))))))
                   

(mutual-recursion 
 (defun substitue-symbol (s g term)
   (if (atom term)
       (if (symbol-names-equal term s) (symbol-repkg g term) term)
     (cons (car term) 
           (substitue-symbol-list s g (cdr term)))))

 (defun substitue-symbol-list (s g arg-terms)
   (if (endp arg-terms) 
       nil
     (cons (substitue-symbol s g (car arg-terms))
           (substitue-symbol-list  s g (cdr arg-terms))))))
          

;; (found-symbol  'sframe '(topStack (popStack sframe)))

;; (substitue-symbol  'sframe 'gframe '(topStack (popStack sframe)))
        
(defun replace-occurance-binding (s g any anyx)
  (if (not (acl2::found-symbol s any)) nil
    (list (cons anyx (acl2::substitue-symbol s g any)))))





(mutual-recursion 
 (defun found-symbol2 (symbol term)
   (if (atom term)
       (equal term symbol)
     (found-symbol-list2 symbol (cdr term))))

 (defun found-symbol-list2 (symbol arg-terms)
   (if (endp arg-terms) 
       nil
     (or (found-symbol2 symbol (car arg-terms))
         (found-symbol-list2 symbol (cdr arg-terms))))))




(mutual-recursion 
 (defun substitue-symbol2 (s g term)
   (if (atom term)
       (if (equal term s) g term)
     (cons (car term) 
           (substitue-symbol-list2 s g (cdr term)))))

 (defun substitue-symbol-list2 (s g arg-terms)
   (if (endp arg-terms) 
       nil
     (cons (substitue-symbol2 s g (car arg-terms))
           (substitue-symbol-list2  s g (cdr arg-terms))))))
          

(defun replace-occurance-binding2 (s g any anyx)
  (if (not (acl2::found-symbol2 s any)) nil
    (list (cons anyx (acl2::substitue-symbol2 s g any)))))

