
(in-package "ACL2")

;; This simply provides a non-tail-recursive way of reasoning about
;; make-list-ac, which is the macroexpansion of make-list.

(defthm make-list-ac-redef
  (equal (make-list-ac n val ac)
         (if (zp n)
             ac
           (cons val (make-list-ac (1- n) val ac))))
  :rule-classes ((:definition
                  :clique (make-list-ac)
                  :controller-alist ((make-list-ac t nil nil)))))

(in-theory (disable make-list-ac))
