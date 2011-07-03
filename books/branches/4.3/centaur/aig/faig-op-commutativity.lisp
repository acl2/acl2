
(in-package "ACL2")

(include-book "three-four")


(defthm aig-and-constants
  (and (equal (aig-and nil x) nil)
       (equal (aig-and x nil) nil)
       (equal (aig-and x t) x)
       (equal (aig-and t x) x))
  :hints(("Goal" :in-theory (enable aig-and))))

(defun pfoc-faig-eval-args (args)
  (if (atom args)
      nil
    (cons (list 'faig-eval (car args) 'env)
          (pfoc-faig-eval-args (cdr args)))))

(defun pfoc-arg-casesplit-list (args)
  (if (atom args)
      nil
    (list* `(and stable-under-simplificationp
                 '(:cases ((aig-eval (car ,(car args)) env))))
           `(and stable-under-simplificationp
                 '(:cases ((aig-eval (cdr ,(car args)) env))))
           (pfoc-arg-casesplit-list (cdr args)))))

(defmacro prove-faig-op-commutes (op args)
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string "FAIG-EVAL-OF-" (symbol-name op))
             op)
     (equal (faig-eval (,op . ,args) env)
            (,op . ,(pfoc-faig-eval-args args)))
     :hints ,(pfoc-arg-casesplit-list args)))

(local (in-theory (enable aig-or)))

(prove-faig-op-commutes t-aig-fix (a))
(prove-faig-op-commutes f-aig-not (a))
(prove-faig-op-commutes f-aig-and (a b))
(prove-faig-op-commutes f-aig-or (a b))
(prove-faig-op-commutes f-aig-xor (a b))
(prove-faig-op-commutes f-aig-iff (a b))
(prove-faig-op-commutes f-aig-res (a b))
(prove-faig-op-commutes f-aig-ite (c a b))
(prove-faig-op-commutes f-aig-ite* (c a b))
(prove-faig-op-commutes t-aig-buf (c a))
(prove-faig-op-commutes f-aig-pullup (a))
(prove-faig-op-commutes f-aig-bi-buf (c a b))


(prove-faig-op-commutes t-aig-not (a))
(prove-faig-op-commutes t-aig-and (a b))
(prove-faig-op-commutes t-aig-or (a b))
(prove-faig-op-commutes t-aig-xor (a b))
(prove-faig-op-commutes t-aig-iff (a b))
(prove-faig-op-commutes t-aig-ite (c a b))
(prove-faig-op-commutes t-aig-ite* (c a b))
