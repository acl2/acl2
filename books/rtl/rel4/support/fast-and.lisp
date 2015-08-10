(in-package "ACL2")

(defun split-list (lst lo hi)
  (cond ((endp lst)
         (mv lo hi))
        ((endp (cdr lst))
         (mv (cons (car lst) lo) hi))
        (t
         (split-list (cddr lst)
                     (cons (car lst) lo)
                     (cons (cadr lst) hi)))))

(defun fast-and-fn (conjuncts)
  (declare (xargs :mode :program))
  (cond ((endp conjuncts) ''t)
        ((endp (cdr conjuncts)) (car conjuncts))
        (t
         (mv-let (hi lo)
             (split-list conjuncts () ())
           (list 'if
                 (fast-and-fn hi)
                 (fast-and-fn lo)
                 'nil)))))

(defmacro fast-and (&rest conjuncts)
  (fast-and-fn conjuncts))
