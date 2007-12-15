

(in-package "ACL2")

;; Evaluates several expressions, returning the value of the last one.
;; For example:
#||
ACL2 !>(progn$ (cons 'a 'b) (cw "Hello~%") (list 1 2 3))
Hello
(1 2 3)
||#

(defun progn$-fn (stmts)
  (if (atom stmts)
      nil
    (if (atom (cdr stmts))
        (car stmts)
      `(prog2$ ,(car stmts)
               ,(progn$-fn (cdr stmts))))))

(defmacro progn$ (&rest stmts)
  (progn$-fn stmts))
