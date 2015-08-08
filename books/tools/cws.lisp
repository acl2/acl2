

(in-package "ACL2")

;; Utility that prints one or more expressions and their values,
;; returning the value of the last expression.
;; For example:
#||
ACL2 !>(let ((x '(a b c)) (y '(d e f))) (cws x y))
X: (A B C)
Y: (D E F)
(D E F)
||#

(defmacro cwval (expr)
  `(let ((cw-val ,expr))
     (prog2$ (cw "~x0: ~x1~%" ',expr cw-val)
             cw-val)))

(defun cws-fn (lst)
  (if (atom lst)
      nil
    (cons `(cwval ,(car lst))
          (cws-fn (cdr lst)))))

(defmacro cws (&rest lst)
  (cons 'progn$ (cws-fn lst)))

