
(in-package "ACL2")

;; Evaluates several expressions, returning the value of the last one.
;; For example:
#||
ACL2 !>(progn$ (cons 'a 'b) (cw "Hello~%") (list 1 2 3))
Hello
(1 2 3)
||#

(defmacro progn$ (&rest rst)
  (cond ((null rst) nil)
        ((null (cdr rst)) (car rst))
        (t (xxxjoin 'prog2$ rst))))
