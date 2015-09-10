; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

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
