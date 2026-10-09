; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(defun typ1 (flg x) ; expand-type

; Flg is nil at the top level, when x is intended to be a type expression as
; recognized by weak-hol-typep except that x might use the :arrow*
; abbreviation.  Otherwise, when flg is not nil, x is a list.

  (declare (xargs :guard t))
  (cond
   ((null flg)
    (cond
     ((or (not (true-listp x))
          (atom x))
      x)
     (t (case (car x)
          (:arrow* (typ1 t (cdr x)))
          (:atom x)
          ((:arrow :hash)
           (list 'list (car x) (typ1 nil (nth 1 x)) (typ1 nil (nth 2 x))))
          ((:list :option)
           (list 'list (car x) (typ1 nil (nth 1 x))))
          (t (er hard? 'typ
                 "Illegal type encountered: ~x0."
                 x))))))
   (t
    (case-match x
      ((a b)
       `(list :arrow ,(typ1 nil a) ,(typ1 nil b)))
      ((a & . &)
       `(list :arrow ,(typ1 nil a) ,(typ1 t (cdr x))))
      (& (er hard? 'typ
             "Illegal list following :arrow*, ~x0."
             x))))))

(defmacro typ (type-expr) ; expand-type
  (typ1 nil type-expr))
