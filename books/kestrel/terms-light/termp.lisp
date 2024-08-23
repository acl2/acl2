; A lightweight book about the built-in function termp
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable termp))

(defthm termp-of-cons
  (equal (termp (cons a x) w)
         (cond
           ((equal a 'quote)
            (and (consp x) (null (cdr x))))
           ((symbolp a)
            (let ((arity (arity a w)))
              (and arity
                   (term-listp x w)
                   (equal (length x) ; todo: len
                          arity))))
           (t (and (consp a)
                   (true-listp a)
                   (equal (car a) 'lambda)
                   (equal 3 (length a)) ; todo: len
                   (arglistp (cadr a)) ; todo: call this legal-variable-listp?
                   (termp (caddr a) w)
                   (null (set-difference-eq (all-vars (caddr a))
                                            (cadr a)))
                   (term-listp x w)
                   (eql (length (cadr a))
                        (length x))))))
  :hints (("Goal" :in-theory (enable termp))))
