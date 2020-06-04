; A Utility to check whether a term is a subterm of another
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;todo: what about lambdas?
(mutual-recursion
 (defun subtermp (a b)
   (declare (xargs :guard (pseudo-termp b)))
   (if (atom b)
       (equal b a)
     (let ((fn (ffn-symb b)))
       (if (eq 'quote fn)
           (equal a b)
         (or (equal a b)
             (subterm-of-anyp a (fargs b)))))))

 (defun subterm-of-anyp (a b-lst)
   (declare (xargs :guard (pseudo-term-listp b-lst)))
   (if (endp b-lst)
       nil
     (or (subtermp a (car b-lst))
         (subterm-of-anyp a (cdr b-lst))))))
