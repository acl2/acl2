; Checking whether a function is called in a term
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Rename this fn-called-in-termp?
;; Instead of calling this, one could gather all called functions and check for
;; membership in the result, but that might be slower.
(mutual-recursion
 (defun expr-calls-fn (fn expr)
   (declare (xargs :measure (acl2-count expr)
                   :guard (and (symbolp fn)
                               (pseudo-termp expr))))
   (cond ((variablep expr) nil)
         ((fquotep expr) nil)
         ;;lambda:
         ((consp (ffn-symb expr))
          (or (expr-calls-fn fn (third (ffn-symb expr))) ;lambda body
              (some-expr-calls-fn fn (fargs expr))))
         (t (or (eq fn (ffn-symb expr))
                (some-expr-calls-fn fn (fargs expr))))))

 (defun some-expr-calls-fn (fn exprs)
   (declare (xargs :measure (acl2-count exprs)
                   :guard (and (symbolp fn)
                               (pseudo-term-listp exprs))))
   (if (atom exprs)
       nil
     (or (expr-calls-fn fn (car exprs))
         (some-expr-calls-fn fn (cdr exprs))))))
