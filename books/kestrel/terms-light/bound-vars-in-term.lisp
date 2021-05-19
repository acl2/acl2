; A utility to gather the lambda-bound vars in a term
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(mutual-recursion
 ;; Gather all the vars that are bound in lambdas in TERM.  Vars that are bound
 ;; in more than one lambda appear only once in the result.  Does not include
 ;; vars that are free (unless they are also bound by a lambbda).
 (defun bound-vars-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       nil ;; not a lambda-bound var
     (let ((fn (ffn-symb term)))
       (if (eq fn 'quote)
           nil
         (if (consp fn)
             ;; a lambda application:
             (union-eq (lambda-formals fn)
                       (union-eq (bound-vars-in-term (lambda-body fn))
                                 (bound-vars-in-terms (fargs term))))
           ;; not a lambda application:
           (bound-vars-in-terms (fargs term)))))))

 (defun bound-vars-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (union-eq (bound-vars-in-term (first terms))
               (bound-vars-in-terms (rest terms))))))

;todo: make a variant of defthm-flag-xxx that puts in the guards as assumptions
(make-flag bound-vars-in-term)

(defthm-flag-bound-vars-in-term
  (defthm symbol-listp-of-bound-vars-in-term
    (implies (pseudo-termp term)
             (symbol-listp (bound-vars-in-term term)))
    :flag bound-vars-in-term)
  (defthm theorem-for-bound-vars-in-terms
    (implies (pseudo-term-listp terms)
             (symbol-listp (bound-vars-in-terms terms)))
    :flag bound-vars-in-terms)
  :hints (("Goal" :expand (pseudo-term-listp term)
           :in-theory (enable pseudo-term-listp))))
