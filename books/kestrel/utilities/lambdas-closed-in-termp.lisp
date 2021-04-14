; A simple utility to check if lambdas are closed
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "vars-in-term")

;; Checks that all free vars in lambda bodies are among the corresponding lambda vars
(mutual-recursion
 (defun lambdas-closed-in-termp (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (variablep term)
       t
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           t
         (and (lambdas-closed-in-termsp (fargs term))
              (if (consp fn) ; fn is (lambda (...vars...) body)
                  (subsetp-equal (vars-in-term (third fn))
                                 (second fn))
                t))))))
 (defun lambdas-closed-in-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
     (and (lambdas-closed-in-termp (first terms))
          (lambdas-closed-in-termsp (rest terms))))))
