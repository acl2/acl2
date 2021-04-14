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
 (defund lambdas-closed-in-termp (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (variablep term)
       t
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           t
         (and (lambdas-closed-in-termsp (fargs term))
              (if (consp fn) ; fn is (lambda (...vars...) body)
                  (and (lambdas-closed-in-termp (third fn))
                       (subsetp-equal (vars-in-term (third fn))
                                      (second fn)))
                t))))))
 (defund lambdas-closed-in-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
     (and (lambdas-closed-in-termp (first terms))
          (lambdas-closed-in-termsp (rest terms))))))

(defthm lambdas-closed-in-termsp-of-cdr
  (implies (lambdas-closed-in-termsp terms)
           (lambdas-closed-in-termsp (cdr terms)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp))))

(defthm lambdas-closed-in-termp-of-car
  (implies (lambdas-closed-in-termsp terms)
           (lambdas-closed-in-termp (car terms)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp))))

(defthm lambdas-closed-in-termsp-of-when-lambdas-closed-in-termp
   (implies (and (lambdas-closed-in-termp term)
                 (not (equal 'quote (car term))))
           (lambdas-closed-in-termsp (cdr term)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))

(defthm lambdas-closed-in-termsp-of-caddr-of-car
  (implies (and (lambdas-closed-in-termp term)
                (not (equal 'quote (car term))))
           (lambdas-closed-in-termp (caddr (car term))))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))
