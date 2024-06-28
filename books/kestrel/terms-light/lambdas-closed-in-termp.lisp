; A simple utility to check if lambdas are closed
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "free-vars-in-term")
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

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
                  (and (lambdas-closed-in-termp (lambda-body fn))
                       (subsetp-equal (free-vars-in-term (lambda-body fn))
                                      (lambda-formals fn)))
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

(defthm lambdas-closed-in-termsp-of-take
  (implies (lambdas-closed-in-termsp terms)
           (lambdas-closed-in-termsp (take n terms)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp))))

(defthm lambdas-closed-in-termsp-of-remove1-equal
  (implies (lambdas-closed-in-termsp terms)
           (lambdas-closed-in-termsp (remove1-equal term terms)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp))))

(defthm lambdas-closed-in-termp-of-car
  (implies (lambdas-closed-in-termsp terms)
           (lambdas-closed-in-termp (car terms)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp))))

(defthm lambdas-closed-in-termsp-of-cons
  (equal (lambdas-closed-in-termsp (cons term terms))
         (and (lambdas-closed-in-termp term)
              (lambdas-closed-in-termsp terms)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp))))

(defthm lambdas-closed-in-termsp-of-append
  (equal (lambdas-closed-in-termsp (append terms1 terms2))
         (and (lambdas-closed-in-termsp terms1)
              (lambdas-closed-in-termsp terms2)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp))))

(defthm lambdas-closed-in-termsp-of-revappend
  (equal (lambdas-closed-in-termsp (revappend terms1 terms2))
         (and (lambdas-closed-in-termsp (true-list-fix terms1))
              (lambdas-closed-in-termsp terms2)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp revappend))))

(defthm lambdas-closed-in-termsp-of-set-difference-equal
  (implies (lambdas-closed-in-termsp terms1)
           (lambdas-closed-in-termsp (set-difference-equal terms1 terms2)))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp set-difference-equal))))

(defthm lambdas-closed-in-termp-when-symbolp
  (implies (symbolp term)
           (lambdas-closed-in-termp term))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))

(defthm lambdas-closed-in-termsp-when-symbol-listp
  (implies (symbol-listp terms)
           (lambdas-closed-in-termsp terms))
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termsp symbol-listp))))

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

(defthm subsetp-equal-of-free-vars-in-term-of-lambda-body-and-lambda-formals
  (implies (and (lambdas-closed-in-termp term)
                (consp (car term)))
           (subsetp-equal (free-vars-in-term (lambda-body (car term)))
                          (lambda-formals (car term))))
  :hints (("Goal" :expand (lambdas-closed-in-termp term)
           :in-theory (enable lambdas-closed-in-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sanity check: logic-termp implies lambdas-closed-in-termp:

(local (make-flag lambdas-closed-in-termp))

(local
 (defthm-flag-lambdas-closed-in-termp
   (defthm lambdas-closed-in-termp-when-logic-termp
     (implies (logic-termp term w)
              (lambdas-closed-in-termp term))
     :flag lambdas-closed-in-termp)
   (defthm lambdas-closed-in-termsp-when-logic-term-listp
     (implies (logic-term-listp terms w)
              (lambdas-closed-in-termsp terms))
     :flag lambdas-closed-in-termsp)
   :hints (("Goal" :expand (free-vars-in-terms terms)
            :in-theory (enable free-vars-in-term lambdas-closed-in-termp)))))

;; redundant and non-local
(defthm lambdas-closed-in-termp-when-logic-termp
  (implies (logic-termp term w)
           (lambdas-closed-in-termp term)))

;; redundant and non-local
(defthm lambdas-closed-in-termsp-when-logic-term-listp
  (implies (logic-term-listp terms w)
           (lambdas-closed-in-termsp terms)))
