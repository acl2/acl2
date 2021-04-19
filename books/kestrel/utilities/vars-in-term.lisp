; A simpler utility to find all the vars in a term
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))

;; This utility is similiar to all-vars but simpler.

;; Simpler than all-vars1 because this has no accumulator
(mutual-recursion
 (defund vars-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;;done below
                   ))
   (if (atom term)
       (list term)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           nil
         ;; We do not include free vars in lambda bodies, because lambdas in
         ;; ACL2 should always be closed:
         (vars-in-terms (fargs term))))))

 (defund vars-in-terms (terms)
   (declare (xargs :guard (and (true-listp terms)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       nil
     (union-eq (vars-in-term (first terms))
               (vars-in-terms (rest terms))))))

(make-flag vars-in-term)

(defthm-flag-vars-in-term
  (defthm symbol-listp-of-vars-in-term
    (implies (pseudo-termp term)
             (symbol-listp (vars-in-term term)))
    :flag vars-in-term)
  (defthm symbol-listp-of-vars-in-terms
    (implies (pseudo-term-listp terms)
             (symbol-listp (vars-in-terms terms)))
    :flag vars-in-terms)
  :hints (("Goal" :in-theory (enable vars-in-term vars-in-terms))))

(verify-guards vars-in-term)

(defthm-flag-vars-in-term
  (defthm true-listp-of-vars-in-term
    (true-listp (vars-in-term term))
    :flag vars-in-term)
  (defthm true-listp-of-vars-in-terms
    (true-listp (vars-in-terms terms))
    :flag vars-in-terms)
  :hints (("Goal" :in-theory (enable vars-in-term vars-in-terms))))

(defthm subsetp-equal-of-vars-in-term-of-car
  (implies (consp terms)
           (subsetp-equal (vars-in-term (car terms))
                          (vars-in-terms terms)))
  :hints (("Goal" :in-theory (enable vars-in-terms))))

(defthm subsetp-equal-of-vars-in-term-of-car
  (implies (consp terms)
           (subsetp-equal (vars-in-term (car terms))
                          (vars-in-terms terms)))
  :hints (("Goal" :in-theory (enable vars-in-terms))))

(defthm subsetp-equal-of-vars-in-terms-of-cdr
  (subsetp-equal (vars-in-terms (cdr terms))
                 (vars-in-terms terms))
  :hints (("Goal" :in-theory (enable vars-in-terms))))

(defthm subsetp-equal-of-vars-in-terms-of-cdr-chain
  (implies (subsetp-equal (vars-in-terms terms) vars)
           (subsetp-equal (vars-in-terms (cdr terms)) vars))
  :hints (("Goal" :in-theory (enable vars-in-terms))))

(defthm subsetp-equal-of-vars-in-terms-of-car-chain
  (implies (and (subsetp-equal (vars-in-terms terms) vars)
                (consp terms))
           (subsetp-equal (vars-in-term (car terms)) vars))
  :hints (("Goal" :in-theory (enable vars-in-terms))))

(defthm vars-in-term-when-not-consp-cheap
  (implies (not (consp term))
           (equal (vars-in-term term)
                  (list term)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable vars-in-term))))

(defthm vars-in-term-of-cons
  (equal (vars-in-term (cons fn args))
         (if (eq fn 'quote)
             nil
           (vars-in-terms args)))
  :hints (("Goal" :in-theory (enable vars-in-term))))

(defthm vars-in-terms-of-cons
  (equal (vars-in-terms (cons term terms))
         (union-equal (vars-in-term term)
                      (vars-in-terms terms)))
  :hints (("Goal" :in-theory (enable vars-in-terms))))

(defthm-flag-vars-in-term
  (defthm no-duplicatesp-of-vars-in-term
    (no-duplicatesp (vars-in-term term))
    :flag vars-in-term)
  (defthm no-duplicatesp-of-vars-in-terms
    (no-duplicatesp (vars-in-terms terms))
    :flag vars-in-terms)
  :hints (("Goal" :in-theory (enable vars-in-term vars-in-terms))))
