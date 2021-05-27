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
 (defund free-vars-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;;done below
                   ))
   (if (atom term)
       (list term)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           nil
         ;; We do not include free vars in lambda bodies, because lambdas in
         ;; pseudo-terms should always be closed:
         (free-vars-in-terms (fargs term))))))

 (defund free-vars-in-terms (terms)
   (declare (xargs :guard (and (true-listp terms)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       nil
     (union-eq (free-vars-in-term (first terms))
               (free-vars-in-terms (rest terms))))))

(make-flag free-vars-in-term)

(defthm-flag-free-vars-in-term
  (defthm symbol-listp-of-free-vars-in-term
    (implies (pseudo-termp term)
             (symbol-listp (free-vars-in-term term)))
    :flag free-vars-in-term)
  (defthm symbol-listp-of-free-vars-in-terms
    (implies (pseudo-term-listp terms)
             (symbol-listp (free-vars-in-terms terms)))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))

(verify-guards free-vars-in-term)

(defthm-flag-free-vars-in-term
  (defthm true-listp-of-free-vars-in-term
    (true-listp (free-vars-in-term term))
    :flag free-vars-in-term)
  (defthm true-listp-of-free-vars-in-terms
    (true-listp (free-vars-in-terms terms))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))

(defthm subsetp-equal-of-free-vars-in-term-of-car
  (implies (consp terms)
           (subsetp-equal (free-vars-in-term (car terms))
                          (free-vars-in-terms terms)))
  :hints (("Goal" :in-theory (enable free-vars-in-terms))))

(defthm subsetp-equal-of-free-vars-in-terms-of-cdr
  (subsetp-equal (free-vars-in-terms (cdr terms))
                 (free-vars-in-terms terms))
  :hints (("Goal" :in-theory (enable free-vars-in-terms))))

(defthm subsetp-equal-of-free-vars-in-terms-of-car-chain
  (implies (and (subsetp-equal (free-vars-in-terms terms) vars)
                (consp terms))
           (subsetp-equal (free-vars-in-term (car terms)) vars))
  :hints (("Goal" :in-theory (enable free-vars-in-terms))))

(defthm subsetp-equal-of-free-vars-in-terms-of-cdr-chain
  (implies (subsetp-equal (free-vars-in-terms terms) vars)
           (subsetp-equal (free-vars-in-terms (cdr terms)) vars))
  :hints (("Goal" :in-theory (enable free-vars-in-terms))))

(defthm free-vars-in-term-when-not-consp-cheap
  (implies (not (consp term))
           (equal (free-vars-in-term term)
                  (list term)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable free-vars-in-term))))

(defthm free-vars-in-term-of-cons
  (equal (free-vars-in-term (cons fn args))
         (if (eq fn 'quote)
             nil
           (free-vars-in-terms args)))
  :hints (("Goal" :in-theory (enable free-vars-in-term))))

(defthm free-vars-in-terms-of-cons
  (equal (free-vars-in-terms (cons term terms))
         (union-equal (free-vars-in-term term)
                      (free-vars-in-terms terms)))
  :hints (("Goal" :in-theory (enable free-vars-in-terms))))

(defthm-flag-free-vars-in-term
  (defthm no-duplicatesp-of-free-vars-in-term
    (no-duplicatesp (free-vars-in-term term))
    :flag free-vars-in-term)
  (defthm no-duplicatesp-of-free-vars-in-terms
    (no-duplicatesp (free-vars-in-terms terms))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))
