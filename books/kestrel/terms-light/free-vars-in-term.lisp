; A simpler utility to find all the vars in a term
;
; Copyright (C) 2019-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(local (include-book "all-vars1"))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))

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
   (declare (xargs :guard (pseudo-term-listp terms)))
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

;; must be a var
(defthm free-vars-in-term-when-not-consp-cheap
  (implies (not (consp term))
           (equal (free-vars-in-term term)
                  (list term)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable free-vars-in-term))))

(defthm free-vars-in-term-when-quotep
  (implies (quotep term)
           (equal (free-vars-in-term term)
                  nil))
  :hints (("Goal" :in-theory (enable free-vars-in-term))))

(defthm free-vars-in-terms-when-quote-listp
  (implies (quote-listp terms)
           (equal (free-vars-in-terms terms)
                  nil))
  :hints (("Goal" :in-theory (enable free-vars-in-terms))))

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

(defthm free-vars-in-terms-of-true-list-fix
  (equal (free-vars-in-terms (true-list-fix terms))
         (free-vars-in-terms terms))
  :hints (("Goal" :in-theory (enable true-list-fix free-vars-in-terms))))

(defthm free-vars-in-terms-of-append
  (equal (free-vars-in-terms (append terms1 terms2))
         (union-equal (free-vars-in-terms terms1)
                      (free-vars-in-terms terms2)))
  :hints (("Goal" :in-theory (enable append free-vars-in-terms))))

(defthm-flag-free-vars-in-term
  (defthm no-duplicatesp-of-free-vars-in-term
    (no-duplicatesp (free-vars-in-term term))
    :flag free-vars-in-term)
  (defthm no-duplicatesp-of-free-vars-in-terms
    (no-duplicatesp (free-vars-in-terms terms))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))

(defthm-flag-free-vars-in-term
  (defthmd free-vars-in-terms-when-symbol-listp
    (implies (symbol-listp terms)
             (equal (free-vars-in-terms terms)
                    (remove-duplicates-equal terms)))
    :flag free-vars-in-terms)
  :skip-others t
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms
                                     remove-duplicates-equal))))

(defthm free-vars-in-terms-when-not-consp-cheap
  (implies (not (consp terms))
           (not (free-vars-in-terms terms)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable free-vars-in-terms))))

;; (defthm-flag-free-vars-in-term
;;   (defthm subsetp-equal-of-free-vars-in-term-and-all-vars1
;;     (subsetp-equal (free-vars-in-term term) (all-vars1 term ans))
;;     :flag free-vars-in-term)
;;   (defthm subsetp-equal-of-free-vars-in-terms-and-all-vars1-lst
;;     (subsetp-equal (free-vars-in-terms terms) (all-vars1-lst terms ans))
;;     :flag free-vars-in-terms)
;;   :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Theorems connecting free-vars-in-term and all-vars.
;; There's no simple relationship.  Consider (foo x y) and (foo x y x).

(local (make-flag all-vars1))

(local
 ;rename these!
 (defthm-flag-all-vars1
   (defthm theorem-for-all-vars1
     (subsetp-equal (all-vars1 term ans)
                    (union-equal (free-vars-in-term term) ans))
     :flag all-vars1)
   (defthm theorem-for-all-vars1-lst
     (subsetp-equal (all-vars1-lst lst ans)
                    (union-equal (free-vars-in-terms lst) ans))
     :flag all-vars1-lst)
   :hints (("Goal" :expand ((all-vars1 term ans)
                            (all-vars1-lst terms ans))
            :in-theory (e/d (all-vars1 all-vars1-lst free-vars-in-term free-vars-in-terms) (reverse))))))

(defthm subsetp-equal-of-all-vars1-of-nil-and-free-vars-in-term
  (subsetp-equal (all-vars1 term nil)
                 (free-vars-in-term term))
  :hints (("Goal" :use (:instance theorem-for-all-vars1 (ans nil))
           :in-theory (disable theorem-for-all-vars1))))

(defthm subsetp-equal-of-all-vars-and-free-vars-in-term
  (subsetp-equal (all-vars term)
                 (free-vars-in-term term))
  :hints (("Goal" :use (:instance all-vars))))

(local
 ;rename these!
 (defthm-flag-all-vars1
   (defthm subsetp-equal-of-free-vars-in-term-and-all-vars1-helper
     (subsetp-equal (union-equal (free-vars-in-term term) ans)
                    (all-vars1 term ans))
     :flag all-vars1)
   (defthm subsetp-equal-of-free-vars-in-terms-and-all-vars1-lst-helper
     (subsetp-equal (union-equal (free-vars-in-terms lst) ans)
                    (all-vars1-lst lst ans))
     :flag all-vars1-lst)
   :hints (("Goal" :expand ((all-vars1 term ans)
                            (all-vars1-lst terms ans))
            :in-theory (e/d (all-vars1 all-vars1-lst free-vars-in-term free-vars-in-terms) (reverse))))))

(defthm subsetp-equal-of-free-vars-in-term-and-all-vars1
  (subsetp-equal (free-vars-in-term term)
                 (all-vars1 term nil))
  :hints (("Goal" :use (:instance subsetp-equal-of-free-vars-in-term-and-all-vars1-helper (ans nil))
           :in-theory (disable subsetp-equal-of-free-vars-in-term-and-all-vars1-helper))))

(defthm subsetp-equal-of-free-vars-in-term-and-all-vars
  (subsetp-equal (free-vars-in-term term)
                 (all-vars term))
  :hints (("Goal" :use (:instance all-vars))))
