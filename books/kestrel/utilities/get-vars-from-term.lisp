; An old utility for getting vars from a term
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

;; TODO: Deprecate this in favor of free-vars-in-term, but some things in Axe
;; may depend on the order of the vars returned by this.

;I guess this works for lambdas too, since they must be complete (i.e., the lambda formals must include all vars that are free in the lambda body)
;TODO: Compare to all-vars1
(mutual-recursion
 (defund get-vars-from-term-aux (term acc)
   (declare (xargs :guard (and (true-listp acc)
                               (pseudo-termp term))
                   :verify-guards nil ;;done below
                   ))
   (if (atom term)
       (add-to-set-eq term acc)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           acc
         (get-vars-from-terms-aux (fargs term) acc)))))

 (defund get-vars-from-terms-aux (terms acc)
   (declare (xargs :guard (and (true-listp acc)
                               (true-listp terms)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       acc
     (get-vars-from-terms-aux (cdr terms)
                          (get-vars-from-term-aux (car terms) acc)))))

(make-flag get-vars-from-term-aux)

(defthm-flag-get-vars-from-term-aux
  (defthm true-listp-of-get-vars-from-term-aux
    (implies (true-listp acc)
             (true-listp (get-vars-from-term-aux term acc)))
    :flag get-vars-from-term-aux)
  (defthm true-listp-of-get-vars-from-terms-aux
    (implies (true-listp acc)
             (true-listp (get-vars-from-terms-aux terms acc)))
    :flag get-vars-from-terms-aux)
  :hints (("Goal" :in-theory (enable get-vars-from-term-aux get-vars-from-terms-aux))))

(verify-guards get-vars-from-term-aux)

(defun get-vars-from-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (get-vars-from-term-aux term nil))

(defun get-vars-from-terms (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (get-vars-from-terms-aux terms nil))

(defthm-flag-get-vars-from-term-aux
  (defthm symbol-listp-of-get-vars-from-term-aux
    (implies (and (pseudo-termp term)
                  (symbol-listp acc))
             (symbol-listp (get-vars-from-term-aux term acc)))
    :flag get-vars-from-term-aux)
  (defthm symbol-listp-of-get-vars-from-terms-aux
    (implies (and (pseudo-term-listp terms)
                  (symbol-listp acc))
             (symbol-listp (get-vars-from-terms-aux terms acc)))
    :flag get-vars-from-terms-aux)
  :hints (("Goal" :in-theory (enable get-vars-from-term-aux get-vars-from-terms-aux))))

(defthm symbol-listp-of-get-vars-from-terms
  (implies (pseudo-term-listp terms)
           (symbol-listp (get-vars-from-terms terms)))
  :hints (("Goal" :in-theory (enable get-vars-from-terms))))

(defthm symbol-listp-of-get-vars-from-term
  (implies (pseudo-termp term)
           (symbol-listp (get-vars-from-term term)))
  :hints (("Goal" :in-theory (enable get-vars-from-term))))

(defthm true-listp-of-get-vars-from-terms
  (implies (pseudo-term-listp terms)
           (true-listp (get-vars-from-terms terms)))
  :hints (("Goal" :in-theory (enable get-vars-from-terms))))

(defthm true-listp-of-get-vars-from-term
  (implies (pseudo-termp term)
           (true-listp (get-vars-from-term term)))
  :hints (("Goal" :in-theory (enable get-vars-from-term))))
