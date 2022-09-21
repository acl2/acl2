; Getting the disjuncts of an untranslated term
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/lists-light/union-equal-alt" :dir :system)
(include-book "tools/flag" :dir :system)

(mutual-recursion
 ;; TODO: Consider treating a negated conjunction as a disjunction
 ;; The result is only boolean-equivalent to UTERM
 (defun disjuncts-of-uterm (uterm ;; untranslated
                            )
   (declare (xargs :guard t
                   :verify-guards nil ; done below
                   ))
   (if (not (consp uterm))
       (list uterm)
     (if (eq 'or (ffn-symb uterm))
         (disjuncts-of-uterms (fargs uterm))
       (if (and (eq 'if (ffn-symb uterm)) ; (if <x> <x> <y>) is (or <x> <y>)
                (= 3 (len (fargs uterm))) ; for guards
                (equal (farg1 uterm) (farg2 uterm)))
           (union-equal-alt (disjuncts-of-uterm (farg1 uterm))
                            (disjuncts-of-uterm (farg3 uterm)))
         (if (and (eq 'if (ffn-symb uterm)) ; (if <x> t <y>) is (or <x> <y>)
                  (= 3 (len (fargs uterm))) ; for guards
                  (or (equal (farg2 uterm) t)
                      (equal (farg2 uterm) 't)))
             (union-equal-alt (disjuncts-of-uterm (farg1 uterm))
                              (disjuncts-of-uterm (farg3 uterm)))
           (list uterm))))))

 (defun disjuncts-of-uterms (uterms ;; untranslated
                             )
   (declare (xargs :guard t))
   (if (atom uterms)
       nil
     (union-equal-alt (disjuncts-of-uterm (first uterms))
                      (disjuncts-of-uterms (rest uterms))))))

(make-flag disjuncts-of-uterm)

(defthm-flag-disjuncts-of-uterm)

(defthm-flag-disjuncts-of-uterm
  (defthm true-listp-of-disjuncts-of-uterm
    (true-listp (disjuncts-of-uterm uterm))
    :flag disjuncts-of-uterm)
  (defthm true-listp-of-disjuncts-of-uterms
    (true-listp (disjuncts-of-uterms uterms))
    :flag disjuncts-of-uterms))

(verify-guards disjuncts-of-uterm :guard-debug t)
