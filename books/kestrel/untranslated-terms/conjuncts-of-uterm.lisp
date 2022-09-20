; Getting the conjuncts of an untranslated term
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
 ;; TODO: Consider treating a negated disjunction as a conjunction
 (defun conjuncts-of-uterm (uterm ;; untranslated
                            )
   (declare (xargs :guard t
                   :verify-guards nil ; done below
                   ))
   (if (not (consp uterm))
       (list uterm)
     (if (eq 'and (ffn-symb uterm))
         (conjuncts-of-uterms (fargs uterm))
       (if (and (eq 'if (ffn-symb uterm)) ; (if <x> <y> nil) is (and <x> <y>)
                (= 3 (len (fargs uterm))) ; for guards
                (or (equal nil (farg3 uterm))
                    (equal *nil* (farg3 uterm))))
           (union-equal-alt (conjuncts-of-uterm (farg1 uterm))
                            (conjuncts-of-uterm (farg2 uterm)))
         ;; todo: Handle (if <x> nil <y>)?
         (list uterm)))))

 (defun conjuncts-of-uterms (uterms ;; untranslated
                             )
   (declare (xargs :guard t))
   (if (atom uterms)
       nil
     (union-equal-alt (conjuncts-of-uterm (first uterms))
                      (conjuncts-of-uterms (rest uterms))))))

(make-flag conjuncts-of-uterm)

(defthm-flag-conjuncts-of-uterm)

(defthm-flag-conjuncts-of-uterm
  (defthm true-listp-of-conjuncts-of-uterm
    (true-listp (conjuncts-of-uterm uterm))
    :flag conjuncts-of-uterm)
  (defthm true-listp-of-conjuncts-of-uterms
    (true-listp (conjuncts-of-uterms uterms))
    :flag conjuncts-of-uterms))

(verify-guards conjuncts-of-uterm :guard-debug t)
