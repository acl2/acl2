; Getting the conjuncts and disjuncts of untranslated terms
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also conjuncts-of-uterm.lisp and disjuncts-of-uterm.lisp.
;; This file treats a negated conjunction as a disjunction, and vice versa.

;; Doesnt handle myif, boolif, booland, boolor, etc.
;; TODO: Consider dropping constant conjuncts / disjuncts.

(include-book "kestrel/terms-light/negate-terms" :dir :system)
(include-book "kestrel/lists-light/union-equal-alt" :dir :system)

(mutual-recursion
 ;; Returns a list of conjuncts (uterms) whose conjunction is boolean-equivalent to UTERM.
 (defund conjuncts-of-uterm2 (uterm)
   (declare (xargs :guard t))
   (if (not (consp uterm)) ; term is a variable
       (list uterm)
     (let ((fn (ffn-symb uterm)))
       (case fn
         (and (conjuncts-of-uterms2 (fargs uterm)))
         (if (if (not (= 3 (len (fargs uterm)))) ; for guards
                 (er hard? 'conjuncts-of-uterm2 "Bad arity: ~x0." uterm)
               (if (or (equal nil (farg3 uterm))
                       (equal *nil* (farg3 uterm)))
                   ;;  (if <x> <y> nil) is (and <x> <y>):
                   (union-equal-alt (conjuncts-of-uterm2 (farg1 uterm))
                                    (conjuncts-of-uterm2 (farg2 uterm)))
                 (if (or (equal nil (farg2 uterm))
                         (equal *nil* (farg2 uterm)))
                     ;; (if <x> nil <y>) is (and (not <x>) <y>)
                     (union-equal-alt (negate-terms (disjuncts-of-uterm2 (farg1 uterm)))
                                      (conjuncts-of-uterm2 (farg3 uterm)))
                   (list uterm)))))
         (not (if (not (= 1 (len (fargs uterm)))) ; for guards
                  (er hard? 'conjuncts-of-uterm2 "Bad arity: ~x0." uterm)
                ;; (not (or <x> <y> ...)) is (and (not <x>) (not <y>) ..):
                (negate-terms (disjuncts-of-uterm2 (farg1 uterm)))))
         (otherwise ;; no special handling:
          (list uterm))))))

 ;; Returns a list of conjuncts (uterms) whose conjunction is
 ;; boolean-equivalent to the conjunction of the UTERMS.
 (defun conjuncts-of-uterms2 (uterms)
   (declare (xargs :guard t))
   (if (not (consp uterms))
       nil
     (union-equal-alt (conjuncts-of-uterm2 (first uterms))
                      (conjuncts-of-uterms2 (rest uterms)))))

  ;; Returns a list of conjuncts (uterms) whose disjunction is boolean-equivalent to UTERM.
 (defund disjuncts-of-uterm2 (uterm)
   (declare (xargs :guard t
                   :verify-guards nil ; done below
                   ))
   (if (not (consp uterm)) ; term is a variable
       (list uterm)
     (let ((fn (ffn-symb uterm)))
       (case fn
         (or (disjuncts-of-uterms2 (fargs uterm)))
         (if (if (not (= 3 (len (fargs uterm)))) ; for guards
                 (er hard? 'disjuncts-of-uterm2 "Bad arity: ~x0." uterm)
               (if (equal (farg1 uterm) (farg2 uterm))
                   ;; (if <x> <x> <y>) is (or <x> <y>):
                   (union-equal-alt (disjuncts-of-uterm2 (farg1 uterm))
                                    (disjuncts-of-uterm2 (farg3 uterm)))
                 (if (or (equal t (farg2 uterm))
                         (equal *t* (farg2 uterm)))
                     ;; (if <x> t <y>) is (or <x> <y>):
                     (union-equal-alt (disjuncts-of-uterm2 (farg1 uterm))
                                      (disjuncts-of-uterm2 (farg3 uterm)))
                   (if (or (equal t (farg3 uterm))
                           (equal *t* (farg3 uterm)))
                       ;; (if <x> <y> t) is (or (not <x>) <y>):
                       (union-equal-alt (negate-terms (conjuncts-of-uterm2 (farg1 uterm)))
                                        (disjuncts-of-uterm2 (farg2 uterm)))
                     (list uterm))))))
         (not (if (not (= 1 (len (fargs uterm)))) ; for guards
                  (er hard? 'disjuncts-of-uterm2 "Bad arity: ~x0." uterm)
                ;; (not (and <x> <y> ...)) is (or (not <x>) (not <y>) ..):
                (negate-terms (conjuncts-of-uterm2 (farg1 uterm)))))
         (otherwise ;; no special handling:
          (list uterm))))))

 ;; Returns a list of disjuncts (uterms) whose disjunction is
 ;; boolean-equivalent to the disjunction of the UTERMS.
 (defun disjuncts-of-uterms2 (uterms)
   (declare (xargs :guard t))
   (if (not (consp uterms))
       nil
     (union-equal-alt (disjuncts-of-uterm2 (first uterms))
                      (disjuncts-of-uterms2 (rest uterms))))))
