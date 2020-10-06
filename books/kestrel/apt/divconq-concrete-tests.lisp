; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "divconq")

(include-book "std/testing/must-be-redundant" :dir :system)

(include-book "kestrel/soft/defunvar" :dir :system)
(include-book "kestrel/soft/define-sk2" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Insertion sort (specification and initial refinement step).

(define orderedp ((ints integer-listp))
  :returns (yes/no booleanp)
  (or (endp ints)
      (endp (cdr ints))
      (and (< (car ints) (cadr ints))
           (orderedp (cdr ints)))))

(define permutationp ((ints1 integer-listp) (ints2 integer-listp))
  :returns (yes/no booleanp)
  (cond ((endp ints1) (endp ints2))
        (t (and (consp ints2)
                (member (car ints1) ints2)
                (permutationp (cdr ints1) (remove1 (car ints1) ints2))))))

(define pre-post-p (input output)
  :returns (yes/no booleanp)
  (impliez
   ;; precondition:
   (integer-listp input)
   ;; postcondition:
   (and (integer-listp output)
        (orderedp output)
        (permutationp input output))))

(defunvar ?sort (*) => *)

(define-sk2 sortp[?sort] ()
  (forall (ints) (pre-post-p ints (?sort ints))))

(apt::divconq sortp[?sort]
              :schema :list-fold
              :spec-atom-name sortp-atom[?sort-atom]
              :spec-cons-name sortp-cons[?sort-cons]
              :cdr-output sorted-cdr
              :new-name sortp{1}[?sort][?sort-atom][?sort-cons])

(must-be-redundant ; result
 (progn
   (defun2 fold[?sort-atom][?sort-cons] (ints)
     (declare (xargs :measure (acl2-count ints)))
     (cond ((atom ints) (?sort-atom ints))
           (t (?sort-cons (car ints)
                          (fold[?sort-atom][?sort-cons] (cdr ints))))))
   (defun-sk2 sortp-atom[?sort-atom] ()
     (forall (ints)
             (impliez (atom ints)
                      (pre-post-p ints (?sort-atom ints)))))
   (defun-sk2 sortp-cons[?sort-cons] ()
     (forall (ints sorted-cdr)
             (impliez (and (consp ints)
                           (pre-post-p (cdr ints) sorted-cdr))
                      (pre-post-p ints
                                  (?sort-cons (car ints) sorted-cdr)))))
   (defequal equal[?sort][fold[?sort-atom][?sort-cons]]
     :left ?sort
     :right fold[?sort-atom][?sort-cons]
     :vars (ints)
     :enable nil
     :left-to-right-enable nil
     :right-to-left-enable nil)
   (defun2 sortp{1}[?sort][?sort-atom][?sort-cons] ()
     (and (equal[?sort][fold[?sort-atom][?sort-cons]])
          (sortp-atom[?sort-atom])
          (sortp-cons[?sort-cons])))
   (defthmd sortp[?sort]-if-sortp{1}[?sort][?sort-atom][?sort-cons]
     (implies (sortp{1}[?sort][?sort-atom][?sort-cons])
              (sortp[?sort])))))
