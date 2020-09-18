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
(include-book "divconq-templates")

(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "kestrel/soft/define-sk2" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; n = m = 0:

(must-succeed*
 (gen-inputs 0 0 0 0)
 (apt::divconq old :schema :list-fold)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; n = m = 1:

(must-succeed*
 (gen-inputs 1 0 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 0 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; n = 2 and m = 1:

(must-succeed*
 (gen-inputs 2 0 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 0 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; n = 1 and m = 2:

(must-succeed*
 (gen-inputs 1 0 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 0 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 0 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; n = m = 2:

(must-succeed*
 (gen-inputs 2 0 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 0 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 0 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 1.

(must-succeed*
 (gen-inputs-1-0)
 (apt::divconq old :schema :list-fold)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 2.

(must-succeed*
 (gen-inputs-2-0)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

(must-succeed*
 (gen-inputs-2-1)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 3.

(must-succeed*
 (gen-inputs-3-0)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

(must-succeed*
 (gen-inputs-3-1)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

(must-succeed*
 (gen-inputs-3-2)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 4.

(must-succeed*
 (gen-inputs-4-0)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

(must-succeed*
 (gen-inputs-4-1)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

(must-succeed*
 (gen-inputs-4-2)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

(must-succeed*
 (gen-inputs-4-3)
 (apt::divconq old :schema :list-fold :list-input list)
 :with-output-off nil)

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

(soft::define-sk2 sortp[?sort] ()
  (forall (ints) (pre-post-p ints (?sort ints))))

(apt::divconq sortp[?sort]
              :schema :list-fold
              :spec-atom-name sortp-atom[?sort-atom]
              :spec-cons-name sortp-cons[?sort-cons]
              :cdr-output sorted-cdr
              :new-name sortp{1}[?sort][?sort-atom][?sort-cons])

(must-be-redundant ; result
 (progn
   (soft::defun2 fold[?sort-atom][?sort-cons] (ints)
     (declare (xargs :measure (acl2-count ints)))
     (cond ((atom ints) (?sort-atom ints))
           (t (?sort-cons (car ints)
                          (fold[?sort-atom][?sort-cons] (cdr ints))))))
   (soft::defun-sk2 sortp-atom[?sort-atom] ()
     (forall (ints)
             (impliez (atom ints)
                      (pre-post-p ints (?sort-atom ints)))))
   (soft::defun-sk2 sortp-cons[?sort-cons] ()
     (forall (ints sorted-cdr)
             (impliez (and (consp ints)
                           (pre-post-p (cdr ints) sorted-cdr))
                      (pre-post-p ints
                                  (?sort-cons (car ints) sorted-cdr)))))
   (soft::defun-sk2 equal[?sort][fold[?sort-atom][?sort-cons]] ()
     (forall (ints)
             (equal (?sort ints)
                    (fold[?sort-atom][?sort-cons] ints))))
   (soft::defun2 sortp{1}[?sort][?sort-atom][?sort-cons] ()
     (and (equal[?sort][fold[?sort-atom][?sort-cons]])
          (sortp-atom[?sort-atom])
          (sortp-cons[?sort-cons])))
   (defthmd sortp[?sort]-if-sortp{1}[?sort][?sort-atom][?sort-cons]
     (implies (sortp{1}[?sort][?sort-atom][?sort-cons])
              (sortp[?sort])))))
