; Coglio-Westfold's ACL2-2020 Paper Examples
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/apt/isodata" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains the schematic example in Section 3.2
; of the paper "Isomorphic Data Type Transformations"
; by A. Coglio and S. Westfold, published at the ACL2-2020 Workshop.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; abstract data representations and conversions,
; and abstract constituents of F:

(encapsulate
  (((old *) => *) ; old representation
   ((new *) => *) ; new representation
   ((iso *) => *) ; conversion from old to new representation
   ((osi *) => *) ; conversion from new to old representation
   ((a *) => *)   ; termination test
   ((b *) => *)   ; base of the recursion
   ((c * *) => *) ; combination of function argument with recursive call
   ((d *) => *)   ; decreasing of the function argument
   ((m *) => *)   ; measure of the function argument
   ((g *) => *))  ; guard of the function

  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (local (defun old (x) t)) ; all values
  (local (defun new (x) t)) ; all values
  (local (defun iso (x) x)) ; identity conversion
  (local (defun osi (x) x)) ; identity conversion

  (local (defun a (x) (zp x)))   ; 0 or not a natural number
  (local (defun b (x) nil))      ; anything, irrelevant
  (local (defun c (x y) nil))    ; anything, irrelevant
  (local (defun d (x) (1- x)))   ; decrement by 1
  (local (defun m (x) (nfix x))) ; argument, treated as natural number
  (local (defun g (x) (old x)))  ; all of the old representation

  ;; for the DEFISO applicability conditions:
  (defthm iso-image (implies (old x) (new (iso x))))
  (defthm osi-image (implies (new x) (old (osi x))))
  (defthm osi-of-iso (implies (old x) (equal (osi (iso x)) x)))
  (defthm iso-of-osi (implies (new x) (equal (iso (osi x)) x)))

  ;; for the termination of F:
  (defthm o-p-of-m (o-p (m x)))
  (defthm o<-of-m (implies (not (a x)) (o< (m (d x)) (m x))))

  ;; for the guard verification of F:
  (defthm g-of-d (implies (and (g x) (not (a x))) (g (d x))))

  ;; for the ISODATA applicability conditions:
  (defthm old-of-d (implies (and (old o) (not (a o))) (old (d o))))
  (defthm old-of-b (implies (and (old o) (a o)) (old (b o))))
  (defthm old-of-c (implies (and (old o) (old o1)) (old (c o o1))))
  (defthm old-when-g (implies (g x) (old x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; definition of F:

(defun f (x)
  (declare (xargs :guard (g x) :measure (m x)))
  (if (a x)
      (b x)
    (c x (f (d x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; establishment of the isomorphic mapping:

(defiso isomap old new iso osi)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; new isomorphic function, and accompanying theorem:

(apt::isodata f (((x :result) isomap)) :new-name f1)

(must-be-redundant
 (defun f1 (x)
   (declare (xargs :guard (and (new x) (g (osi x)))
                   :measure (m (osi x))
                   :ruler-extenders :all))
   (if (mbt$ (new x))
       (if (a (osi x))
           (iso (b (osi x)))
         (iso (c (osi x)
                 (osi (f1 (iso (d (osi x))))))))
     nil)))

(must-be-redundant
 (defthm f-~>-f1
   (implies (old x)
            (equal (f x)
                   (osi (f1 (iso x)))))))
