; Coglio-Westfold's ACL2-2020 Paper Examples
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "isodata")
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "workshops/2017/coglio-kaufmann-smith/support/simplify-defun" :dir :system)

(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains the loop example in Section 4.2
; of the paper "Isomorphic Data Type Transformations"
; by A. Coglio and S. Westfold, published at the ACL2-2020 Workshop.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function to be applied repeatedly:

(defstub h (*) => *)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; loop to apply H a number of times, counting down:

(defun applyn (x n)
  (declare (xargs :guard (and (natp n) (<= n 10))))
  (if (zp n)
      x
    (h (applyn x (1- n)))))

; loop caller to apply H ten times:

(defun applyten (x)
  (declare (xargs :guard t))
  (applyn x 10))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; change the loop direction to count up:

(apt::isodata applyn
              ((n ((lambda (n) (and (natp n) (<= n 10)))
                   (lambda (n) (and (natp n) (<= n 10)))
                   (lambda (n) (- 10 n))
                   (lambda (n) (- 10 n)))))
              :new-name applyn0)

(must-be-redundant
 (defun applyn0 (x n)
   (declare (xargs :well-founded-relation o<
                   :measure (acl2-count (binary-+ '10 (unary-- n)))
                   :ruler-extenders :all
                   :guard (and (natp n)
                               (<= n 10)
                               (natp (+ 10 (- n)))
                               (<= (+ 10 (- n)) 10))))
   (if (mbt$ (and (natp n) (<= n 10)))
       (if (zp (+ 10 (- n)))
           x
         (h (applyn0 x (+ 10 (- (+ -1 10 (- n)))))))
     nil)))

; simplify the arithmetic in the new loop:

(simplify-defun applyn0 :simplify-guard t :new-name applyn1)

(must-be-redundant
 (defun applyn1 (x n)
   (declare (xargs :normalize nil
                   :ruler-extenders :all
                   :guard (and (natp n)
                               (not (< 10 n))
                               (not (< 10 (+ 10 (- n)))))
                   :measure (acl2-count (+ 10 (- n)))))
   (if (mbt (and (natp n) (not (< 10 n))))
       (if (< n 10)
           (h (applyn1 x (+ 1 n)))
         x)
     nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; rewrite the loop caller to call the re-indexed loop:

(simplify-defun applyten :new-name applyten1 :enable applyn-to-applyn0)

(must-be-redundant
 (defun applyten1 (x)
   (declare (xargs :normalize nil :guard t))
   (applyn1 x 0)))
