; A formalization of groups
;
; Copyright (C) 2016-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Formalization of group theory, using encapsulate

(include-book "kestrel/utilities/defcalculation" :dir :system)

(encapsulate
  ((pred (x) t)  ;; recognize an element of the set
   (dot (x y) t) ;; the group operation, often represented as a dot
   (id () t)     ;; the identity element (a 0-ary function)
   (inv (x) t))  ;; the inverse operation

  ;; We'll use booleans and XOR as a simple witness:
  (local (defun pred (x) (booleanp x)))
  ; boolean xor:
  (local (defun dot (x y) (if x (not y) y)))
  (local (defun id () nil))
  ;; bool-fix:
  (local (defun inv (x) (if x t nil)))

  ;; The set is closed under the group operation:
  (defthm closure-for-dot
    (implies (and (pred x)
                  (pred y))
             (pred (dot x y))))

  (defthm associativity
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equal (dot (dot x y) z)
                    (dot x (dot y z)))))

  ;; The identity element is in the set:
  (defthm id-in-set
    (pred (id)))

  (defthm left-identity
    (implies (pred x)
             (equal (dot (id) x)
                    x)))

  ;; The inverse is in the set:
  (defthm closure-for-inv
    (implies (pred x)
             (pred (inv x))))

  (defthm left-inverse
    (implies (pred x)
             (equal (dot (inv x) x)
                    (id)))))

;; Show that id is also a right identity:
(defcalculation right-identity
  (dot x (id))
  (= (dot (dot (id) x) (id)))
  (= (dot (dot (inv (inv x)) (inv x))
          (dot x
               (dot (inv x) x))))
  (= (dot (inv (inv x))
          (dot (dot (inv x) x)
               (dot (inv x) x)))
     :hints (("Goal" :in-theory (disable LEFT-INVERSE LEFT-IDENTITY))))
  (= (dot (inv (inv x))
          (dot (inv x) x)))
  (= (dot (dot (inv (inv x))
               (inv x))
          x)
     :hints (("Goal" :in-theory (disable LEFT-INVERSE LEFT-IDENTITY))))
  (= x)
  :assumptions ((pred x)))

;redundant
(defthm right-identity
  (implies (pred x)
           (equal (dot x (id))
                  x)))

;; Show that inv is also a right inverse:
(defcalculation right-inverse
  (dot x (inv x))
  (= (dot (id)                        (dot x (inv x))))
  (= (dot (dot (inv (inv x)) (inv x)) (dot x (inv x))))
  (= (dot (inv (inv x)) (dot (dot (inv x) x) (inv x)))
     :hints (("Goal" :in-theory (disable LEFT-INVERSE LEFT-IDENTITY)))) ;re-associate
  (= (dot (inv (inv x)) (dot (id)            (inv x))))
  (= (dot (inv (inv x)) (inv x)))
  (= (id))
  :assumptions ((pred x)))

;redundant
(defthm right-inverse
  (implies (pred x)
           (equal (dot x (inv x))
                  (id))))
