; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defarbrec")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function of the form shown in the documentation:

(must-succeed* ; unary
 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)
 (defarbrec f (x)
   (if (a x)
       (b x)
     (c x (f (d x))))))

(must-succeed* ; binary
 (defstub a (* *) => *)
 (defstub b (* *) => *)
 (defstub c (* * *) => *)
 (defstub dx (* *) => *)
 (defstub dy (* *) => *)
 (defarbrec f (x y)
   (if (a x y)
       (b x y)
     (c x y (f (dx x y) (dy x y))))))

(must-succeed* ; ternary
 (defstub a (* * *) => *)
 (defstub b (* * *) => *)
 (defstub c (* * * *) => *)
 (defstub dx (* * *) => *)
 (defstub dy (* * *) => *)
 (defstub dz (* * *) => *)
 (defarbrec f (x y z)
   (if (a x y z)
       (b x y z)
     (c x y z (f (dx x y z) (dy x y z) (dz x y z))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function of the form shown in the documentation,
; but with the IF branches flipped:

(must-succeed* ; unary
 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)
 (defarbrec f (x)
   (if (a x)
       (c x (f (d x)))
     (b x))))

(must-succeed* ; binary
 (defstub a (* *) => *)
 (defstub b (* *) => *)
 (defstub c (* * *) => *)
 (defstub dx (* *) => *)
 (defstub dy (* *) => *)
 (defarbrec f (x y)
   (if (a x y)
       (c x y (f (dx x y) (dy x y)))
     (b x y))))

(must-succeed* ; ternary
 (defstub a (* * *) => *)
 (defstub b (* * *) => *)
 (defstub c (* * * *) => *)
 (defstub dx (* * *) => *)
 (defstub dy (* * *) => *)
 (defstub dz (* * *) => *)
 (defarbrec f (x y z)
   (if (a x y z)
       (c x y z (f (dx x y z) (dy x y z) (dz x y z)))
     (b x y z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tail-recursive function with a base branch and then a recursive branch:

(must-succeed* ; unary
 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub d (*) => *)
 (defarbrec f (x)
   (if (a x)
       (b x)
     (f (d x)))))

(must-succeed* ; binary
 (defstub a (* *) => *)
 (defstub b (* *) => *)
 (defstub dx (* *) => *)
 (defstub dy (* *) => *)
 (defarbrec f (x y)
   (if (a x y)
       (b x y)
     (f (dx x y) (dy x y)))))

(must-succeed* ; ternary
 (defstub a (* * *) => *)
 (defstub b (* * *) => *)
 (defstub dx (* * *) => *)
 (defstub dy (* * *) => *)
 (defstub dz (* * *) => *)
 (defarbrec f (x y z)
   (if (a x y z)
       (b x y z)
     (f (dx x y z) (dy x y z) (dz x y z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; tail-recursive function with a recursive branch and then a base branch:

(must-succeed* ; unary
 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub d (*) => *)
 (defarbrec f (x)
   (if (a x)
       (f (d x))
     (b x))))

(must-succeed* ; binary
 (defstub a (* *) => *)
 (defstub b (* *) => *)
 (defstub dx (* *) => *)
 (defstub dy (* *) => *)
 (defarbrec f (x y)
   (if (a x y)
       (f (dx x y) (dy x y))
     (b x y))))

(must-succeed* ; ternary
 (defstub a (* * *) => *)
 (defstub b (* * *) => *)
 (defstub dx (* * *) => *)
 (defstub dy (* * *) => *)
 (defstub dz (* * *) => *)
 (defarbrec f (x y z)
   (if (a x y z)
       (f (dx x y z) (dy x y z) (dz x y z))
     (b x y z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function with two base branches and then a recursive branch:

(must-succeed* ; unary
 (defstub a1 (*) => *)
 (defstub a2 (*) => *)
 (defstub b1 (*) => *)
 (defstub b2 (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)
 (defarbrec f (x)
   (cond ((a1 x) (b1 x))
         ((a2 x) (b2 x))
         (t (c x (f (d x)))))))

(must-succeed* ; binary
 (defstub a1 (* *) => *)
 (defstub a2 (* *) => *)
 (defstub b1 (* *) => *)
 (defstub b2 (* *) => *)
 (defstub c (* * *) => *)
 (defstub dx (* *) => *)
 (defstub dy (* *) => *)
 (defarbrec f (x y)
   (cond ((a1 x y) (b1 x y))
         ((a2 x y) (b2 x y))
         (t (c x y (f (dx x y) (dy x y)))))))

(must-succeed* ; ternary
 (defstub a1 (* * *) => *)
 (defstub a2 (* * *) => *)
 (defstub b1 (* * *) => *)
 (defstub b2 (* * *) => *)
 (defstub c (* * * *) => *)
 (defstub dx (* * *) => *)
 (defstub dy (* * *) => *)
 (defstub dz (* * *) => *)
 (defarbrec f (x y z)
   (cond ((a1 x y z) (b1 x y z))
         ((a2 x y z) (b2 x y z))
         (t (c x y z (f (dx x y z) (dy x y z) (dz x y z)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function with a base branch, then a recursive branch, then a base branch:

(must-succeed* ; unary
 (defstub a1 (*) => *)
 (defstub a2 (*) => *)
 (defstub b1 (*) => *)
 (defstub b2 (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)
 (defarbrec f (x)
   (cond ((a1 x) (b1 x))
         ((a2 x) (c x (f (d x))))
         (t (b2 x)))))

(must-succeed* ; binary
 (defstub a1 (* *) => *)
 (defstub a2 (* *) => *)
 (defstub b1 (* *) => *)
 (defstub b2 (* *) => *)
 (defstub c (* * *) => *)
 (defstub dx (* *) => *)
 (defstub dy (* *) => *)
 (defarbrec f (x y)
   (cond ((a1 x y) (b1 x y))
         ((a2 x y) (c x y (f (dx x y) (dy x y))))
         (t (b2 x y)))))

(must-succeed* ; ternary
 (defstub a1 (* * *) => *)
 (defstub a2 (* * *) => *)
 (defstub b1 (* * *) => *)
 (defstub b2 (* * *) => *)
 (defstub c (* * * *) => *)
 (defstub dx (* * *) => *)
 (defstub dy (* * *) => *)
 (defstub dz (* * *) => *)
 (defarbrec f (x y z)
   (cond ((a1 x y z) (b1 x y z))
         ((a2 x y z) (c x y z (f (dx x y z) (dy x y z) (dz x y z))))
         (t (b2 x y z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; function with a recursive branch and then two base branches:

(must-succeed* ; unary
 (defstub a1 (*) => *)
 (defstub a2 (*) => *)
 (defstub b1 (*) => *)
 (defstub b2 (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)
 (defarbrec f (x)
   (cond ((a1 x) (c x (f (d x))))
         ((a2 x) (b1 x))
         (t (b2 x)))))

(must-succeed* ; binary
 (defstub a1 (* *) => *)
 (defstub a2 (* *) => *)
 (defstub b1 (* *) => *)
 (defstub b2 (* *) => *)
 (defstub c (* * *) => *)
 (defstub dx (* *) => *)
 (defstub dy (* *) => *)
 (defarbrec f (x y)
   (cond ((a1 x y) (c x y (f (dx x y) (dy x y))))
         ((a2 x y) (b1 x y))
         (t (b2 x y)))))

(must-succeed* ; ternary
 (defstub a1 (* * *) => *)
 (defstub a2 (* * *) => *)
 (defstub b1 (* * *) => *)
 (defstub b2 (* * *) => *)
 (defstub c (* * * *) => *)
 (defstub dx (* * *) => *)
 (defstub dy (* * *) => *)
 (defstub dz (* * *) => *)
 (defarbrec f (x y z)
   (cond ((a1 x y z) (c x y z (f (dx x y z) (dy x y z) (dz x y z))))
         ((a2 x y z) (b1 x y z))
         (t (b2 x y z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the FN input:

;; not a symbol:
(must-fail (defarbrec 3 (x) x) :with-output-off nil)
(must-fail (defarbrec "f" (x) x) :with-output-off nil)

;; in the main Lisp package:
(must-fail (defarbrec cons (x) x) :with-output-off nil)

;; keyword:
(must-fail (defarbrec :g (x) x) :with-output-off nil)

;; not new:
(must-fail (defarbrec len (x) x) :with-output-off nil)
(must-succeed*
 (defun g (x) x)
 (must-fail (defarbrec g (x) x) :with-output-off nil)
 :with-output-off nil)

;; determines the name of the new function:
(must-succeed*
 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)
 (assert! (not (function-namep 'f (w state))))
 (defarbrec f (x)
   (if (a x)
       (b x)
     (c x (f (d x)))))
 (assert! (logic-function-namep 'f (w state)))
 :with-output-off nil)

;; multiple results:
(must-fail
 (defarbrec f (x y)
   (mv x y))
 :with-output-off nil)

;; stobjs:
(must-fail
 (defarbrec f (state)
   state)
 :with-output-off nil)

;; not recursive:
(must-fail
 (defarbrec f (x)
   x)
 :with-output-off nil)

;; multiple recursive calls:
(must-fail
 (defarbrec f (x)
   (if (atom x)
       x
     (cons (f (car x)) (f (cdr x)))))
 :with-output-off nil)

;; multiple recursive calls:
(must-fail
 (defarbrec g (x)
   (list x (g (car x)) (g (cdr x))))
 :with-output-off nil)

;; calls program-mode function:
(must-succeed*
 (defun h (x)
   (declare (xargs :mode :program))
   x)
 (must-fail
  (defarbrec f (x)
    (if (h x)
        (f (car x))
      x))
  :with-output-off nil)
 :with-output-off nil)

;; determines the source function:
(must-succeed*
 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)
 (defarbrec f (x)
   (if (a x)
       (b x)
     (c x (f (d x)))))
 (assert-equal (ubody 'f (w state))
               '(if (f-terminates x)
                    (if (a x)
                        (b x)
                      (c x (f (d x))))
                  ':nonterminating))
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :UPDATE-NAMES input:

(must-succeed* ; single

 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)

 ;; not a NIL-terminated list of symbols:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names 4/5)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (1 2 3))
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names upd)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (upd 3))
  :with-output-off nil)

 ;; duplicates:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (upd upd))
  :with-output-off nil)

 ;; wrong number:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (upd upd2))
  :with-output-off nil)

 ;; in Common Lisp package:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (cons))
  :with-output-off nil)

 ;; keyword:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (:upd))
  :with-output-off nil)

 ;; not new:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (len))
  :with-output-off nil)
 (must-succeed*
  (defun g (x) x)
  (must-fail
   (defarbrec f (x)
     (if (a x)
         (b x)
       (c x (f (d x))))
     :update-names (g))
   :with-output-off nil)
  :with-output-off nil)

 ;; same as the main function:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (f))
  :with-output-off nil)

 ;; determines the iterated argument update function:
 (must-succeed*
  (assert! (not (function-namep 'upd (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (upd))
  (assert! (function-namep 'upd (w state)))
  :with-output-off nil)

 ;; default:
 (must-succeed*
  (assert! (not (function-namep 'f-x* (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  (assert! (function-namep 'f-x* (w state)))
  :with-output-off nil)

 ;; explicit default:
 (must-succeed*
  (assert! (not (function-namep 'f-x* (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names nil)
  (assert! (function-namep 'f-x* (w state)))
  :with-output-off nil)

 :with-output-off nil)

(must-succeed* ; multiple

 (defstub a (* *) => *)
 (defstub b (* *) => *)
 (defstub c (* * *) => *)
 (defstub dx (* *) => *)
 (defstub dy (* *) => *)

 ;; not a NIL-terminated list of symbols:
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names 4/5)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (1 2 3))
  :with-output-off nil)
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names upd)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (upd 3))
  :with-output-off nil)

 ;; duplicates:
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (upd upd upd2))
  :with-output-off nil)

 ;; wrong number:
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (upd))
  :with-output-off nil)
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (upd upd2 upd3))
  :with-output-off nil)

 ;; in Common Lisp package:
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (upd cons))
  :with-output-off nil)
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (cons upd))
  :with-output-off nil)

 ;; keyword:
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (:upd upd))
  :with-output-off nil)
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (upd :upd))
  :with-output-off nil)

 ;; not new:
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (len upd))
  :with-output-off nil)
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (upd len))
  :with-output-off nil)
 (must-succeed*
  (defun g (x) x)
  (must-fail
   (defarbrec f (x y)
     (if (a x y)
         (b x y)
       (c x y (f (dx x y) (dy x y))))
     :update-names (g upd))
   :with-output-off nil)
  (must-fail
   (defarbrec f (x y)
     (if (a x y)
         (b x y)
       (c x y (f (dx x y) (dy x y))))
     :update-names (upd g))
   :with-output-off nil)
  :with-output-off nil)

 ;; same as the main function:
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (f upd))
  :with-output-off nil)
 (must-fail
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (upd f))
  :with-output-off nil)

 ;; determines the iterated argument update function:
 (must-succeed*
  (assert! (not (function-namep 'updx (w state))))
  (assert! (not (function-namep 'updy (w state))))
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names (updx updy))
  (assert! (function-namep 'updx (w state)))
  (assert! (function-namep 'updy (w state)))
  :with-output-off nil)

 ;; default:
 (must-succeed*
  (assert! (not (function-namep 'f-x* (w state))))
  (assert! (not (function-namep 'f-y* (w state))))
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y)))))
  (assert! (function-namep 'f-x* (w state)))
  (assert! (function-namep 'f-y* (w state)))
  :with-output-off nil)

 ;; explicit default:
 (must-succeed*
  (assert! (not (function-namep 'f-x* (w state))))
  (assert! (not (function-namep 'f-y* (w state))))
  (defarbrec f (x y)
    (if (a x y)
        (b x y)
      (c x y (f (dx x y) (dy x y))))
    :update-names nil)
  (assert! (function-namep 'f-x* (w state)))
  (assert! (function-namep 'f-y* (w state)))
  :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :TERMINATES-NAME input:

(must-succeed*

 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)

 ;; not a symbol:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name #\u)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name (term))
  :with-output-off nil)

 ;; in Common Lisp package:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name cons)
  :with-output-off nil)

 ;; keyword:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name :term)
  :with-output-off nil)

 ;; not new:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name len)
  :with-output-off nil)
 (must-succeed*
  (defun g (x) x)
  (must-fail
   (defarbrec f (x)
     (if (a x)
         (b x)
       (c x (f (d x))))
     :terminates-name g)
   :with-output-off nil)
  :with-output-off nil)
 (must-succeed*
  (defun g-witness (x) x)
  (must-fail
   (defarbrec f (x)
     (if (a x)
         (b x)
       (c x (f (d x))))
     :terminates-name g)
   :with-output-off nil)
  :with-output-off nil)
 (must-succeed*
  (defun g-suff (x) x)
  (must-fail
   (defarbrec f (x)
     (if (a x)
         (b x)
       (c x (f (d x))))
     :terminates-name g)
   :with-output-off nil)
  :with-output-off nil)

 ;; same as the main function:
 (must-fail
  (defarbrec term (x)
    (if (a x)
        (b x)
      (c x (term (d x))))
    :terminates-name term)
  :with-output-off nil)

 ;; same as iterated argument update function:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name f-x*)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))) :update-names (term)
      :terminates-name term)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))) :update-names (term-witness)
      :terminates-name term)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))) :update-names (term-suff)
      :terminates-name term)
  :with-output-off nil)

 ;; determines the termination testing predicate:
 (must-succeed*
  (assert! (not (function-namep 'term (w state))))
  (assert! (not (function-namep 'term-witness (w state))))
  (assert! (not (theorem-namep 'term-suff (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name term)
  (assert! (function-namep 'term (w state)))
  (assert! (function-namep 'term-witness (w state)))
  (assert! (theorem-namep 'term-suff (w state)))
  :with-output-off nil)

 ;; default:
 (must-succeed*
  (assert! (not (function-namep 'f-terminates (w state))))
  (assert! (not (function-namep 'f-terminates-witness (w state))))
  (assert! (not (theorem-namep 'f-terminates-suff (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  (assert! (function-namep 'f-terminates (w state)))
  (assert! (function-namep 'f-terminates-witness (w state)))
  (assert! (theorem-namep 'f-terminates-suff (w state)))
  :with-output-off nil)

 ;; explicit default:
 (must-succeed*
  (assert! (not (function-namep 'f-terminates (w state))))
  (assert! (not (function-namep 'f-terminates-witness (w state))))
  (assert! (not (theorem-namep 'f-terminates-suff (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name nil)
  (assert! (function-namep 'f-terminates (w state)))
  (assert! (function-namep 'f-terminates-witness (w state)))
  (assert! (theorem-namep 'f-terminates-suff (w state)))
  :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :MEASURE-NAME input:

(must-succeed*

 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)

 ;; not a symbol:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name "meas")
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name (meas))
  :with-output-off nil)

 ;; in Common Lisp package:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name cons)
  :with-output-off nil)

 ;; keyword:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name :meas)
  :with-output-off nil)

 ;; not new:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name len)
  :with-output-off nil)
 (must-succeed*
  (defun g (x) x)
  (must-fail
   (defarbrec f (x)
     (if (a x)
         (b x)
       (c x (f (d x))))
     :measure-name g)
   :with-output-off nil)
  :with-output-off nil)

 ;; same as the main function:
 (must-fail
  (defarbrec meas (x)
    (if (a x)
        (b x)
      (c x (meas (d x))))
    :measure-name meas)
  :with-output-off nil)

 ;; same as iterated argument update function:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name f-x*)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :update-names (meas)
    :measure-name meas)
  :with-output-off nil)

 ;; same as the termination testing predicate (or witness or rewrite rule):
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name f-terminates)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name meas
    :measure-name meas)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name meas
    :measure-name meas-witness)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :terminates-name meas
    :measure-name meas-suff)
  :with-output-off nil)

 ;; determines the measure function:
 (must-succeed*
  (assert! (not (function-namep 'meas (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name meas)
  (assert! (function-namep 'meas (w state)))
  :with-output-off nil)

 ;; default:
 (must-succeed*
  (assert! (not (function-namep 'f-measure (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  (assert! (function-namep 'f-measure (w state)))
  :with-output-off nil)

 ;; explicit default:
 (must-succeed*
  (assert! (not (function-namep 'f-measure (w state))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :measure-name nil)
  (assert! (function-namep 'f-measure (w state)))
  :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :NONTERMINATING input:

(must-succeed*

 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)

 ;; not a valid term:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :nonterminating (len x x))
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :nonterminating (ggggg x))
  :with-output-off nil)

 ;; extra free variables:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :nonterminating (cons x y))
  :with-output-off nil)

 ;; not in logic mode:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :nonterminating (f 0))
  :with-output-off nil)
 (must-succeed*
  (defun g (x) (declare (xargs :mode :program)) x)
  (must-fail
   (defarbrec f (x)
     (if (a x)
         (b x)
       (c x (f (d x))))
     :nonterminating (g x))
   :with-output-off nil)
  :with-output-off nil)

 ;; multiple results:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :nonterminating (mv 1 2))
  :with-output-off nil)

 ;; stobjs:
 (must-succeed*
  (defstobj s)
  (set-irrelevant-formals-ok t)
  (must-fail
   (defarbrec g (x s)
     (if (a x)
         (b x)
       (c x (g (d x) s)))
     :nonterminating s)
   :with-output-off nil)
  :with-output-off nil)

 ;; determines the nonterminating value:
 (must-succeed*
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :nonterminating (cons x x))
  (defthm check-nonterminating
    (implies (not (f-terminates x))
             (equal (f x) (cons x x))))
  :with-output-off nil)

 ;; default:
 (must-succeed*
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  (defthm check-nonterminating
    (implies (not (f-terminates x))
             (equal (f x)
                    :nonterminating)))
  :with-output-off nil)

 ;; explicit default:
 (must-succeed*
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :nonterminating :nonterminating)
  (defthm check-nonterminating
    (implies (not (f-terminates x))
             (equal (f x)
                    :nonterminating)))
  :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :PRINT input:

(must-succeed*

 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)

 ;; not NIL, :ERROR, :RESULT, or :ALL:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print 44)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :nil)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print "ALL")
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print (:result :submit))
  :with-output-off nil)

 ;; default:
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  :with-output-off nil)

 ;; print nothing:
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print nil)
  :with-output-off nil)

 ;; print errors:
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :error)
  :with-output-off nil)

 ;; print result:
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :result)
  :with-output-off nil)

 ;; print everything:
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :all)
  :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test the :SHOW-ONLY input:

(must-succeed*

 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)

 ;; not T or NIL:
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only 't)
  :with-output-off nil)
 (must-fail
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only :nil)
  :with-output-off nil)

 ;; default:
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))))

 ;; only show expansion (ignore :PRINT):
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only t))
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print nil :show-only t))
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :error :show-only t))
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :result :show-only t))
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :all :show-only t))

 ;; submit expansion:
 (must-succeed
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only nil))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test redundancy:

(must-succeed*

 (defstub a (*) => *)
 (defstub b (*) => *)
 (defstub c (* *) => *)
 (defstub d (*) => *)

 ;; not recorded when :SHOW-ONLY is T:
 (must-succeed*
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only t)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))) ; not redundant
  :with-output-off nil)

 ;; call recorded without :PRINT or :SHOW-ONLY:
 (must-succeed*
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  ;; redundant:
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :all)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only t)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only nil)
  :with-output-off nil)

 ;; call recorded with :PRINT:
 (must-succeed*
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :error)
  ;; redundant:
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :all)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only t)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only nil)
  :with-output-off nil)

 ;; call recorded with :SHOW-ONLY (NIL):
 (must-succeed*
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only nil)
  ;; redundant:
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :all)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only t)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only nil)
  :with-output-off nil)

 ;; call recorded with :SHOW-ONLY (NIL) and :PRINT:
 (must-succeed*
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print nil :show-only nil)
  ;; redundant:
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x)))))
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :print :all)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only t)
  (defarbrec f (x)
    (if (a x)
        (b x)
      (c x (f (d x))))
    :show-only nil)
  :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; factorial example:

(must-succeed*
 (defarbrec fact (n)
   (if (equal n 0)
       1
     (* n (fact (1- n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; paradox example:

(must-succeed*
 (set-irrelevant-formals-ok t)
 (defarbrec paradox (x)
   (1+ (paradox x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; indeterminate example:

(must-succeed*
 (set-irrelevant-formals-ok t)
 (defarbrec indet (x)
   ;; without (CAR (LIST ...)), ACL2 cannot infer the output signature:
   (car (list (indet x)))))
