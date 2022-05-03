; ACL2 2017 Workshop Paper on SIMPLIFY-DEFUN - Section 2.2 Example
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains full details for the example in Section 2.2
; of the ACL2 2017 Workshop paper on SIMPLIFY-DEFUN,
; "A Versatile, Sound Tool for Simplifying Definitions"
; by A. Coglio, M. Kaufmann, and E. W. Smith.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "simplify-defun")

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The recognizer, conversion, and operations used in the example
; are introduced as constrained functions,
; to make clear which properties the example relies on.

(encapsulate
  (((int32p *) => *)
   ((int32 *) => * :formals (i) :guard (signed-byte-p 32 i))
   ((int *) => * :formals (u) :guard (int32p u))
   ((add32 * *) => * :formals (u v) :guard (and (int32p u) (int32p v)))
   ((sub32 * *) => * :formals (u v) :guard (and (int32p u) (int32p v)))
   ((mul32 * *) => * :formals (u v) :guard (and (int32p u) (int32p v)))
   ((lte32 * *) => * :formals (u v) :guard (and (int32p u) (int32p v)))
   ((gte32 * *) => * :formals (u v) :guard (and (int32p u) (int32p v))))

  (local (include-book "ihs/basic-definitions" :dir :system))

  ;; For witnessing the constrained functions,
  ;; we represent two's complement 32-bit integers
  ;; as ACL2 integers in [-2^31,2^31).

  (local (defun int32p (u)
           (signed-byte-p 32 u)))

  (local (defun int32 (i)
           (logext 32 i)))

  (local (defun int (u)
           (ifix u)))

  (local (defun add32 (u v)
           (int32 (+ (int u) (int v)))))

  (local (defun sub32 (u v)
           (int32 (- (int u) (int v)))))

  (local (defun mul32 (u v)
           (int32 (* (int u) (int v)))))

  (local (defun lte32 (u v)
           (<= (int u) (int v))))

  (local (defun gte32 (u v)
           (>= (int u) (int v))))

  ;; The following theorems are the only properties
  ;; that the example relies on.

  (defthm int32p-of-int32
    (int32p (int32 i)))

  (defthm integerp-of-int
    (integerp (int u))
    :rule-classes :type-prescription)

  (defthm int-of-int32
    (implies (signed-byte-p 32 x)
             (equal (int (int32 x))
                    x)))

  (defthmd add32-to-+
    (equal (add32 u v)
           (int32 (+ (int u) (int v)))))

  (defthmd sub32-to--
    (equal (sub32 u v)
           (int32 (- (int u) (int v)))))

  (defthmd mul32-to-*
    (equal (mul32 u v)
           (int32 (* (int u) (int v)))))

  (defthmd lte32-to-<=
    (equal (lte32 u v)
           (<= (int u) (int v))))

  (defthmd gte32-to->=
    (equal (gte32 u v)
           (>= (int u) (int v)))))

; It is convenient to group the operation rewriting rules.

(deftheory int32-ops-to-int-ops
  '(add32-to-+
    sub32-to--
    mul32-to-*
    lte32-to-<=
    gte32-to->=)
  :redundant-okp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The details of drawing a point on the screen are unimportant,
; so we introduce a disabled function to represent that.
; Since it is disabled, the example does not depend on its definition.

(defund drawpoint (x y screen)
  (declare (xargs :guard (and (int32p x) (int32p y))))
  (cons (list x y) screen))

; Precondition of the Java method.

(defun precond (a b)
  (declare (xargs :guard t))
  (and (int32p a)
       (int32p b)
       (<= 0 (int b))
       (<= (int b) (int a))
       (<= (int a) 1000000)))

; Invariant of the Java loop.
; This invariant is adequate for the example,
; but other invariants would work too.

(defun invar (a b x y d)
  (declare (xargs :guard t))
  (and (precond a b)
       (int32p x)
       (int32p y)
       (int32p d)
       (<= 0 (int x))
       (<= (int x) (1+ (int a)))
       (<= 0 (int y))
       (<= (int y) (int x))
       (<= -2000000 (int d))
       (<= (int d) 2000000)))

; Java loop.
; The loop terminates because the distance between x and a decreases.
; Termination is proved by turning the bounded integer operations
; to their unbounded counterparts and then doing arithmetic reasoning.
; The guards are verified by turning the bounded integer operations
; to their unbounded counterparts and then doing arithmetic reasoning.
; The verification of the guards implies the preservation of the loop invariant.

(defun drawline-loop (a b x y d screen)
  (declare
   (xargs :guard (invar a b x y d)
          :guard-hints (("Goal" :in-theory (enable int32-ops-to-int-ops)))
          :measure (nfix (- (1+ (int a)) (int x)))
          :hints (("Goal" :in-theory (enable int32-ops-to-int-ops)))))
  (if (invar a b x y d)
      (if (not (lte32 x a))
          screen
        (drawline-loop a
                       b
                       (add32 x (int32 1))
                       (if (gte32 d (int32 0))
                           (add32 y (int32 1))
                         y)
                       (if (gte32 d (int32 0))
                           (add32 d (mul32 (int32 2) (sub32 b a)))
                         (add32 d (mul32 (int32 2) b)))
                       (drawpoint x y screen)))
    :undefined))

; Java method.
; The guards are verified by turning the bounded integer operations
; to their unbounded counterparts and then doing arithmetic reasoning.
; The verification of the guards implies
; the establishment of the loop invariant.

(defun drawline (a b screen)
  (declare
   (xargs :guard (precond a b)
          :guard-hints (("Goal" :in-theory (enable int32-ops-to-int-ops)))))
  (if (precond a b)
      (drawline-loop a
                     b
                     (int32 0)
                     (int32 0)
                     (sub32 (mul32 (int32 2) b) a)
                     screen)
    :undefined))

; Use the tool to simplify the loop function.

(simplify-defun drawline-loop
                :simplify-body (if _ @ _)
                :enable int32-ops-to-int-ops)

; Use the tool to simplify the method function.

(simplify-defun drawline
                :simplify-body (if _ @ _)
                :enable int32-ops-to-int-ops)

; The resulting functions use only unbounded integer operations.
; The remaining INT conversions at the variable leaves of the expressions
; and the remaining INT32 conversions at the roots of the expressions
; can be eliminated via APT's isomorphic data transformation
; (not shown here).
; The following two events are redundant,
; testing that the functions generated by SIMPLIFY-DEFUN
; have the expected form.

(DEFUN DRAWLINE-LOOP{1} (A B X Y D SCREEN)
  (DECLARE (XARGS :NORMALIZE NIL
                  :GUARD (INVAR A B X Y D)
                  :MEASURE (NFIX (+ (+ 1 (INT A)) (- (INT X))))))
  (IF
   (INVAR A B X Y D)
   (IF (< (INT A) (INT X))
       SCREEN
       (DRAWLINE-LOOP{1} A B (INT32 (+ 1 (INT X)))
                         (IF (< (INT D) 0)
                             Y (INT32 (+ 1 (INT Y))))
                         (IF (< (INT D) 0)
                             (INT32 (+ (INT D) (* 2 (INT B))))
                             (INT32 (+ (INT D)
                                       (* 2 (INT B))
                                       (* -2 (INT A)))))
                         (DRAWPOINT X Y SCREEN)))
   :UNDEFINED))

(DEFUN DRAWLINE{1} (A B SCREEN)
  (DECLARE (XARGS :NORMALIZE NIL
                  :GUARD (PRECOND A B)))
  (IF (PRECOND A B)
      (DRAWLINE-LOOP{1} A B (INT32 0)
                        (INT32 0)
                        (INT32 (+ (- (INT A)) (* 2 (INT B))))
                        SCREEN)
      :UNDEFINED))
