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

; This file contains the integers example in Section 4.1
; of the paper "Isomorphic Data Type Transformations"
; by A. Coglio and S. Westfold, published at the ACL2-2020 Workshop.

; This file extends the example in
; [books]/workshops/2017/coglio-kaufmann-smith/support/example-integers.lisp
; with the use of ISODATA.

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

  (local (include-book "arithmetic-5/top" :dir :system))

  ;; For witnessing the constrained functions,
  ;; we represent two's complement 32-bit integers
  ;; as ACL2 integers in [-2^31,2^31).

  (local (defun int32p (u) (signed-byte-p 32 u)))
  (local (defun int32 (i) (logext 32 i)))
  (local (defun int (u) (ifix u)))
  (local (defun add32 (u v) (int32 (+ (int u) (int v)))))
  (local (defun sub32 (u v) (int32 (- (int u) (int v)))))
  (local (defun mul32 (u v) (int32 (* (int u) (int v)))))
  (local (defun lte32 (u v) (<= (int u) (int v))))
  (local (defun gte32 (u v) (>= (int u) (int v))))

  ;; The following theorems are the only properties
  ;; that the example relies on.

  (defthm int32p-of-int32
    (int32p (int32 i)))

  (defthm integerp-of-int
    (integerp (int u))
    :rule-classes :type-prescription)

  (defthm lower-bound-of-int
    (implies (int32p u)
             (<= (- (expt 2 31)) (int u)))
    :rule-classes :linear)

  (defthm upper-bound-of-int
    (implies (int32p u)
             (<= (int u) (1- (expt 2 31))))
    :rule-classes :linear)

  (defthm int-of-int32
    (implies (force (signed-byte-p 32 i))
             (equal (int (int32 i))
                    i)))

  (defthm int32-of-int
    (implies (int32p u)
             (equal (int32 (int u))
                    u)))

  (defthm int32p-of-add32
    (implies (and (int32p u)
                  (int32p v))
             (int32p (add32 u v)))
    :hints (("Goal" :in-theory (disable int32p int32))))

  (defthm int32p-of-sub32
    (implies (and (int32p u)
                  (int32p v))
             (int32p (sub32 u v)))
    :hints (("Goal" :in-theory (disable int32p int32))))

  (defthm int32p-of-mul32
    (implies (and (int32p u)
                  (int32p v))
             (int32p (mul32 u v)))
    :hints (("Goal" :in-theory (disable int32p int32))))

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

; This will be used in the simplification steps later.

(defthmd int-of-if
  (equal (int (if a b c))
         (if a (int b) (int c))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The details of drawing a point on the screen are unimportant,
; so we introduce an abstract function to represent that.

(defstub drawpoint (* * *) => *
  :formals (x y screen) :guard (and (int32p x) (int32p y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Precondition of the Java method.

(defun precondition (a b)
  (declare (xargs :guard t))
  (and (int32p a)
       (int32p b)
       (<= 0 (int b))
       (<= (int b) (int a))
       (<= (int a) 1000000)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Invariant of the Java loop.
; This invariant is adequate for the example,
; but other invariants would work too.

(defun invariant (a b x y d)
  (declare (xargs :guard t))
  (and (precondition a b)
       (int32p x)
       (int32p y)
       (int32p d)
       (<= 0 (int x))
       (<= (int x) (1+ (int a)))
       (<= 0 (int y))
       (<= (int y) (int x))
       (<= -2000000 (int d))
       (<= (int d) 2000000)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Java loop.
; The loop terminates because the distance between x and a decreases.
; Termination is proved by turning the bounded integer operations
; to their unbounded counterparts and then doing arithmetic reasoning.
; The guards are verified by turning the bounded integer operations
; to their unbounded counterparts and then doing arithmetic reasoning.
; The verification of the guards implies the preservation of the loop invariant.

(defun drawline-loop (a b x y d screen)
  (declare
   (xargs :guard (invariant a b x y d)
          :guard-hints (("Goal" :in-theory (enable int32-ops-to-int-ops)))
          :measure (nfix (- (1+ (int a)) (int x)))
          :hints (("Goal" :in-theory (enable int32-ops-to-int-ops)))))
  (if (invariant a b x y d)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Java method.
; The guards are verified by turning the bounded integer operations
; to their unbounded counterparts and then doing arithmetic reasoning.
; The verification of the guards implies
; the establishment of the loop invariant.

(defun drawline (a b screen)
  (declare
   (xargs :guard (precondition a b)
          :guard-hints (("Goal" :in-theory (enable int32-ops-to-int-ops)))))
  (if (precondition a b)
      (drawline-loop a
                     b
                     (int32 0)
                     (int32 0)
                     (sub32 (mul32 (int32 2) b) a)
                     screen)
    :undefined))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We change the representation of the loop function's arguments
; to be the (SIGNED-BYTE-P 32 ...) subset of the integers,
; instead of the (opaque) INT32P values.

(apt::isodata drawline-loop
              (((a b x y d) (int32p
                             (lambda (x) (signed-byte-p 32 x))
                             int
                             int32)))
              :untranslate t)

; This is the result,
; which adds an INT32 conversion in front of each transformed variable
; (excluding the initial wrapping test added by ISODATA),
; and also adds an INT conversion in front of each recursive call arguments
; (excluding the SCREEN argument, which is not transformed).
; Note the terms (INT (INT32 ...)), amenable to simplification.

(must-be-redundant
 (DEFUN DRAWLINE-LOOP{1} (A B X Y D SCREEN)
   (DECLARE (XARGS :WELL-FOUNDED-RELATION O<
                   :MEASURE (NFIX (BINARY-+ (BINARY-+ '1 (INT (INT32 A)))
                                            (UNARY-- (INT (INT32 X)))))
                   :RULER-EXTENDERS :ALL
                   :GUARD (AND (SIGNED-BYTE-P 32 A)
                               (SIGNED-BYTE-P 32 B)
                               (SIGNED-BYTE-P 32 X)
                               (SIGNED-BYTE-P 32 Y)
                               (SIGNED-BYTE-P 32 D)
                               (INVARIANT (INT32 A)
                                          (INT32 B)
                                          (INT32 X)
                                          (INT32 Y)
                                          (INT32 D)))
                   :VERIFY-GUARDS T))
   (IF
    (MBT$ (AND (SIGNED-BYTE-P 32 A)
               (SIGNED-BYTE-P 32 B)
               (SIGNED-BYTE-P 32 X)
               (SIGNED-BYTE-P 32 Y)
               (SIGNED-BYTE-P 32 D)))
    (IF
     (INVARIANT (INT32 A)
                (INT32 B)
                (INT32 X)
                (INT32 Y)
                (INT32 D))
     (IF (NOT (LTE32 (INT32 X) (INT32 A)))
         SCREEN
         (DRAWLINE-LOOP{1} (INT (INT32 A))
                           (INT (INT32 B))
                           (INT (ADD32 (INT32 X) (INT32 1)))
                           (INT (IF (GTE32 (INT32 D) (INT32 0))
                                    (ADD32 (INT32 Y) (INT32 1))
                                    (INT32 Y)))
                           (INT (IF (GTE32 (INT32 D) (INT32 0))
                                    (ADD32 (INT32 D)
                                           (MUL32 (INT32 2)
                                                  (SUB32 (INT32 B) (INT32 A))))
                                    (ADD32 (INT32 D)
                                           (MUL32 (INT32 2) (INT32 B)))))
                           (DRAWPOINT (INT32 X) (INT32 Y) SCREEN)))
     :UNDEFINED)
    NIL)))

(must-be-redundant
 (DEFTHM DRAWLINE-LOOP-TO-DRAWLINE-LOOP{1}
   (IMPLIES (AND (INT32P A)
                 (INT32P B)
                 (INT32P X)
                 (INT32P Y)
                 (INT32P D))
            (EQUAL (DRAWLINE-LOOP A B X Y D SCREEN)
                   (DRAWLINE-LOOP{1} (INT A)
                                     (INT B)
                                     (INT X)
                                     (INT Y)
                                     (INT D)
                                     SCREEN)))))

; Now we apply the operations' rewrite rules,
; and we also simplify the terms (INT (INT32 ...)),
; more of which are temporarily produced by the operations' rewrite rules.

(simplify-defun drawline-loop{1}
                :enable (int32-ops-to-int-ops
                         int-of-if)
                :theorem-name drawline-loop{1}-to-drawline-loop{2})

; This is the result, whose body,
; except for the DRAWPOINT call
; (which could be transformed separately in a more full-fledged example),
; no longer uses the bounded integer types or operations.

(must-be-redundant
 (DEFUN DRAWLINE-LOOP{2} (A B X Y D SCREEN)
   (DECLARE
    (XARGS
     :NORMALIZE NIL
     :RULER-EXTENDERS :ALL
     :GUARD (AND (SIGNED-BYTE-P 32 A)
                 (SIGNED-BYTE-P 32 B)
                 (SIGNED-BYTE-P 32 X)
                 (SIGNED-BYTE-P 32 Y)
                 (SIGNED-BYTE-P 32 D)
                 (INVARIANT (INT32 A)
                            (INT32 B)
                            (INT32 X)
                            (INT32 Y)
                            (INT32 D)))
     :MEASURE (NFIX (+ (+ 1 (INT (INT32 A)))
                       (- (INT (INT32 X)))))))
   (IF (AND (AND (INTEGERP A)
                 (NOT (< A -2147483648))
                 (< A 2147483648))
            (AND (INTEGERP B)
                 (NOT (< B -2147483648))
                 (< B 2147483648))
            (AND (INTEGERP X)
                 (NOT (< X -2147483648))
                 (< X 2147483648))
            (AND (INTEGERP Y)
                 (NOT (< Y -2147483648))
                 (< Y 2147483648))
            (INTEGERP D)
            (NOT (< D -2147483648))
            (< D 2147483648))
       (IF (AND (AND (NOT (< B 0))
                     (NOT (< A B))
                     (NOT (< 1000000 A)))
                (NOT (< X 0))
                (NOT (< (+ 1 A) X))
                (NOT (< Y 0))
                (NOT (< X Y))
                (NOT (< D -2000000))
                (NOT (< 2000000 D)))
           (IF (< A X)
               SCREEN
               (DRAWLINE-LOOP{2} A B (+ 1 X)
                                 (IF (< D 0) Y (+ 1 Y))
                                 (IF (< D 0)
                                     (+ D (* 2 B))
                                     (+ D (- (* 2 A)) (* 2 B)))
                                 (DRAWPOINT (INT32 X) (INT32 Y) SCREEN)))
           :UNDEFINED)
       NIL)))

(must-be-redundant
 (DEFTHM DRAWLINE-LOOP{1}-TO-DRAWLINE-LOOP{2}
   (EQUAL (DRAWLINE-LOOP{1} A B X Y D SCREEN)
          (DRAWLINE-LOOP{2} A B X Y D SCREEN))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We change the representation of the method function's arguments
; to be the (SIGNED-BYTE-P 32 ...) subset of the integers,
; instead of the (opaque) INT32P values,
; as done for the loop function.

(apt::isodata drawline
              (((a b) (int32p
                       (lambda (x) (signed-byte-p 32 x))
                       int
                       int32))))

; This is the result,
; which adds an INT32 conversion in front of each transformed variable
; (excluding the initial wrapping test added by ISODATA).
; There are no recursive calls here.

(must-be-redundant
 (DEFUN DRAWLINE{1} (A B SCREEN)
   (DECLARE (XARGS :GUARD (AND (SIGNED-BYTE-P 32 A)
                               (SIGNED-BYTE-P 32 B)
                               (PRECONDITION (INT32 A) (INT32 B)))
                   :VERIFY-GUARDS T))
   (IF (MBT$ (AND (SIGNED-BYTE-P 32 A)
                  (SIGNED-BYTE-P 32 B)))
       (IF (PRECONDITION (INT32 A) (INT32 B))
           (DRAWLINE-LOOP (INT32 A)
                          (INT32 B)
                          (INT32 0)
                          (INT32 0)
                          (SUB32 (MUL32 (INT32 2) (INT32 B))
                                 (INT32 A))
                          SCREEN)
           :UNDEFINED)
       NIL)))

(must-be-redundant
 (DEFTHM DRAWLINE-TO-DRAWLINE{1}
   (IMPLIES (AND (INT32P A) (INT32P B))
            (EQUAL (DRAWLINE A B SCREEN)
                   (DRAWLINE{1} (INT A) (INT B) SCREEN)))))

; Now we apply the operations' rewrite rules,
; and we also simplify the terms (INT (INT32 ...))
; that are temporarily produced by the operations' rewrite rules.
; The application of DRAWLINE-LOOP-TO-DRAWLINE-LOOP{1}
; also temporarily introduces terms (INT (INT32 ...)) here.

(simplify-defun drawline{1}
                :enable (int32-ops-to-int-ops
                         int-of-if
                         drawline-loop-to-drawline-loop{1})
                :theorem-name drawline{1}-to-drawline{2})

; This is the result, whose body
; no longer uses the bounded integer types or operations.

(must-be-redundant
 (DEFUN DRAWLINE{2} (A B SCREEN)
   (DECLARE
    (XARGS
     :NORMALIZE NIL
     :GUARD (AND (SIGNED-BYTE-P 32 A)
                 (SIGNED-BYTE-P 32 B)
                 (PRECONDITION (INT32 A) (INT32 B)))))
   (IF (AND (AND (INTEGERP A)
                 (NOT (< A -2147483648))
                 (< A 2147483648))
            (INTEGERP B)
            (NOT (< B -2147483648))
            (< B 2147483648))
       (IF (AND (NOT (< B 0))
                (NOT (< A B))
                (NOT (< 1000000 A)))
           (DRAWLINE-LOOP{2} A B 0 0 (+ (- A) (* 2 B))
                             SCREEN)
           :UNDEFINED)
       NIL)))

(must-be-redundant
 (DEFTHM DRAWLINE{1}-TO-DRAWLINE{2}
   (EQUAL (DRAWLINE{1} A B SCREEN)
          (DRAWLINE{2} A B SCREEN))))
