; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "pattern-matching-ext")

(assert-event
 (equal (ext-fdeposit-term '(f a (g a (h b) (h (f2 x y))) c)
                           '(2 3 1)
                           '(f3 y x))
        '(F A (G A (H B) (H (F3 Y X))) C)))

(assert-event
 (equal (ext-fdeposit-term

; (LET* ((Y U)
;        (Z (F2 Y C)))
;       (F1 (G Y Z (CONS Z Y)) Y))

         '((lambda (y c)
             ((lambda (z y) (f1 (g y z (cons z y)) y))
              (f2 y c)
              y))
           u
           c)
         '(0 0 1 3)
         'v)

; (LET* ((Y U)
;        (Z (F2 Y C)))
 ;      (F1 (G Y Z V) Y))

        '((LAMBDA (Y C V)
                  ((LAMBDA (Z Y V)
                           (F1 (G Y Z V) Y))
                   (F2 Y C)
                   Y V))
          U C V)))

; Test avoidance of capture.
#||
(LET* ((Y U) (Z (F2 Y C)))
      (F1 (G Y Z (CONS Z Y))
          Y))
==> {substitute [the global] Z for (CONS Z Y)}
(LET* ((Y U) (Z1 (F2 Y C)))
      (F1 (G Y Z1 Z) Y))
||#
(assert-event
 (equal (ext-fdeposit-term '((lambda (y c)
                               ((lambda (z y) (f1 (g y z (cons z y)) y))
                                (f2 y c)
                                y))
                             u
                             c)
                           '(0 0 1 3)
                           'z)
        '((LAMBDA (Y C Z)
                  ((LAMBDA (Z{1} Y Z) (F1 (G Y Z{1} Z) Y))
                   (F2 Y C)
                   Y Z))
          U C Z)))

; Test restoring of formals (while avoiding capture).
#||
(LET ((Y U)
      (Z (F2 U C)))
     (F1 (G Y Z (CONS Z Y))
         Y))
==> {substitute (H U (F2 U C)) for (G Y Z (CONS Z Y))}
(LET ((Y U)
      (Z (F2 U C)))
     (F1 (H Y Z)
         Y))
||#

(assert-event
 (equal (ext-fdeposit-term '((lambda (y z)
                               (f1 (g y z (cons z y))
                                   y))
                             u
                             (f2 u c))
                           '(0 1)
                           '(h u (f2 u c)))
        '((LAMBDA (Y Z)
                  (F1 (H Y Z)
                      Y))
          U
          (F2 U C))))

; A more complex test.

#||
ACL2 !>:trans (if (equal v (f1 x))
                  (let* ((x z)
                         (y (h x)))
                    (g v y))
                17)

(IF (EQUAL V (F1 X))
    ((LAMBDA (X V)
             ((LAMBDA (Y V) (G V Y)) (H X) V))
     Z V)
    '17)

=> *

ACL2 !>(let ((term '(IF (EQUAL V (F1 X))
			((LAMBDA (X V)
				 ((LAMBDA (Y V) (G V Y)) (H X) V))
			 Z V)
			'17))
	     (addr '(2 0 0))
	     (subterm '(G (F1 X) (H Z))))
	 (ext-fdeposit-term term addr subterm))
(IF (EQUAL V (F1 X))
    ((LAMBDA (X1 X)
             ((LAMBDA (Y X) (G (F1 X) Y)) (H X1) X))
     Z X)
    '17)
ACL2 !>(thm (equal (if (equal v (f1 x))
                       (let* ((x z)
                              (y (h x)))
                         (g v y))
                     17)
                   (IF (EQUAL V (F1 X))
                       (LET* ((X1 Z)
                              (Y (H X1)))
                             (G (F1 X) Y))
                       17)))
Goal'

Q.E.D.

Summary
Form:  ( THM ...)
Rules: ((:FAKE-RUNE-FOR-TYPE-SET NIL))
Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
Prover steps counted:  78

Proof succeeded.
ACL2 !>
||#

(assert-event
 (equal (let ((term '(IF (EQUAL V (F1 X))
                         ((LAMBDA (X V)
                                  ((LAMBDA (Y V) (G V Y)) (H X) V))
                          Z V)
                         '17))
              (addr '(2 0 0))
              (subterm '(G (F1 X) (H Z))))
          (ext-fdeposit-term term addr subterm))
        '(IF (EQUAL V (F1 X))
             ((LAMBDA (X{1} X)
                      ((LAMBDA (Y X) (G (F1 X) Y)) (H X{1}) X))
              Z X)
             '17)))

; Next we check that alpha-conversion can be avoided when possible.

(encapsulate
  ()

(defstub f (x) t)
(defun g (x) (f x))
(defstub h (x) t)

#||
 ACL2 !>:trans (let* ((x z)
                      (x (h x)))
                 (g x))

 ((LAMBDA (X) ((LAMBDA (X) (G X)) (H X)))
  Z)

 => *

 ACL2 !>
||#

(assert-event
 (equal (let ((term '((LAMBDA (X)
                              ((LAMBDA (X) (G X))
                               (H X)))
                      Z))
              (addr '(0 0))
              (subterm '(f (h z))))
          (ext-fdeposit-term term addr subterm))
        '((LAMBDA (X)
                  ((LAMBDA (X) (F X))
                   (H X)))
          Z)))
)

; Let's try to avoid generating terms that untranslate to (let nil ...).
; The following example is just like above, except we deposit a term with a
; fresh, global variable, not captured.

(assert-event
 (equal (let ((term '((LAMBDA (X)
                              ((LAMBDA (X) (G X))
                               (H X)))
                      Z))
              (addr '(0 0))
              (subterm '(g w)))
          (ext-fdeposit-term term addr subterm))
        '(G W)))

;;; Begin testing for ext-address-subterm-governors-lst

(defstub f1 (x) t)
(defstub f2 (x y) t)
(defstub f3 (x y z) t)
(defstub g1 (x) t)
(defstub g2 (x y) t)
(defstub g3 (x y z) t)
(defstub h1 (x) t)
(defstub h2 (x y) t)
(defstub h3 (x y z) t)
(defstub k1 (x) t)
(defstub k2 (x y) t)
(defstub k3 (x y z) t)

(defun remove-eq-duplicate-keys (alist)
  (declare (xargs :guard (symbol-alistp alist) :verify-guards nil))
  (cond ((endp alist) nil)
        ((assoc-eq (caar alist) (cdr alist))
         (cons (car alist)
               (remove1-assoc-eq (caar alist)
                                 (remove-eq-duplicate-keys (cdr alist)))))
        (t (cons (car alist)
                 (remove-eq-duplicate-keys (cdr alist))))))

(defthm symbol-alistp-remove-eq-duplicate-keys
  (implies (symbol-alistp alist)
           (symbol-alistp (remove-eq-duplicate-keys alist))))

(verify-guards remove-eq-duplicate-keys)

(defun remove-dup-bindings (lst)
  (cond ((endp lst) nil)
        (t (cons (let* ((val (car lst))
                        (addr (car val))
                        (subterm (cadr val))
                        (bindings (caddr val))
                        (governors+ (cdddr val)))
                   (list* addr
                          subterm
                          (remove-eq-duplicate-keys bindings)
                          governors+))
                 (remove-dup-bindings (cdr lst))))))

(defmacro run-easgl (untrans-pat term)
  `(let ((untrans-pat ',untrans-pat)
         (term ',term)
         (ctx 'my-top))
     (mv-let (erp val)
       (ext-address-subterm-governors-lst untrans-pat term ctx state)
       (cond (erp (mv erp val))
             (t (mv nil (remove-dup-bindings val)))))))

(defmacro test-easgl (untrans-pat term expected)
  `(assert-event
    (mv-let (erp val)
      (run-easgl ,untrans-pat ,term)
      (and (null erp)
           (equal val ',expected)))))

(defmacro fail-easgl (untrans-pat term)
  `(assert-event
    (mv-let (erp val)
      (run-easgl ,untrans-pat ,term)
      (declare (ignore val))
      erp)))

; This first batch of tests gives the same result if we call
; address-subterm-governors-lst instead of ext-address-subterm-governors-lst.

(test-easgl (f1 @)
            (f2 x (f1 x))
            (((2 1) ; address
              X     ; subterm matching (:@ ...)
              ()    ; bindings
              ;; governors
              )))

(test-easgl (if (f1 _x)
                (g1 (if (h1 (:@ a0)) _ (f2 y @)))
              _v)
            (if (f1 x0)
                (g1 (if (h1 a0) w0 (f2 y (k x))))
              v0)
            (((2 1 1 1) ; address
              A0        ; subterm matching (:@ ...)
              ()        ; bindings
              ;; governors
              (F1 X0))
             ((2 1 3 2) (K X) () (F1 X0) (NOT (H1 A0)))))

; Test as above, except fail because (:@ term) expects exact match of term.
(fail-easgl (if (f1 _x)
                (g1 (if (h1 (:@ a7)) _ (f2 y @)))
              _v)
            (if (f1 x0)
                (g1 (if (h1 a0) w0 (f2 y (k x))))
              v0))

(test-easgl (if (f1 _x)
                (g1 (if (h1 (:@ a0)) _ (f2 y @)))
              _v)
            (g1 (f2 a (if (f1 x0)
                          (g1 (if (h1 a0) w0 (f2 y (k x))))
                        v0)))
            (((1 2 2 1 1 1) ; address
              A0 ; subterm matching (:@ ...)
              () ; bindings
              ;; governors
              (F1 X0))
             ((1 2 2 1 3 2) ; address
              (K X) ; subterm matching (:@ ...)
              () ; bindings
              ;; governors
              (F1 X0)
              (NOT (H1 A0)))))

; Now let us try diving inside LET bindings.

#||
ACL2 !>:trans (if (equal v (f1 x))
                  (let* ((x z)
                         (y (g1 x)))
                    (g2 v y))
                17)

(IF (EQUAL V (F1 X))
    ((LAMBDA (X V)
             ((LAMBDA (Y V) (G2 V Y)) (G1 X) V))
     Z V)
    '17)

=> *

ACL2 !>
||#

(test-easgl (g2 _ @)
            (if (equal v (f1 x))
                ((lambda (x v)
                   ((lambda (y v) (g2 v y)) (g1 x) v))
                 z v)
              '17)
            (((2 0 0 2) ; address
              Y ;; subterm matching (:@ ...)
              ((Y . (G1 Z))
               (V . V)
               (X . Z)) ; bindings
              ;; governors
              (EQUAL V (F1 X)))))

; Next, when we dive inside let bindings let's pick up some governors.

#||
ACL2 !>:trans (if (equal (car v) z)
                  (let* ((v (cons w w))
                         (v (cons v v)))
                    (if (equal v (f1 x))
                        (let* ((x z)
                               (y (g1 x)))
                          (g2 v (g3 x y v)))
                      17))
                18)

(IF (EQUAL (CAR V) Z)
    ((LAMBDA (V X Z)
             ((LAMBDA (V Z X)
                      (IF (EQUAL V (F1 X))
                          ((LAMBDA (X V)
                                   ((LAMBDA (Y X V) (G2 V (G3 X Y V)))
                                    (G1 X)
                                    X V))
                           Z V)
                          '17))
              (CONS V V)
              Z X))
     (CONS W W)
     X Z)
    '18)

=> *

ACL2 !>
||#

(test-easgl (g2 _ (:@ (g3 _ y v)))
            (IF (EQUAL (CAR V) Z)
                ((LAMBDA (V X Z)
                         ((LAMBDA (V Z X)
                                  (IF (EQUAL V (F1 X))
                                      ((LAMBDA (X V)
                                               ((LAMBDA (Y X V) (G2 V (G3 X Y V)))
                                                (G1 X)
                                                X V))
                                       Z V)
                                      '17))
                          (CONS V V)
                          Z X))
                 (CONS W W)
                 X Z)
                '18)
            (((2 0 0 2 0 0 2) ; address
              (G3 X Y V)
              ((Y . (G1 Z))
               (X . Z)
               (V . (CONS (CONS W W) (CONS W W)))
               (Z . Z))
              (EQUAL (CAR V) Z)
              (EQUAL (CONS (CONS W W) (CONS W W))
                     (F1 X)))))

; Variation where we include a let-binding of more than one variable

#||
ACL2 !>:trans (if (equal (car v) z)
                  (let ((v (cons w w))
                        (u (cons v v)))
                    (if (equal v (f1 x))
                        (let* ((x z)
                               (y (g1 x)))
                          (g2 v (g3 u y v)))
                      17))
                18)

(IF (EQUAL (CAR V) Z)
    ((LAMBDA (V U Z X)
             (IF (EQUAL V (F1 X))
                 ((LAMBDA (X V U)
                          ((LAMBDA (Y U V) (G2 V (G3 U Y V)))
                           (G1 X)
                           U V))
                  Z V U)
                 '17))
     (CONS W W)
     (CONS V V)
     Z X)
    '18)

=> *

ACL2 !>
||#

(test-easgl (g2 _ (:@ (g3 _ y v)))
            (IF (EQUAL (CAR V) Z)
                ((LAMBDA (V U Z X)
                         (IF (EQUAL V (F1 X))
                             ((LAMBDA (X V U)
                                      ((LAMBDA (Y U V) (G2 V (G3 U Y V)))
                                       (G1 X)
                                       U V))
                              Z V U)
                             '17))
                 (CONS W W)
                 (CONS V V)
                 Z X)
                '18)
            (((2 0 2 0 0 2) ; address
              (G3 U Y V)
              ((Y . (G1 Z))
               (U . (CONS V V))
               (V . (CONS W W))
               (X . Z)
               (Z . Z))
              (EQUAL (CAR V) Z)
              (EQUAL (CONS W W) (F1 X)))))

; A further variation, where we have two subterms and more governors under let
; bindings, and we also test that the pattern matches against the untranslated
; input

#||
ACL2 !>:trans (if (equal (car v) z)
                  (let ((v (cons w w))
                        (u (cons v v)))
                    (if (equal v (f1 x))
                        (let* ((x z)
                               (y (g1 x)))
                          (h1 (if (consp v) (h2 v 3) (g3 u y v))))
                      17))
                18)

(IF (EQUAL (CAR V) Z)
    ((LAMBDA (V U Z X)
             (IF (EQUAL V (F1 X))
                 ((LAMBDA (X V U)
                          ((LAMBDA (Y U V)
                                   (H1 (IF (CONSP V) (H2 V '3) (G3 U Y V))))
                           (G1 X)
                           U V))
                  Z V U)
                 '17))
     (CONS W W)
     (CONS V V)
     Z X)
    '18)

=> *

ACL2 !>
||#

(test-easgl (h1 (if _ (h2 @ 3) (:@ (g3 _ _ _))))
            (IF (EQUAL (CAR V) Z)
                ((LAMBDA (V U Z X)
                         (IF (EQUAL V (F1 X))
                             ((LAMBDA (X V U)
                                      ((LAMBDA (Y U V)
                                               (H1 (IF (CONSP V)
                                                       (H2 V '3)
                                                       (G3 U Y V))))
                                       (G1 X)
                                       U V))
                              Z V U)
                             '17))
                 (CONS W W)
                 (CONS V V)
                 Z X)
                '18)
            (

; first address-subterm-governors triple:

             ((2 0 2 0 0 1 2 1) ; address

; subterm:

              V

; bindings:

              ((Y . (G1 Z))
               (U . (CONS V V))
               (V . (CONS W W))
               (X . Z)
               (Z . Z))

; governors

              (EQUAL (CAR V) Z)
              (EQUAL (CONS W W) (F1 X))
              (CONSP (CONS W W)))

; second address-subterm-governors triple:

             ((2 0 2 0 0 1 3) ; address
              (G3 U Y V) ; subterm

; bindings

              ((Y . (G1 Z))
               (U . (CONS V V))
               (V . (CONS W W))
               (X . Z)
               (Z . Z))

; governors

              (EQUAL (CAR V) Z)
              (EQUAL (CONS W W) (F1 X))
              (NOT (CONSP (CONS W W))))))

; Here is a very simple test handling of let bindings.

(test-easgl (let ((y @)) (car y))
            ((LAMBDA (Y) (CAR Y))
             (CDR (CONS X (CONS X X))))
            (((1)
              (CDR (CONS X (CONS X X)))
              ())))
