; Tests of the rename-params transformation
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Authors: Limei Gilham
;          Eric Smith (eric.smith@kestrel.edu)
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rename-params")
(include-book "kestrel/utilities/deftest" :dir :system)

;trivial test
(deftest
  (defun foo (x) (+ 1 x))
  (rename-params foo (x y))
  (must-be-redundant
   (DEFUN FOO$1 (Y)
     (DECLARE (IGNORABLE Y)) ;todo: clean up
     (DECLARE (XARGS :VERIFY-GUARDS NIL)) ;todo
     ;; note that the 1 isn't quoted:
     (+ 1 Y))))

;;TEST1
(deftest
  ;;an example non-recursive function with a let:
  (defun foo (x)
    (let ((y (+ 1 x)))
      (* y y)))
  (rename-params foo ((x z)))
  (must-be-redundant
    (DEFUN FOO$1 (Z)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (let ((y (+ 1 z)))
        (* y y)))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;variant of the above with a guard:
(deftest
  ;;an example non-recursive function with a let:
  (defun foo (x)
    (declare (xargs :guard (natp x)))
    (let ((y (+ 1 x)))
      (* y y)))
  (rename-params foo ((x z)))
  (must-be-redundant
    (DEFUN FOO$1 (Z)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (DECLARE (XARGS :GUARD (NATP Z)))
      (let ((y (+ 1 z))) (* y y)))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;variant of the above with a guard but verify-guards nil
(deftest
  ;;an example non-recursive function with a let:
  (defun foo (x)
    (declare (xargs :guard (natp x) :verify-guards nil))
    (let ((y (+ 1 x)))
      (* y y)))
  (rename-params foo ((x z)))
  (must-be-redundant
    (DEFUN FOO$1 (Z)
      (DECLARE (XARGS :GUARD (NATP Z)
                      :VERIFY-GUARDS NIL))
      (let ((y (+ 1 z))) (* y y)))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;renaming multiple parameters
(deftest
  ;;an example non-recursive function with a let
  (defun foo (x y z)
    (let ((x (+ 1 x))
          (y (- y 1)))
      (- (* x y) z)))
  (rename-params foo ((x u) (z v)))
  (must-be-redundant
    (DEFUN FOO$1 (U Y V)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (let ((u (+ 1 u))
            (y (+ -1 y)))
        (+ (* u y) (- v))))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X Y Z) (FOO$1 X Y Z)))))

(deftest
  ;;an example non-recursive function with a let
  ;;where some new parameter names coincide with lambda variable names
  (defun foo (x y z)
    (let ((u (+ x y))
          (v (* x y)))
      (list x y z u v)))
  (rename-params foo ((x u) (y v)))
  (must-be-redundant
    (DEFUN
      FOO$1 (U V Z)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (LET ((U2 (+ U V))
            (V2 (* U V)))
           (LIST U V Z U2 V2)))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X Y Z) (FOO$1 X Y Z)))))

(deftest
  ;; an example recursive function with a let
  (defun sum-list (l r$)
    (declare (xargs :measure (acl2-count l)))
    (if (endp l)
        (+ r$ 0)
      (let ((l (cdr l))
            (r$ (+ r$ (fix (car l)))))
        (sum-list l r$))))
  (rename-params sum-list ((l lst) (r$ result)))
  (must-be-redundant
    (DEFUN SUM-LIST$1 (LST RESULT)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (DECLARE (XARGS :MEASURE (ACL2-COUNT LST)))
      (IF (ENDP LST)
          (+ RESULT 0)
          (LET ((LST (CDR LST))
                (RESULT (+ RESULT (FIX (CAR LST)))))
               (SUM-LIST$1 LST RESULT))))
    (DEFTHM
      SUM-LIST-BECOMES-SUM-LIST$1
      (EQUAL (SUM-LIST L R$)
             (SUM-LIST$1 L R$)))))

;; ;;test the transformation by applying to itself!
;; (deftest
;;   ;;Here we give a single function that's part of a mutual-recursion nest.
;;   ;;Note that the param renaming is applied to all functions in the nest (TODO:
;;   ;;allow for finer-grained control):
;;   (rename-params rename-params-in-term ((term tm) (terms tms) (renaming-alist alist)))
;;   (must-be-redundant
;;    (MUTUAL-RECURSION
;;     (DEFUN
;;       RENAME-PARAMS-IN-TERM$1 (TM ALIST)
;;       (DECLARE (XARGS :VERIFY-GUARDS NIL))
;;       (DECLARE (XARGS :MEASURE (ACL2-COUNT TM)
;;                       :GUARD (AND (PSEUDO-TERMP TM)
;;                                   (SYMBOL-SYMBOL-ALISTP ALIST))
;;                       :VERIFY-GUARDS NIL))
;;       (COND ((ATOM TM) (OR (LOOKUP-EQ TM ALIST) TM))
;;             ((QUOTEP TM) TM)
;;             (T (LET* ((ARGS (CDR TM))
;;                       (ARGS (RENAME-PARAMS-IN-TERMS$1 ARGS ALIST))
;;                       (FN (CAR TM)))
;;                      (IF (CONSP FN)
;;                          (LET* ((LAMBDA-FORMALS (CADR FN))
;;                                 (LAMBDA-FORMALS (SUBLIS-VAR-SIMPLE-LST ALIST LAMBDA-FORMALS))
;;                                 (LAMBDA-BODY (CADDR FN))
;;                                 (LAMBDA-BODY (RENAME-PARAMS-IN-TERM$1 LAMBDA-BODY ALIST)))
;;                                (CONS (LIST 'LAMBDA
;;                                            LAMBDA-FORMALS LAMBDA-BODY)
;;                                      ARGS))
;;                          (CONS FN ARGS))))))
;;     (DEFUN
;;       RENAME-PARAMS-IN-TERMS$1 (TMS ALIST)
;;       (DECLARE (XARGS :VERIFY-GUARDS NIL))
;;       (DECLARE (XARGS :MEASURE (ACL2-COUNT TMS)
;;                       :GUARD (AND (PSEUDO-TERM-LISTP TMS)
;;                                   (SYMBOL-SYMBOL-ALISTP ALIST))))
;;       (AND (NOT (ENDP TMS))
;;            (CONS (RENAME-PARAMS-IN-TERM$1 (CAR TMS)
;;                                           ALIST)
;;                  (RENAME-PARAMS-IN-TERMS$1 (CDR TMS)
;;                                            ALIST)))))
;;    ;; (MAKE-FLAG FLAG-RENAME-PARAMS-IN-TERM
;;    ;;            RENAME-PARAMS-IN-TERM)
;;    (DEFTHM
;;      RENAME-PARAMS-IN-TERM-BECOMES-RENAME-PARAMS-IN-TERM$1
;;      (EQUAL (RENAME-PARAMS-IN-TERM TERM RENAMING-ALIST)
;;             (RENAME-PARAMS-IN-TERM$1 TERM RENAMING-ALIST)))
;;    (DEFTHM
;;      RENAME-PARAMS-IN-TERMS-BECOMES-RENAME-PARAMS-IN-TERMS$1
;;      (EQUAL (RENAME-PARAMS-IN-TERMS TERMS RENAMING-ALIST)
;;             (RENAME-PARAMS-IN-TERMS$1 TERMS RENAMING-ALIST)))))

;TODO: test the skip guard proof stuff

(deftest
  (defun foo (x y) (+ x y))
  (rename-params foo ((x x1) (y y1)) :new-name bar)
  (must-be-redundant (defun bar (x1 y1) (+ x1 y1)))
  )

;; this previously failed to verify guards
(deftest
  (defund g1 (x) (declare (xargs :guard t)) x)
  (defund g2 (x) (declare (xargs :guard t)) x)

  (in-theory (disable (:type-prescription g1) (:type-prescription g2)))

  (defun D1 (x) (declare (xargs :guard (g1 x))) x)
  (defun D2 (x) (declare (xargs :guard (g2 x))) x)

  (defun foo (x n)
    (declare (xargs :guard (and (natp n) (g1 x))
                    :guard-hints (("Goal" :in-theory (enable g1 g2)))))
    (if (zp n)
        x
      (foo (D2 x) (1- n))))

  (mutual-recursion
   (defun foo1 (x n)
     (declare (xargs :guard (and (natp n) (g1 x))))
     (if (zp n)
         x
       (foo2 (D2 x) (1- n))))
   (defun foo2 (x n)
     (declare (xargs :guard (and (natp n) (g2 x))
                     :guard-hints (("Goal" :in-theory (enable g1 g2)))))
     (if (zp n)
         x
       (foo1 (D1 x) (1- n)))))

  (rename-params foo (x y))
  (rename-params foo1 (x y))

  (must-be-redundant
   (verify-guards foo$1)
   (verify-guards foo1$1)
   (verify-guards foo2$1))
  )


;; This previously failed, because the guard conjecture was computed in the
;; current theory (now we do the verify-guards after doing (in-theory nil)).
(deftest
  (defun even-lengthp (x)
    (declare (xargs :guard (natp (len x))))
    (if (zp (len x))
        t
      (if (equal (len x) 1)
          nil
        (even-lengthp (cddr x)))))

  ;; This disable was previously necessary:
  ;; (in-theory (disable (:type-prescription len)))
  (rename-params even-lengthp (x y)))

;;
;; more tests with possible conflicts:
;;

(deftest
  ;; x trivially bound in the lambda, new name for x doesn't appear in the lambda body
  (defun foo (x) (let ((y 4)) (+ x y)))
  (rename-params foo (x x2))
  (must-be-redundant
   (defun foo$1 (x2)
     (declare (ignorable x2))
     (declare (xargs :verify-guards nil))
     (let ((y 4)) (+ x2 y))))

  ;; another option (less nice, but easier, but what if there was another param being renamed to x?)::
  ;; (defun foo (x2) (let ((y 4) (x x2)) (+ x y)))
  )

(deftest
  ;; x trivially bound in the lambda, new name for x does appear
  (defun foo (x) (let ((x2 4)) (+ x x2)))
  (rename-params foo (x x2))
  (must-be-redundant
   (DEFUN FOO$1 (X2)
     (DECLARE (IGNORABLE X2))
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET ((X22 4)) (+ X2 X22))))

  ;; or could do this (but what if there was another param being renamed to x?)::
  ;; (defun foo (x2) (let ((x2 4) (x x2)) (+ x x2)))
  )

(deftest
  ;; x non-trivially bound in the lambda
  (defun foo (x) (let ((x (+ 1 x))) (+ 2 x)))
  (rename-params foo (x x2))
  (must-be-redundant
   (DEFUN FOO$1 (X2)
     (DECLARE (IGNORABLE X2))
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET ((X2 (+ 1 X2))) (+ 2 X2))))

  ;; or could do this (but what if there was another param being renamed to x?):
  ;; (defun foo (x2) (let ((x (+ 1 x2))) (+ 2 x)))
  )

(deftest
  (defun foo (x) (< x (let ((x2 4)) x2))) ; note that x does not appear in the let
  (rename-params foo (x x2))
  (must-be-redundant
   (defun foo$1 (x2)
     (declare (ignorable x2))
     (declare (xargs :verify-guards nil))
     (< x2
        ;; okay to re-bind x2 since x2 wasn't used in this subterm originally:
        (let ((x2 4)) x2)))))

;; this swaps x and y.  no new names are really needed
(deftest
  (defun foo (x y) (let ((x (+ 1 x)) (y (+ 1 y))) (+ x y)))
  (rename-params foo ((x y) (y x)))
  (must-be-redundant
   (DEFUN FOO$1 (y x)
     (DECLARE (IGNORABLE X Y))
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET ((y (+ 1 y))
           (x (+ 1 x)))
          (+ Y x)))))

;; todo: get this to work
;; problem with variable capture
(deftest
  (DEFUN foo (N R)
    (declare (xargs :measure (nfix (+ 1 (- 100 n)))))
    (IF (or (not (natp n))
            (<= 100 N))
        (CONS R (CONS N 'NIL))
        (LET ((r2 (+ R 2)))
             (LET ((n2 (+ 1 n)))
                  (foo n2 r2)))))

  (RENAME-PARAMS foo ((R r2)) :PRINT :ALL)
  (must-be-redundant
   (DEFUN FOO$1 (N R2)
     (DECLARE (IGNORABLE N R2))
     (DECLARE (XARGS :VERIFY-GUARDS NIL
                     :MEASURE (NFIX (BINARY-+ '1
                                              (BINARY-+ '100 (UNARY-- N))))))
     (IF (OR (NOT (NATP N)) (<= 100 N))
         (LIST R2 N)
         (LET* ((R2 (+ R2 2))
                (N2 (+ 1 N)))
               (FOO$1 N2 R2))))
   (DEFTHM FOO-BECOMES-FOO$1 (EQUAL (FOO N R) (FOO$1 N R)))))

;; test with a clash
(deftest
  (defun foo (x y) (+ x y))
  (must-fail (rename-params foo (x y))) ; y already exists!  todo: better error message?
  )

;; A test with mutual-recursion
(deftest
  (rename-params pseudo-termp
                 ((x term) ;todo: support different lists for each function
                  (lst terms))))

;; A test with a :map for :new-names
(deftest
  (rename-params pseudo-termp
                 ((x term) ;todo: support different lists for each function
                  (lst terms))
                 :new-name
                 (:map (pseudo-termp new-pseudo-termp)
                       (pseudo-term-listp new-pseudo-term-listp)))
  (must-be-redundant
   (MUTUAL-RECURSION (DEFUN NEW-PSEUDO-TERMP (TERM)
                       (DECLARE (IGNORABLE TERM))
                       (DECLARE (XARGS :VERIFY-GUARDS NIL
                                       :GUARD T
                                       :MODE :LOGIC))
                       (COND ((ATOM TERM) (SYMBOLP TERM))
                             ((EQ (CAR TERM) 'QUOTE)
                              (AND (CONSP (CDR TERM))
                                   (NULL (CDDR TERM))))
                             ((NOT (TRUE-LISTP TERM)) NIL)
                             ((NOT (NEW-PSEUDO-TERM-LISTP (CDR TERM)))
                              NIL)
                             ((SYMBOLP (CAR TERM))
                              (SYMBOLP (CAR TERM)))
                             ((TRUE-LISTP (CAR TERM))
                              (AND (EQUAL (LENGTH (CAR TERM)) 3)
                                   (EQ (CAR (CAR TERM)) 'LAMBDA)
                                   (SYMBOL-LISTP (CADR (CAR TERM)))
                                   (NEW-PSEUDO-TERMP (CADDR (CAR TERM)))
                                   (EQUAL (LENGTH (CADR (CAR TERM)))
                                          (LENGTH (CDR TERM)))))
                             (T NIL)))
                     (DEFUN NEW-PSEUDO-TERM-LISTP (TERMS)
                       (DECLARE (IGNORABLE TERMS))
                       (DECLARE (XARGS :VERIFY-GUARDS NIL :GUARD T))
                       (COND ((ATOM TERMS) (EQUAL TERMS NIL))
                             ((NEW-PSEUDO-TERMP (CAR TERMS))
                              (NEW-PSEUDO-TERM-LISTP (CDR TERMS)))
                             (T NIL))))
   (DEFTHM PSEUDO-TERMP-BECOMES-NEW-PSEUDO-TERMP
     (EQUAL (PSEUDO-TERMP X)
            (NEW-PSEUDO-TERMP X)))
   (DEFTHM PSEUDO-TERM-LISTP-BECOMES-NEW-PSEUDO-TERM-LISTP
     (EQUAL (PSEUDO-TERM-LISTP LST)
            (NEW-PSEUDO-TERM-LISTP LST)))
   (VERIFY-GUARDS$
    NEW-PSEUDO-TERMP
    :HINTS
    (("Goal" :USE (:INSTANCE (:GUARD-THEOREM PSEUDO-TERMP NIL)
                             :EXTRA-BINDINGS-OK (X TERM)
                             (LST TERMS))
      :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
      :IN-THEORY '(PSEUDO-TERMP-BECOMES-NEW-PSEUDO-TERMP
                   PSEUDO-TERM-LISTP-BECOMES-NEW-PSEUDO-TERM-LISTP
                   (:E EQLABLEP)
                   (:E EQLABLE-LISTP))))
    :GUARD-SIMPLIFY NIL)))
