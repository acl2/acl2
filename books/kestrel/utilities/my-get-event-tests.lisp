; Tests of my-get-event
;
; Copyright (C) 2015-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "my-get-event")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "deftest")

;; TODO: Rename this to get-event$ or get-event!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo! (my-get-event 'car (w state)) this gives (enter-boot-strap-mode :unix) !

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example with a defun:
(assert-equal
  (my-get-event 'natp (w state))
  '(defun natp (x)
     (declare (xargs :guard t :mode :logic))
     (and (integerp x) (<= 0 x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example with a defmacro:
(assert-equal
  (my-get-event 'append (w state))
  '(defmacro append (&rest rst)
     (cond ((null rst) nil)
           ((null (cdr rst)) (car rst))
           (t (xxxjoin 'binary-append rst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example with a mutual-recursion (the result is the entire mutual-recursion):

(assert-equal
  (my-get-event 'pseudo-termp (w state)) ; first function in the nest
  '(mutual-recursion
    (defun pseudo-termp (x)
      (declare (xargs :guard t :mode :logic))
      (cond ((atom x) (symbolp x))
            ((eq (car x) 'quote)
             (and (consp (cdr x))
                  (null (cdr (cdr x)))))
            ((not (pseudo-term-listp (cdr x))) nil)
            (t (or (symbolp (car x))
                   (and (true-listp (car x))
                        (equal (len$ (car x)) 3)
                        (eq (car (car x)) 'lambda)
                        (symbol-listp (cadr (car x)))
                        (pseudo-termp (caddr (car x)))
                        (equal (len$ (cadr (car x)))
                               (len$ (cdr x))))))))
    (defun pseudo-term-listp (lst)
      (declare (xargs :guard t))
      (cond ((atom lst) (equal lst nil))
            (t (and (pseudo-termp (car lst))
                    (pseudo-term-listp (cdr lst))))))))

(assert-equal
  (my-get-event 'pseudo-term-listp (w state)) ; second function in the nest
  '(mutual-recursion
    (defun pseudo-termp (x)
      (declare (xargs :guard t :mode :logic))
      (cond ((atom x) (symbolp x))
            ((eq (car x) 'quote)
             (and (consp (cdr x))
                  (null (cdr (cdr x)))))
            ((not (pseudo-term-listp (cdr x))) nil)
            (t (or (symbolp (car x))
                   (and (true-listp (car x))
                        (equal (len$ (car x)) 3)
                        (eq (car (car x)) 'lambda)
                        (symbol-listp (cadr (car x)))
                        (pseudo-termp (caddr (car x)))
                        (equal (len$ (cadr (car x)))
                               (len$ (cdr x))))))))
    (defun pseudo-term-listp (lst)
      (declare (xargs :guard t))
      (cond ((atom lst) (equal lst nil))
            (t (and (pseudo-termp (car lst))
                    (pseudo-term-listp (cdr lst))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example with a defaxiom:
(assert-equal
  (my-get-event 'car-cons (w state))
  '(defaxiom car-cons
     (equal (car (cons x y)) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example with a defthm:
(assert-equal
  (my-get-event 'default-pkg-imports (w state))
  '(defthm default-pkg-imports
     (implies (not (stringp x))
              (equal (pkg-imports x)
                     nil))
     :hints (("Goal" :use completion-of-pkg-imports))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example with a deftheory

(deftheory my-theory nil)

(assert-equal
  (my-get-event 'my-theory (w state))
  '(deftheory my-theory nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example with a stobj (todo: doesn't work for state):

(defstobj my-stobj (scalar-field-1 :type integer :initially 7))
;; todo: also test defabsstobj

(assert-equal
  (my-get-event 'my-stobj (w state))
  '(defstobj my-stobj
     (scalar-field-1 :type integer
                     :initially 7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An example where the built-in utility GET-EVENT returns something not
;; useful.

;; get-event is not helpful:
(assert-equal (get-event 'def-body (w state)) '(verify-termination-boot-strap (def-body)))

(assert-equal
 (my-get-event 'def-body (w state))
 '(DEFUN
    DEF-BODY (FN WRLD)
    (DECLARE
     (XARGS :GUARD (AND (SYMBOLP FN)
                        (PLIST-WORLDP WRLD)
                        (TRUE-LISTP (GETPROPC FN 'DEF-BODIES NIL WRLD)))))
    (CAR (GETPROPC FN 'DEF-BODIES NIL WRLD))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An example where the built-in utility GET-EVENT returns something not
;; useful:

;; get-event is not helpful:
(assert-equal
  (get-event 'all-vars1 (w state))
  '(verify-termination-boot-strap
    (all-vars1 (declare (xargs :mode :logic :verify-guards nil)))
    (all-vars1-lst (declare (xargs :mode :logic)))))

;; my-get-event gives us what we want:
(assert-equal
 (my-get-event 'all-vars1 (w state))
 '(MUTUAL-RECURSION
   (DEFUN ALL-VARS1 (TERM ANS)
     (DECLARE (XARGS :GUARD (AND (PSEUDO-TERMP TERM)
                                 (SYMBOL-LISTP ANS))
                     :MODE :PROGRAM))
     (COND ((VARIABLEP TERM)
            (ADD-TO-SET-EQ TERM ANS))
           ((FQUOTEP TERM) ANS)
           (T (ALL-VARS1-LST (FARGS TERM) ANS))))
   (DEFUN ALL-VARS1-LST (LST ANS)
     (DECLARE (XARGS :GUARD (AND (PSEUDO-TERM-LISTP LST)
                                 (SYMBOL-LISTP ANS))
                     :MODE :PROGRAM))
     (COND ((ENDP LST) ANS)
           (T (ALL-VARS1-LST (CDR LST)
                             (ALL-VARS1 (CAR LST) ANS)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test on a built-in :program mode function (get-event also works):
(assert-equal
 (my-get-event 'translatable-p (w state))
 '(defun translatable-p (form stobjs-out bindings known-stobjs ctx wrld)
    (mv-let (erp val bindings)
      (translate1-cmp form stobjs-out bindings known-stobjs ctx wrld
                      (default-state-vars nil))
      (declare (ignore val bindings))
      (null erp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test on a name that was introduced with defuns:
(deftest
  (defuns
    (new-PSEUDO-TERMP (X)
                      (DECLARE (XARGS :GUARD T :MODE :LOGIC))
                      (COND ((ATOM X) (SYMBOLP X))
                            ((EQ (CAR X) 'QUOTE)
                             (AND (CONSP (CDR X))
                                  (NULL (CDR (CDR X)))))
                            ((NOT (new-PSEUDO-TERM-LISTP (CDR X))) NIL)
                            (T (OR (SYMBOLP (CAR X))
                                   (AND (TRUE-LISTP (CAR X))
                                        (EQUAL (LENGTH (CAR X)) 3)
                                        (EQ (CAR (CAR X)) 'LAMBDA)
                                        (SYMBOL-LISTP (CADR (CAR X)))
                                        (new-PSEUDO-TERMP (CADDR (CAR X)))
                                        (EQUAL (LENGTH (CADR (CAR X)))
                                               (LENGTH (CDR X))))))))
    (new-PSEUDO-TERM-LISTP (LST)
                           (DECLARE (XARGS :GUARD T))
                           (COND ((ATOM LST) (EQUAL LST NIL))
                                 (T (AND (new-PSEUDO-TERMP (CAR LST))
                                         (new-PSEUDO-TERM-LISTP (CDR LST)))))))
  ;; Note that my-get-event returns a DEFUNS event:
  (assert-equal
   (my-get-event 'NEW-PSEUDO-TERMP (w state))
   '(DEFUNS
      (NEW-PSEUDO-TERMP (X)
                        (DECLARE (XARGS :GUARD T :MODE :LOGIC))
                        (COND ((ATOM X) (SYMBOLP X))
                              ((EQ (CAR X) 'QUOTE)
                               (AND (CONSP (CDR X))
                                    (NULL (CDR (CDR X)))))
                              ((NOT (NEW-PSEUDO-TERM-LISTP (CDR X)))
                               NIL)
                              (T (OR (SYMBOLP (CAR X))
                                     (AND (TRUE-LISTP (CAR X))
                                          (EQUAL (LENGTH (CAR X)) 3)
                                          (EQ (CAR (CAR X)) 'LAMBDA)
                                          (SYMBOL-LISTP (CADR (CAR X)))
                                          (NEW-PSEUDO-TERMP (CADDR (CAR X)))
                                          (EQUAL (LENGTH (CADR (CAR X)))
                                                 (LENGTH (CDR X))))))))
      (NEW-PSEUDO-TERM-LISTP (LST)
                             (DECLARE (XARGS :GUARD T))
                             (COND ((ATOM LST) (EQUAL LST NIL))
                                   (T (AND (NEW-PSEUDO-TERMP (CAR LST))
                                           (NEW-PSEUDO-TERM-LISTP (CDR LST)))))))))
