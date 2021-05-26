; Tests of my-get-event
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "my-get-event")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;; An example where the built-in utility GET-EVENT returns something not
;; useful, namely (VERIFY-TERMINATION-BOOT-STRAP (DEF-BODY)):
(assert-equal
 (my-get-event 'def-body (w state))
 '(DEFUN
    DEF-BODY (FN WRLD)
    (DECLARE
     (XARGS :GUARD (AND (SYMBOLP FN)
                        (PLIST-WORLDP WRLD)
                        (TRUE-LISTP (GETPROPC FN 'DEF-BODIES NIL WRLD)))))
    (CAR (GETPROPC FN 'DEF-BODIES NIL WRLD))))

;; An example where the built-in utility GET-EVENT returns something not
;; useful:
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

;; Test on a name was introduced with mutual-recursion:
(assert-equal
 (my-get-event 'pseudo-termp (w state))
 '(MUTUAL-RECURSION (DEFUN PSEUDO-TERMP (X)
                      (DECLARE (XARGS :GUARD T :MODE :LOGIC))
                      (COND ((ATOM X) (SYMBOLP X))
                            ((EQ (CAR X) 'QUOTE)
                             (AND (CONSP (CDR X))
                                  (NULL (CDR (CDR X)))))
                            ((NOT (TRUE-LISTP X)) NIL)
                            ((NOT (PSEUDO-TERM-LISTP (CDR X))) NIL)
                            (T (OR (SYMBOLP (CAR X))
                                   (AND (TRUE-LISTP (CAR X))
                                        (EQUAL (LENGTH (CAR X)) 3)
                                        (EQ (CAR (CAR X)) 'LAMBDA)
                                        (SYMBOL-LISTP (CADR (CAR X)))
                                        (PSEUDO-TERMP (CADDR (CAR X)))
                                        (EQUAL (LENGTH (CADR (CAR X)))
                                               (LENGTH (CDR X))))))))
                    (DEFUN PSEUDO-TERM-LISTP (LST)
                      (DECLARE (XARGS :GUARD T))
                      (COND ((ATOM LST) (EQUAL LST NIL))
                            (T (AND (PSEUDO-TERMP (CAR LST))
                                    (PSEUDO-TERM-LISTP (CDR LST))))))))

;; Test on a built-in :program mode function:
(assert-equal ; Matt K. mod: avoid translate, to avoid ACL2(p) error
 (my-get-event 'translatable-p (w state))
 '(defun translatable-p (form stobjs-out bindings known-stobjs ctx wrld)
    (mv-let (erp val bindings)
      (translate1-cmp form stobjs-out bindings known-stobjs ctx wrld
                      (default-state-vars nil))
      (declare (ignore val bindings))
      (null erp))))

;; Test on a name that was introduced with defuns:
(deftest
  (defuns
    (new-PSEUDO-TERMP (X)
                      (DECLARE (XARGS :GUARD T :MODE :LOGIC))
                      (COND ((ATOM X) (SYMBOLP X))
                            ((EQ (CAR X) 'QUOTE)
                             (AND (CONSP (CDR X))
                                  (NULL (CDR (CDR X)))))
                            ((NOT (TRUE-LISTP X)) NIL)
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
                              ((NOT (TRUE-LISTP X)) NIL)
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
