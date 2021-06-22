; Tests of make-evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-evaluator")
(include-book "std/testing/must-be-redundant" :dir :system)

;this introduces a skip-proofs :
(make-evaluator len-evaluator
                (acons 1 '((len len arg1) (consp consp arg1) (cdr cdr arg1))
                       (acons 2 '((binary-+ binary-+ arg1 arg2)) nil)))

(defthm len-evaluator-test
  (equal (apply-len-evaluator 'len '((a b c)) nil 0) 3))

;fixme add more tests!
(defthm len-evaluator-test-2
  (equal (dag-val-with-len-evaluator '((1 len 0) (0 . v)) (acons 'v '(1 b c) nil) nil 0)
         3))

;; Expected result:
(must-be-redundant
 (MUTUAL-RECURSION
  (DEFUND APPLY-LEN-EVALUATOR (FN ARGS INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
    (DECLARE (XARGS :MEASURE 1
                    :GUARD (AND (OR (SYMBOLP FN) (PSEUDO-LAMBDAP FN))
                                (TRUE-LISTP ARGS)
                                (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
                                (NATP ARRAY-DEPTH))))
    (IF (CONSP FN) ; todo: do we sometimes know that things are lambda-free?
        (LET* ((FORMALS (SECOND FN))
               (BODY (THIRD FN))
               (ALIST (PAIRLIS$-FAST FORMALS ARGS))) ;todo: avoid this?
              (EVAL-LEN-EVALUATOR
               ALIST BODY
               INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH))
        (LET
         ((ARGS-TO-WALK-DOWN ARGS))
         (MV-LET
           (HIT VAL)
           (IF
            (ENDP ARGS-TO-WALK-DOWN)
            (MV NIL NIL)
            (LET
             ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
             (IF
              (ENDP ARGS-TO-WALK-DOWN)
              (LET ((ARG1 (NTH 0 ARGS)))
                   (IF (EQ 'CDR FN)
                       (MV T (CDR ARG1))
                       (IF (EQ 'CONSP FN)
                           (MV T (CONSP ARG1))
                           (IF (EQ 'LEN FN)
                               (MV T (LEN ARG1))
                               (MV NIL NIL)))))
              (LET
               ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
               (IF
                (ENDP ARGS-TO-WALK-DOWN)
                (LET ((ARG2 (NTH 1 ARGS))
                      (ARG1 (NTH 0 ARGS)))
                     (IF (EQ 'BINARY-+ FN)
                         (MV T (BINARY-+ ARG1 ARG2))
                         (MV NIL NIL)))
                (LET
                 ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                 (IF
                  (ENDP ARGS-TO-WALK-DOWN)
                  (MV NIL NIL)
                  (LET
                   ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                   (IF
                    (ENDP ARGS-TO-WALK-DOWN)
                    (LET
                     ((ARG4 (NTH 3 ARGS)) ;todo: optimize stuff like this
                      (ARG3 (NTH 2 ARGS))
                      (ARG2 (NTH 1 ARGS))
                      (ARG1 (NTH 0 ARGS)))
                     (DECLARE (IGNORE ARG4)) ;todo: why?  don't compute
                     (IF
                      (EQ 'APPLY-LEN-EVALUATOR FN)
                      (MV T
                          (APPLY-LEN-EVALUATOR
                           ARG1 ARG2 ARG3 ARRAY-DEPTH))
                      (IF
                       (EQ 'DAG-VAL-WITH-LEN-EVALUATOR FN)
                       (MV T
                           (DAG-VAL-WITH-LEN-EVALUATOR
                            ARG1 ARG2 ARG3 (+ 1 ARRAY-DEPTH)))
                       (MV NIL NIL))))
                    (LET
                     ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                     (IF
                      (ENDP ARGS-TO-WALK-DOWN)
                      (MV NIL NIL)
                      (LET
                       ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                       (IF
                        (ENDP ARGS-TO-WALK-DOWN)
                        (MV NIL NIL)
                        (LET
                         ((ARGS-TO-WALK-DOWN
                           (CDR ARGS-TO-WALK-DOWN)))
                         (IF
                          (ENDP ARGS-TO-WALK-DOWN)
                          (MV NIL NIL)
                          (LET
                           ((ARGS-TO-WALK-DOWN
                             (CDR ARGS-TO-WALK-DOWN)))
                           (IF
                            (ENDP ARGS-TO-WALK-DOWN)
                            (LET
                             ((ARG8 (NTH 7 ARGS))
                              (ARG7 (NTH 6 ARGS))
                              (ARG6 (NTH 5 ARGS))
                              (ARG5 (NTH 4 ARGS))
                              (ARG4 (NTH 3 ARGS))
                              (ARG3 (NTH 2 ARGS))
                              (ARG2 (NTH 1 ARGS))
                              (ARG1 (NTH 0 ARGS)))
                             (DECLARE (IGNORE ARG8))
                             (IF
                              (EQ 'EVAL-DAG-WITH-LEN-EVALUATOR FN)
                              (MV
                               T
                               (EVAL-DAG-WITH-LEN-EVALUATOR
                                ARG1 ARG2 ARG3
                                ARG4 ARG5 ARG6 ARG7 ARRAY-DEPTH))
                              (MV NIL NIL)))
                            (MV NIL NIL))))))))))))))))))
           (IF
            HIT VAL
            (LET
             ((MATCH (ASSOC-EQ FN INTERPRETED-FUNCTION-ALIST)))
             (IF
              (NOT MATCH)
              (ER
               HARD? 'APPLY-LEN-EVALUATOR
               "Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)"
               FN ARGS 'LEN-EVALUATOR)
              (LET* ((FN-INFO (CDR MATCH))
                     (FORMALS (FIRST FN-INFO))
                     (BODY (SECOND FN-INFO))
                     (ALIST (PAIRLIS$-FAST FORMALS ARGS)))
                    (EVAL-LEN-EVALUATOR
                     ALIST BODY INTERPRETED-FUNCTION-ALIST
                     ARRAY-DEPTH)))))))))
  (DEFUN EVAL-LEN-EVALUATOR (ALIST FORM INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
    (DECLARE
     (XARGS
      :VERIFY-GUARDS NIL
      :GUARD
      (AND
       (SYMBOL-ALISTP ALIST)
       (PSEUDO-TERMP FORM)
       (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
       (NATP ARRAY-DEPTH))))
    (COND
     ((VARIABLEP FORM)
      (LOOKUP-EQ FORM ALIST))
     ((FQUOTEP FORM) (UNQUOTE FORM))
     (T
      (LET
       ((FN (FFN-SYMB FORM)))
       (IF
        (and (OR (EQ FN 'IF) (EQ FN 'MYIF))
             (= 3 (len (fargs form))))
        (LET*
         ((TEST-FORM (farg1 FORM))
          (TEST-RESULT (EVAL-LEN-EVALUATOR
                        ALIST
                        TEST-FORM INTERPRETED-FUNCTION-ALIST
                        ARRAY-DEPTH)))
         (EVAL-LEN-EVALUATOR
          ALIST
          (IF TEST-RESULT (farg2 FORM)
              (farg3 FORM))
          INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH))
        (LET
         ((ARGS
           (EVAL-LIST-LEN-EVALUATOR ALIST (FARGS FORM)
                                    INTERPRETED-FUNCTION-ALIST
                                    ARRAY-DEPTH)))
         (APPLY-LEN-EVALUATOR FN ARGS INTERPRETED-FUNCTION-ALIST
                              ARRAY-DEPTH)))))))
  (DEFUN
    EVAL-LIST-LEN-EVALUATOR
    (ALIST FORM-LST
           INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
    (DECLARE
     (XARGS
      :VERIFY-GUARDS NIL
      :MEASURE (LEN FORM-LST)
      :GUARD
      (AND
       (SYMBOL-ALISTP ALIST)
       (PSEUDO-TERM-LISTP FORM-LST)
       (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
       (NATP ARRAY-DEPTH))))
    (IF
     (ENDP FORM-LST)
     NIL
     (CONS (EVAL-LEN-EVALUATOR
            ALIST (CAR FORM-LST)
            INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
           (EVAL-LIST-LEN-EVALUATOR ALIST (CDR FORM-LST)
                                    INTERPRETED-FUNCTION-ALIST
                                    ARRAY-DEPTH))))
  (DEFUN
    DAG-VAL-WITH-LEN-EVALUATOR
    (DAG ALIST
         INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
    (DECLARE
     (XARGS
      :MEASURE 0
      :GUARD
      (AND
       (OR (QUOTEP DAG)
           (AND (PSEUDO-DAGP DAG)
                (< (LEN DAG) 2147483646)))
       (SYMBOL-ALISTP ALIST)
       (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
       (NATP ARRAY-DEPTH))))
    (IF
     (QUOTEP DAG)
     (UNQUOTE DAG)
     (LET*
      ((TOP-NODENUM (TOP-NODENUM-of-dag DAG))
       (DAG-ARRAY-NAME (PACK$ 'DAG-ARRAY-
                              ARRAY-DEPTH '-FOR-DAG-VAL))
       (DAG-ARRAY (MAKE-INTO-ARRAY DAG-ARRAY-NAME DAG))
       (EVAL-ARRAY-NAME (PACK$ 'EVAL-ARRAY-
                               ARRAY-DEPTH '-FOR-DAG-VAL))
       (EVAL-ARRAY
        (MAKE-EMPTY-ARRAY EVAL-ARRAY-NAME (+ 1 TOP-NODENUM))))
      (CAR (AREF1 EVAL-ARRAY-NAME
                  (EVAL-DAG-WITH-LEN-EVALUATOR
                   (LIST TOP-NODENUM)
                   DAG-ARRAY-NAME DAG-ARRAY
                   ALIST EVAL-ARRAY-NAME EVAL-ARRAY
                   INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
                  TOP-NODENUM)))))
  (DEFUN EVAL-DAG-WITH-LEN-EVALUATOR (NODENUM-WORKLIST DAG-ARRAY-NAME DAG-ARRAY VAR-VALUE-ALIST
                                                       EVAL-ARRAY-NAME EVAL-ARRAY
                                                       INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
    (DECLARE (XARGS :GUARD (AND (NAT-LISTP NODENUM-WORKLIST)
                                (IF (CONSP NODENUM-WORKLIST)
                                    (PSEUDO-DAG-ARRAYP DAG-ARRAY-NAME DAG-ARRAY
                                                       (+ 1 (MAXELEM NODENUM-WORKLIST)))
                                    T)
                                (SYMBOL-ALISTP VAR-VALUE-ALIST)
                                (SYMBOLP EVAL-ARRAY-NAME)
                                (IF (CONSP NODENUM-WORKLIST)
                                    (EVAL-ARRAYP EVAL-ARRAY-NAME EVAL-ARRAY
                                                 (+ 1 (MAXELEM NODENUM-WORKLIST)))
                                    T)
                                (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
                                (NATP ARRAY-DEPTH))
                    :VERIFY-GUARDS NIL))
    (IF
     (ENDP NODENUM-WORKLIST)
     EVAL-ARRAY
     (LET*
      ((NODENUM (FIRST NODENUM-WORKLIST))
       (EXPR (AREF1 DAG-ARRAY-NAME DAG-ARRAY NODENUM)))
      (IF
       (VARIABLEP EXPR)
       (LET ((VALUE (LOOKUP-EQ-SAFE EXPR VAR-VALUE-ALIST)))
            (EVAL-DAG-WITH-LEN-EVALUATOR
             (REST NODENUM-WORKLIST)
             DAG-ARRAY-NAME DAG-ARRAY
             VAR-VALUE-ALIST EVAL-ARRAY-NAME
             (ASET1 EVAL-ARRAY-NAME
                    EVAL-ARRAY NODENUM (CONS VALUE NIL))
             INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH))
       (LET
        ((FN (CAR EXPR)))
        (IF
         (EQUAL FN 'QUOTE)
         (LET ((VALUE (UNQUOTE EXPR)))
              (EVAL-DAG-WITH-LEN-EVALUATOR
               (REST NODENUM-WORKLIST)
               DAG-ARRAY-NAME DAG-ARRAY
               VAR-VALUE-ALIST EVAL-ARRAY-NAME
               (ASET1 EVAL-ARRAY-NAME
                      EVAL-ARRAY NODENUM (CONS VALUE NIL))
               INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH))
         (LET
          ((ARGS (DARGS EXPR)))
          (IF
           (OR (EQ 'IF FN)
               (EQ 'MYIF FN)
               (EQ 'BVIF FN))
           (LET*
            ((TEST (IF (EQ 'BVIF FN)
                       (SECOND ARGS)
                       (FIRST ARGS)))
             (TEST-QUOTEP (QUOTEP TEST))
             (TEST-RESULT
              (IF TEST-QUOTEP NIL
                  (AREF1 EVAL-ARRAY-NAME EVAL-ARRAY TEST)))
             (TEST-DONE (OR TEST-QUOTEP TEST-RESULT)))
            (IF
             (NOT TEST-DONE)
             (EVAL-DAG-WITH-LEN-EVALUATOR
              (CONS TEST NODENUM-WORKLIST)
              DAG-ARRAY-NAME DAG-ARRAY VAR-VALUE-ALIST
              EVAL-ARRAY-NAME EVAL-ARRAY
              INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
             (LET*
              ((TEST-VAL (IF TEST-QUOTEP (UNQUOTE TEST)
                             (CAR TEST-RESULT)))
               (RELEVANT-BRANCH
                (IF (EQ 'BVIF FN)
                    (IF TEST-VAL (THIRD ARGS) (FOURTH ARGS))
                    (IF TEST-VAL (SECOND ARGS)
                        (THIRD ARGS))))
               (QUOTEP-RELEVANT-BRANCH (QUOTEP RELEVANT-BRANCH))
               (RELEVANT-BRANCH-RESULT
                (IF QUOTEP-RELEVANT-BRANCH NIL
                    (AREF1 EVAL-ARRAY-NAME
                           EVAL-ARRAY RELEVANT-BRANCH)))
               (RELEVANT-BRANCH-DONE
                (OR QUOTEP-RELEVANT-BRANCH
                    RELEVANT-BRANCH-RESULT)))
              (IF
               (NOT RELEVANT-BRANCH-DONE)
               (EVAL-DAG-WITH-LEN-EVALUATOR
                (CONS RELEVANT-BRANCH NODENUM-WORKLIST)
                DAG-ARRAY-NAME DAG-ARRAY VAR-VALUE-ALIST
                EVAL-ARRAY-NAME EVAL-ARRAY
                INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
               (LET*
                ((BVIFP (EQ FN 'BVIF))
                 (SIZE (AND BVIFP (FIRST ARGS)))
                 (SIZE-QUOTEP (AND BVIFP (QUOTEP SIZE)))
                 (SIZE-RESULT
                  (AND BVIFP (NOT SIZE-QUOTEP)
                       (AREF1 EVAL-ARRAY-NAME EVAL-ARRAY SIZE)))
                 (BVIF-AND-SIZE-NOT-DONE
                  (AND BVIFP
                       (NOT (OR SIZE-QUOTEP SIZE-RESULT)))))
                (IF
                 BVIF-AND-SIZE-NOT-DONE
                 (EVAL-DAG-WITH-LEN-EVALUATOR
                  (CONS SIZE NODENUM-WORKLIST)
                  DAG-ARRAY-NAME DAG-ARRAY VAR-VALUE-ALIST
                  EVAL-ARRAY-NAME EVAL-ARRAY
                  INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
                 (LET*
                  ((RELEVANT-BRANCH-VALUE
                    (IF QUOTEP-RELEVANT-BRANCH
                        (UNQUOTE RELEVANT-BRANCH)
                        (CAR RELEVANT-BRANCH-RESULT)))
                   (VALUE
                    (IF (EQ FN 'BVIF)
                        (BVCHOP (IF SIZE-QUOTEP (UNQUOTE SIZE)
                                    (CAR SIZE-RESULT))
                                RELEVANT-BRANCH-VALUE)
                        RELEVANT-BRANCH-VALUE)))
                  (EVAL-DAG-WITH-LEN-EVALUATOR
                   (CDR NODENUM-WORKLIST)
                   DAG-ARRAY-NAME DAG-ARRAY
                   VAR-VALUE-ALIST EVAL-ARRAY-NAME
                   (ASET1 EVAL-ARRAY-NAME
                          EVAL-ARRAY NODENUM (CONS VALUE NIL))
                   INTERPRETED-FUNCTION-ALIST
                   ARRAY-DEPTH))))))))
           (MV-LET
             (NODENUM-WORKLIST WORKLIST-EXTENDEDP)
             (GET-ARGS-NOT-DONE-ARRAY
              ARGS EVAL-ARRAY-NAME
              EVAL-ARRAY NODENUM-WORKLIST NIL)
             (IF
              WORKLIST-EXTENDEDP
              (EVAL-DAG-WITH-LEN-EVALUATOR
               NODENUM-WORKLIST
               DAG-ARRAY-NAME DAG-ARRAY VAR-VALUE-ALIST
               EVAL-ARRAY-NAME EVAL-ARRAY
               INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
              (LET*
               ((ARG-VALUES
                 (GET-VALS-OF-ARGS-ARRAY
                  ARGS EVAL-ARRAY-NAME EVAL-ARRAY))
                (VALUE
                 (APPLY-LEN-EVALUATOR
                  FN ARG-VALUES INTERPRETED-FUNCTION-ALIST
                  ARRAY-DEPTH)))
               (EVAL-DAG-WITH-LEN-EVALUATOR
                (CDR NODENUM-WORKLIST)
                DAG-ARRAY-NAME DAG-ARRAY
                VAR-VALUE-ALIST EVAL-ARRAY-NAME
                (ASET1 EVAL-ARRAY-NAME
                       EVAL-ARRAY NODENUM (CONS VALUE NIL))
                INTERPRETED-FUNCTION-ALIST
                ARRAY-DEPTH))))))))))))) ;end of mut-rec


 (DEFUN APPLY-LEN-EVALUATOR-TO-QUOTED-ARGS (FN ARGS
                                               INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
   (DECLARE (XARGS :GUARD (AND (OR (SYMBOLP FN) (PSEUDO-LAMBDAP FN))
                               (TRUE-LISTP ARGS)
                               (ALL-MYQUOTEP ARGS)
                               (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
                               (NATP ARRAY-DEPTH))
                   :VERIFY-GUARDS NIL))
   (IF
    (CONSP FN)
    (LET*
     ((FORMALS (SECOND FN))
      (BODY (THIRD FN))
      (ALIST (PAIRLIS$-FAST FORMALS (UNQUOTE-LIST ARGS))))
     (EVAL-LEN-EVALUATOR
      ALIST BODY
      INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH))
    (LET
     ((ARGS-TO-WALK-DOWN ARGS))
     (MV-LET
       (HIT VAL)
       (IF
        (ENDP ARGS-TO-WALK-DOWN)
        (MV NIL NIL)
        (LET
         ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
         (IF
          (ENDP ARGS-TO-WALK-DOWN)
          (LET ((ARG1 (UNQUOTE (NTH 0 ARGS))))
               (IF (EQ 'CDR FN)
                   (MV T (CDR ARG1))
                   (IF (EQ 'CONSP FN)
                       (MV T (CONSP ARG1))
                       (IF (EQ 'LEN FN)
                           (MV T (LEN ARG1))
                           (MV NIL NIL)))))
          (LET
           ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
           (IF
            (ENDP ARGS-TO-WALK-DOWN)
            (LET ((ARG2 (UNQUOTE (NTH 1 ARGS)))
                  (ARG1 (UNQUOTE (NTH 0 ARGS))))
                 (IF (EQ 'BINARY-+ FN)
                     (MV T (BINARY-+ ARG1 ARG2))
                     (MV NIL NIL)))
            (LET
             ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
             (IF
              (ENDP ARGS-TO-WALK-DOWN)
              (MV NIL NIL)
              (LET
               ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
               (IF
                (ENDP ARGS-TO-WALK-DOWN)
                (LET
                 ((ARG4 (UNQUOTE (NTH 3 ARGS)))
                  (ARG3 (UNQUOTE (NTH 2 ARGS)))
                  (ARG2 (UNQUOTE (NTH 1 ARGS)))
                  (ARG1 (UNQUOTE (NTH 0 ARGS))))
                 (DECLARE (IGNORE ARG4))
                 (IF
                  (EQ 'APPLY-LEN-EVALUATOR FN)
                  (MV T
                      (APPLY-LEN-EVALUATOR
                       ARG1 ARG2 ARG3 ARRAY-DEPTH))
                  (IF (EQ 'DAG-VAL-WITH-LEN-EVALUATOR FN)
                      (MV T
                          (DAG-VAL-WITH-LEN-EVALUATOR
                           ARG1 ARG2 ARG3 (+ 1 ARRAY-DEPTH)))
                      (MV NIL NIL))))
                (LET
                 ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                 (IF
                  (ENDP ARGS-TO-WALK-DOWN)
                  (MV NIL NIL)
                  (LET
                   ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                   (IF
                    (ENDP ARGS-TO-WALK-DOWN)
                    (MV NIL NIL)
                    (LET
                     ((ARGS-TO-WALK-DOWN
                       (CDR ARGS-TO-WALK-DOWN)))
                     (IF
                      (ENDP ARGS-TO-WALK-DOWN)
                      (MV NIL NIL)
                      (LET
                       ((ARGS-TO-WALK-DOWN
                         (CDR ARGS-TO-WALK-DOWN)))
                       (IF
                        (ENDP ARGS-TO-WALK-DOWN)
                        (LET
                         ((ARG8 (UNQUOTE (NTH 7 ARGS)))
                          (ARG7 (UNQUOTE (NTH 6 ARGS)))
                          (ARG6 (UNQUOTE (NTH 5 ARGS)))
                          (ARG5 (UNQUOTE (NTH 4 ARGS)))
                          (ARG4 (UNQUOTE (NTH 3 ARGS)))
                          (ARG3 (UNQUOTE (NTH 2 ARGS)))
                          (ARG2 (UNQUOTE (NTH 1 ARGS)))
                          (ARG1 (UNQUOTE (NTH 0 ARGS))))
                         (DECLARE (IGNORE ARG8))
                         (IF
                          (EQ 'EVAL-DAG-WITH-LEN-EVALUATOR FN)
                          (MV
                           T
                           (EVAL-DAG-WITH-LEN-EVALUATOR
                            ARG1 ARG2 ARG3
                            ARG4 ARG5 ARG6 ARG7 ARRAY-DEPTH))
                          (MV NIL NIL)))
                        (MV NIL NIL))))))))))))))))))
       (IF
        HIT VAL
        (LET
         ((MATCH (ASSOC-EQ FN INTERPRETED-FUNCTION-ALIST)))
         (IF
          (NOT MATCH)
          (ER
           HARD?
           'APPLY-LEN-EVALUATOR-TO-QUOTED-ARGS
           "Unknown function: ~x0 applied to args ~x1 (pass it as an interpreted function, or add to the list of built-ins, or check the arity of the call)."
           FN ARGS)
          (LET*
           ((FN-INFO (CDR MATCH))
            (FORMALS (FIRST FN-INFO))
            (BODY (SECOND FN-INFO))
            (ALIST
             (PAIRLIS$-FAST FORMALS (UNQUOTE-LIST ARGS))))
           (EVAL-LEN-EVALUATOR
            ALIST BODY INTERPRETED-FUNCTION-ALIST
            ARRAY-DEPTH))))))))))
