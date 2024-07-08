; Tests of make-evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
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
                   (case fn
                     (len (mv t (len arg1)))
                     (consp (mv t (consp arg1)))
                     (cdr (mv t (cdr arg1)))
                     (t (mv nil nil))))
              (LET
               ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
               (IF
                (ENDP ARGS-TO-WALK-DOWN)
                (LET ((ARG2 (NTH 1 ARGS))
                      (ARG1 (NTH 0 ARGS)))
                     (case fn
                       (binary-+ (mv t (binary-+ arg1 arg2)))
                       (t (mv nil nil))))
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
                     (case fn
                       (dag-val-with-len-evaluator
                         (mv t
                             (dag-val-with-len-evaluator
                               arg1 arg2 arg3 (+ 1 array-depth))))
                       (apply-len-evaluator
                         (mv t
                             (apply-len-evaluator
                               arg1 arg2 arg3 array-depth)))
                       (t (mv nil nil))))
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
                             (case fn
                               (eval-dag-with-len-evaluator
                                 (mv
                                   t
                                   (eval-dag-with-len-evaluator
                                     arg1 arg2 arg3
                                     arg4 arg5 arg6 arg7 array-depth)))
                               (t (mv nil nil))))
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
                (< (LEN DAG) *max-1d-array-length*)))
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
          ((DARGS (DARGS EXPR)))
          (IF
           (OR (EQ 'IF FN)
               (EQ 'MYIF FN)
               (EQ 'BVIF FN))
           (LET*
            ((TEST (IF (EQ 'BVIF FN)
                       (SECOND DARGS)
                       (FIRST DARGS)))
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
                    (IF TEST-VAL (THIRD DARGS) (FOURTH DARGS))
                    (IF TEST-VAL (SECOND DARGS)
                        (THIRD DARGS))))
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
                 (SIZE (AND BVIFP (FIRST DARGS)))
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
              DARGS EVAL-ARRAY-NAME
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
                  DARGS EVAL-ARRAY-NAME EVAL-ARRAY))
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


 (defun apply-len-evaluator-to-quoted-args (fn args
                                               interpreted-function-alist array-depth)
   (declare (xargs :guard (and (or (symbolp fn) (pseudo-lambdap fn))
                               (true-listp args)
                               (all-myquotep args)
                               (interpreted-function-alistp interpreted-function-alist)
                               (natp array-depth))
                   :verify-guards nil))
   (if
    (consp fn)
    (let*
     ((formals (second fn))
      (body (third fn))
      (alist (pairlis$-fast formals (unquote-list args))))
     (eval-len-evaluator
      alist body
      interpreted-function-alist array-depth))
    (let
     ((args-to-walk-down args))
     (mv-let
       (hit val)
       (if
        (endp args-to-walk-down)
        (mv nil nil)
        (let
         ((args-to-walk-down (cdr args-to-walk-down)))
         (if
          (endp args-to-walk-down)
          (let ((arg1 (unquote (nth 0 args))))
               (case fn
                 (len (mv t (len arg1)))
                 (consp (mv t (consp arg1)))
                 (cdr (mv t (cdr arg1)))
                 (t (mv nil nil))))
          (let
           ((args-to-walk-down (cdr args-to-walk-down)))
           (if
            (endp args-to-walk-down)
            (let ((arg2 (unquote (nth 1 args)))
                  (arg1 (unquote (nth 0 args))))
                 (case fn
                   (binary-+ (mv t (binary-+ arg1 arg2)))
                   (t (mv nil nil))))
            (let
             ((args-to-walk-down (cdr args-to-walk-down)))
             (if
              (endp args-to-walk-down)
              (mv nil nil)
              (let
               ((args-to-walk-down (cdr args-to-walk-down)))
               (if
                (endp args-to-walk-down)
                (let
                 ((arg4 (unquote (nth 3 args)))
                  (arg3 (unquote (nth 2 args)))
                  (arg2 (unquote (nth 1 args)))
                  (arg1 (unquote (nth 0 args))))
                 (declare (ignore arg4))
                 (case fn
                    (dag-val-with-len-evaluator
                      (mv t
                          (dag-val-with-len-evaluator
                            arg1 arg2 arg3 (+ 1 array-depth))))
                    (apply-len-evaluator
                      (mv t
                          (apply-len-evaluator
                            arg1 arg2 arg3 array-depth)))
                    (t (mv nil nil))))
                (let
                 ((args-to-walk-down (cdr args-to-walk-down)))
                 (if
                  (endp args-to-walk-down)
                  (mv nil nil)
                  (let
                   ((args-to-walk-down (cdr args-to-walk-down)))
                   (if
                    (endp args-to-walk-down)
                    (mv nil nil)
                    (let
                     ((args-to-walk-down
                       (cdr args-to-walk-down)))
                     (if
                      (endp args-to-walk-down)
                      (mv nil nil)
                      (let
                       ((args-to-walk-down
                         (cdr args-to-walk-down)))
                       (if
                        (endp args-to-walk-down)
                        (let
                         ((arg8 (unquote (nth 7 args)))
                          (arg7 (unquote (nth 6 args)))
                          (arg6 (unquote (nth 5 args)))
                          (arg5 (unquote (nth 4 args)))
                          (arg4 (unquote (nth 3 args)))
                          (arg3 (unquote (nth 2 args)))
                          (arg2 (unquote (nth 1 args)))
                          (arg1 (unquote (nth 0 args))))
                         (declare (ignore arg8))
                         (case fn
                           (eval-dag-with-len-evaluator
                             (mv
                               t
                               (eval-dag-with-len-evaluator
                                 arg1 arg2 arg3
                                 arg4 arg5 arg6 arg7 array-depth)))
                           (t (mv nil nil))))
                        (mv nil nil))))))))))))))))))
       (if
        hit val
        (let
         ((match (assoc-eq fn interpreted-function-alist)))
         (if
          (not match)
          (er
           hard?
           'apply-len-evaluator-to-quoted-args
           "Unknown function: ~x0 applied to args ~x1 (pass it as an interpreted function, or add to the list of built-ins, or check the arity of the call)."
           fn args)
          (let*
           ((fn-info (cdr match))
            (formals (first fn-info))
            (body (second fn-info))
            (alist
             (pairlis$-fast formals (unquote-list args))))
           (eval-len-evaluator
            alist body interpreted-function-alist
            array-depth))))))))))
