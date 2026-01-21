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
  (defund apply-len-evaluator (fn args interpreted-function-alist array-depth)
    (declare (xargs :measure 1
                    :guard (and (or (symbolp fn) (pseudo-lambdap fn))
                                (true-listp args)
                                (interpreted-function-alistp interpreted-function-alist)
                                (natp array-depth))))
    (if (consp fn) ; todo: do we sometimes know that things are lambda-free?
        (let* ((formals (second fn))
               (body (third fn))
               (alist (pairlis$-fast formals args))) ;todo: avoid this?
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
              (let ((arg1 (nth 0 args)))
                   (case fn
                     (len (mv t (len arg1)))
                     (consp (mv t (consp arg1)))
                     (cdr (mv t (cdr arg1)))
                     (t (mv nil nil))))
              (let
               ((args-to-walk-down (cdr args-to-walk-down)))
               (if
                (endp args-to-walk-down)
                (let ((arg2 (nth 1 args))
                      (arg1 (nth 0 args)))
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
                     ((arg4 (nth 3 args)) ;todo: optimize stuff like this
                      (arg3 (nth 2 args))
                      (arg2 (nth 1 args))
                      (arg1 (nth 0 args)))
                     (declare (ignore arg4)) ;todo: why?  don't compute
                     (case fn
                       (dag-val-with-len-evaluator
                         (mv t
                             (eval-in-logic (dag-val-with-len-evaluator arg1 arg2 arg3 (+ 1 array-depth)))))
                       (apply-len-evaluator
                         (mv t
                             (eval-in-logic (apply-len-evaluator arg1 arg2 arg3 array-depth))))
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
                             ((arg8 (nth 7 args))
                              (arg7 (nth 6 args))
                              (arg6 (nth 5 args))
                              (arg5 (nth 4 args))
                              (arg4 (nth 3 args))
                              (arg3 (nth 2 args))
                              (arg2 (nth 1 args))
                              (arg1 (nth 0 args)))
                             (declare (ignore arg8))
                             (case fn
                               (eval-dag-with-len-evaluator
                                 (mv
                                   t
                                   (eval-in-logic (eval-dag-with-len-evaluator
                                                    arg1 arg2 arg3
                                                    arg4 arg5 arg6 arg7 array-depth))))
                               (t (mv nil nil))))
                            (mv nil nil))))))))))))))))))
           (if
            hit val
            (let
             ((match (assoc-eq fn interpreted-function-alist)))
             (if
              (not match)
              (er
               hard? 'apply-len-evaluator
               "Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)"
               fn args 'len-evaluator)
              (let* ((fn-info (cdr match))
                     (formals (first fn-info))
                     (body (second fn-info))
                     (alist (pairlis$-fast formals args)))
                    (eval-len-evaluator
                     alist body interpreted-function-alist
                     array-depth)))))))))
  (defun eval-len-evaluator (alist form interpreted-function-alist array-depth)
    (declare
     (xargs
      :verify-guards nil
      :guard
      (and
       (symbol-alistp alist)
       (pseudo-termp form)
       (interpreted-function-alistp interpreted-function-alist)
       (natp array-depth))))
    (cond
     ((variablep form)
      (lookup-eq form alist))
     ((fquotep form) (unquote form))
     (t
      (let
       ((fn (ffn-symb form)))
       (if
        (and (or (eq fn 'if) (eq fn 'myif))
             (= 3 (len (fargs form))))
        (let*
         ((test-form (farg1 form))
          (test-result (eval-len-evaluator
                        alist
                        test-form interpreted-function-alist
                        array-depth)))
         (eval-len-evaluator
          alist
          (if test-result (farg2 form)
              (farg3 form))
          interpreted-function-alist array-depth))
        (let
         ((args
           (eval-list-len-evaluator alist (fargs form)
                                    interpreted-function-alist
                                    array-depth)))
         (apply-len-evaluator fn args interpreted-function-alist
                              array-depth)))))))
  (defun
    eval-list-len-evaluator
    (alist form-lst
           interpreted-function-alist array-depth)
    (declare
     (xargs
      :verify-guards nil
      :measure (len form-lst)
      :guard
      (and
       (symbol-alistp alist)
       (pseudo-term-listp form-lst)
       (interpreted-function-alistp interpreted-function-alist)
       (natp array-depth))))
    (if
     (endp form-lst)
     nil
     (cons (eval-len-evaluator
            alist (car form-lst)
            interpreted-function-alist array-depth)
           (eval-list-len-evaluator alist (cdr form-lst)
                                    interpreted-function-alist
                                    array-depth))))
  (defun
    dag-val-with-len-evaluator
    (dag alist
         interpreted-function-alist array-depth)
    (declare
     (xargs
      :measure 0
      :guard
      (and
       (or (myquotep dag)
           (and (pseudo-dagp dag)
                (< (len dag) *max-1d-array-length*)))
       (symbol-alistp alist)
       (interpreted-function-alistp interpreted-function-alist)
       (natp array-depth))))
    (if
     (quotep dag)
     (unquote dag)
     (let*
      ((top-nodenum (top-nodenum-of-dag dag))
       (dag-array-name (pack$ 'dag-array-
                              array-depth '-for-dag-val))
       (dag-array (make-into-array dag-array-name dag))
       (eval-array-name (pack$ 'eval-array-
                               array-depth '-for-dag-val))
       (eval-array
        (make-empty-array eval-array-name (+ 1 top-nodenum))))
      (car (aref1 eval-array-name
                  (eval-dag-with-len-evaluator
                   (list top-nodenum)
                   dag-array-name dag-array
                   alist eval-array-name eval-array
                   interpreted-function-alist array-depth)
                  top-nodenum)))))
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
          (IF (or (and (or (eq 'if fn)
                           (eq 'myif fn))
                       (= 3 (len dargs)))
                  (and (eq 'bvif fn)
                       (= 4 (len dargs))))
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
                          (eval-in-logic (dag-val-with-len-evaluator arg1 arg2 arg3 (+ 1 array-depth)))))
                    (apply-len-evaluator
                      (mv t
                          (eval-in-logic (apply-len-evaluator arg1 arg2 arg3 array-depth))))
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
                               (eval-in-logic (eval-dag-with-len-evaluator
                                                arg1 arg2 arg3
                                                arg4 arg5 arg6 arg7 array-depth))))
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
