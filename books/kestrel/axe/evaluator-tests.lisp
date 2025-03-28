; Tests of the evaluator
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

(include-book "evaluator")
(include-book "std/testing/must-be-redundant" :dir :system)

(must-be-redundant
 (MUTUAL-RECURSION
  (DEFUND APPLY-AXE-EVALUATOR (FN ARGS INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
    (DECLARE
     (XARGS
      :MEASURE 1
      :GUARD
      (AND
       (OR (SYMBOLP FN) (PSEUDO-LAMBDAP FN))
       (TRUE-LISTP ARGS)
       (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
       (NATP ARRAY-DEPTH))))
    (IF
     (CONSP FN)
     (LET* ((FORMALS (SECOND FN))
            (BODY (THIRD FN))
            (ALIST (PAIRLIS$-FAST FORMALS ARGS)))
           (EVAL-AXE-EVALUATOR
            ALIST BODY
            INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH))
     (LET
      ((ARGS-TO-WALK-DOWN ARGS))
      (MV-LET
        (HIT VAL)
        (IF
         (ENDP ARGS-TO-WALK-DOWN)
         (MV NIL NIL)
         (let ((args-to-walk-down (cdr args-to-walk-down)))
                      (if
                       (endp args-to-walk-down)
                       (let ((arg1 (nth 0 args)))
                        (case fn
                          (quotep (mv t (quotep arg1)))
                          (natp (mv t (natp arg1)))
                          (posp (mv t (posp arg1)))
                          (integerp (mv t (integerp arg1)))
                          (rationalp (mv t (rationalp arg1)))
                          (print-constant (mv t (print-constant arg1)))
                          (not (mv t (not arg1)))
                          (power-of-2p (mv t (power-of-2p arg1)))
                          (lg (mv t (lg-unguarded arg1)))
                          (bool-to-bit (mv t (bool-to-bit arg1)))
                          (char-code (mv t (char-code-unguarded arg1)))
                          (code-char (mv t (code-char-unguarded arg1)))
                          (symbol-package-name
                               (mv t (symbol-package-name-unguarded arg1)))
                          (symbol-name (mv t (symbol-name-unguarded arg1)))
                          (all-same (mv t (all-same arg1)))
                          (bool-fix$inline (mv t (bool-fix$inline arg1)))
                          (booleanp (mv t (booleanp arg1)))
                          (list::2set (mv t (list::2set arg1)))
                          (rkeys (mv t (rkeys arg1)))
                          (key-list (mv t (key-list arg1)))
                          (true-list-fix (mv t (true-list-fix arg1)))
                          (all-integerp (mv t (all-integerp arg1)))
                          (no-duplicatesp-equal
                               (mv t (no-duplicatesp-equal-unguarded arg1)))
                          (strip-cdrs (mv t (strip-cdrs-unguarded arg1)))
                          (strip-cars (mv t (strip-cars-unguarded arg1)))
                          (stringp (mv t (stringp arg1)))
                          (true-listp (mv t (true-listp arg1)))
                          (consp (mv t (consp arg1)))
                          (bytes-to-bits (mv t (bytes-to-bits arg1)))
                          (width-of-widest-int
                               (mv t (width-of-widest-int-unguarded arg1)))
                          (all-natp (mv t (all-natp arg1)))
                          (endp (mv t (endp-unguarded arg1)))
                          (bitnot (mv t (bitnot-unguarded arg1)))
                          (logmaskp (mv t (logmaskp arg1)))
                          (integer-length
                               (mv t (integer-length-unguarded arg1)))
                          (ceiling-of-lg
                               (mv t (ceiling-of-lg-unguarded arg1)))
                          (unary-/ (mv t (unary-/-unguarded arg1)))
                          (nfix (mv t (nfix arg1)))
                          (ifix (mv t (ifix arg1)))
                          (len (mv t (len arg1)))
                          (reverse-list (mv t (reverse-list-unguarded arg1)))
                          (acl2-numberp (mv t (acl2-numberp arg1)))
                          (zp (mv t (zp-unguarded arg1)))
                          (unary-- (mv t (unary---unguarded arg1)))
                          (atom (mv t (atom arg1)))
                          (car (mv t (car-unguarded arg1)))
                          (cdr (mv t (cdr-unguarded arg1)))
                          (map-reverse-list (mv t (map-reverse-list-unguarded arg1)))
                          (realpart (mv t (realpart-unguarded arg1)))
                          (imagpart (mv t (imagpart-unguarded arg1)))
                          (symbolp (mv t (symbolp arg1)))
                          (characterp (mv t (characterp arg1)))
                          (complex-rationalp (mv t (complex-rationalp arg1)))
                          (denominator (mv t (denominator-unguarded arg1)))
                          (numerator (mv t (numerator-unguarded arg1)))
                          (t (mv nil nil))))
                       (let ((args-to-walk-down (cdr args-to-walk-down)))
                        (if
                         (endp args-to-walk-down)
                         (let ((arg2 (nth 1 args))
                               (arg1 (nth 0 args)))
                          (case fn
                           (mv-nth (mv t (mv-nth-unguarded arg1 arg2)))
                           (items-have-len
                                (mv t (items-have-len-unguarded arg1 arg2)))
                           (all-all-unsigned-byte-p
                                (mv t (all-all-unsigned-byte-p arg1 arg2)))
                           (add-to-end (mv t (add-to-end arg1 arg2)))
                           (coerce (mv t (coerce-unguarded arg1 arg2)))
                           (< (mv t (<-unguarded arg1 arg2)))
                           (equal (mv t (equal arg1 arg2)))
                           (eql (mv t (equal arg1 arg2)))
                           (= (mv t (equal arg1 arg2)))
                           (list-equiv (mv t (list-equiv arg1 arg2)))
                           (prefixp (mv t (prefixp arg1 arg2)))
                           (lookup-equal (mv t (lookup-equal-unguarded arg1 arg2)))
                           (lookup (mv t (lookup arg1 arg2)))
                           (bvnot (mv t (bvnot-unguarded arg1 arg2)))
                           (bvuminus (mv t (bvuminus-unguarded arg1 arg2)))
                           (assoc-equal
                                (mv t (assoc-equal-unguarded arg1 arg2)))
                           (unsigned-byte-p-forced
                                (mv t (unsigned-byte-p-forced arg1 arg2)))
                           (trim (mv t (trim-unguarded arg1 arg2)))
                           (binary-+ (mv t (binary-+-unguarded arg1 arg2)))
                           ;; (all-items-less-than (mv t (all-items-less-than arg1 arg2)))
                           (every-nth (mv t (every-nth-unguarded arg1 arg2)))
                           (intersection-equal
                                (mv t (intersection-equal-unguarded arg1 arg2)))
                           (all-equal$ (mv t (all-equal$-unguarded arg1 arg2)))
                           (repeatbit (mv t (repeatbit-unguarded arg1 arg2)))
                           (implies (mv t (implies arg1 arg2)))
                           (first-non-member
                                (mv t (first-non-member-unguarded arg1 arg2)))
                           (booland (mv t (booland arg1 arg2)))
                           (boolor (mv t (boolor arg1 arg2)))
                           (getbit-list (mv t (getbit-list-unguarded arg1 arg2)))
                           (set::union (mv t (set::union arg1 arg2)))
                           (leftrotate32
                                (mv t (leftrotate32-unguarded arg1 arg2)))
                           (set::insert (mv t (set::insert arg1 arg2)))
                           (floor (mv t (floor-unguarded arg1 arg2)))
                           (member-equal
                                (mv t (member-equal-unguarded arg1 arg2)))
                           (g (mv t (g arg1 arg2)))
                           (nthcdr (mv t (nthcdr-unguarded arg1 arg2)))
                           (take (mv t (take-unguarded arg1 arg2)))
                           (firstn (mv t (firstn-unguarded arg1 arg2)))
                           (binary-append
                                (mv t (binary-append-unguarded arg1 arg2)))
                           (signed-byte-p (mv t (signed-byte-p arg1 arg2)))
                           (unsigned-byte-p
                                (mv t (unsigned-byte-p arg1 arg2)))
                           (bvchop-list
                                (mv t (bvchop-list-unguarded arg1 arg2)))
                           (all-unsigned-byte-p
                                (mv t (all-unsigned-byte-p arg1 arg2)))
                           (all-signed-byte-p
                                (mv t (all-signed-byte-p arg1 arg2)))
                           (bitor (mv t (bitor-unguarded arg1 arg2)))
                           (bitand (mv t (bitand-unguarded arg1 arg2)))
                           (bitxor (mv t (bitxor-unguarded arg1 arg2)))
                           (expt (mv t (expt-unguarded arg1 arg2)))
                           (min (mv t (min-unguarded arg1 arg2)))
                           (max (mv t (max-unguarded arg1 arg2)))
                           (mod (mv t (mod-unguarded arg1 arg2)))
                           (getbit (mv t (getbit-unguarded arg1 arg2)))
                           (cons (mv t (cons arg1 arg2)))
                           (bvchop (mv t (bvchop-unguarded arg1 arg2)))
                           (logtail$inline
                                (mv t (logtail$inline-unguarded arg1 arg2)))
                           (logext (mv t (logext-unguarded arg1 arg2)))
                           (nth (mv t (nth-unguarded arg1 arg2)))
                           (binary-* (mv t (binary-*-unguarded arg1 arg2)))
                           (bvnot-list
                                (mv t (bvnot-list-unguarded arg1 arg2)))
                           (eq (mv t (equal arg1 arg2)))
                           (ceiling (mv t (ceiling-unguarded arg1 arg2)))
                           (lookup-eq (mv t (lookup-eq arg1 arg2)))
                           (lookup (mv t (lookup arg1 arg2)))
                           (group (mv t (group arg1 arg2)))
                           (group2 (mv t (group2 arg1 arg2)))
                           (set::in (mv t (set::in-unguarded arg1 arg2)))
                           (symbol< (mv t (symbol<-unguarded arg1 arg2)))
                           (t (mv nil nil))))
                         (let ((args-to-walk-down (cdr args-to-walk-down)))
                          (if
                           (endp args-to-walk-down)
                           (let ((arg3 (nth 2 args))
                                 (arg2 (nth 1 args))
                                 (arg1 (nth 0 args)))
                            (case fn
                             (repeat-tail
                                  (mv t (repeat-tail arg1 arg2 arg3)))
                             (negated-elems-listp (mv t
                                                      (negated-elems-listp-unguarded
                                                           arg1 arg2 arg3)))
                             (leftrotate (mv t (leftrotate-unguarded arg1 arg2 arg3)))
                             (acons (mv t (acons-unguarded arg1 arg2 arg3)))
                             (bvshr (mv t (bvshr-unguarded arg1 arg2 arg3)))
                             (bvashr (mv t (bvashr-unguarded arg1 arg2 arg3)))
                             (packbv (mv t (packbv-unguarded arg1 arg2 arg3)))
                             (unpackbv
                                 (mv t
                                     (unpackbv-less-guarded arg1 arg2 arg3)))
;;                             (bvplus-lst (mv t (bvplus-lst arg1 arg2 arg3)))
                             (bvequal
                                  (mv t (bvequal-unguarded arg1 arg2 arg3)))
                             (bvlt (mv t (bvlt-unguarded arg1 arg2 arg3)))
                             (bvle (mv t (bvle-unguarded arg1 arg2 arg3)))
                             (bvxor (mv t (bvxor-unguarded arg1 arg2 arg3)))
                             (bvor (mv t (bvor-unguarded arg1 arg2 arg3)))
                             (bvand (mv t (bvand-unguarded arg1 arg2 arg3)))
                             (bvmult
                                  (mv t (bvmult-unguarded arg1 arg2 arg3)))
                             (bvplus
                                  (mv t (bvplus-unguarded arg1 arg2 arg3)))
                             (bvminus
                                  (mv t (bvminus-unguarded arg1 arg2 arg3)))
                             (bvmod (mv t (bvmod-unguarded arg1 arg2 arg3)))
                             (bvdiv (mv t (bvdiv-unguarded arg1 arg2 arg3)))
                             (bvsx (mv t (bvsx-unguarded arg1 arg2 arg3)))
                             (sbvdiv (mv t (sbvdiv-unguarded arg1 arg2 arg3)))
                             (sbvdivdown (mv t (sbvdivdown arg1 arg2 arg3)))
                             (sbvrem (mv t (sbvrem arg1 arg2 arg3)))
                             (sbvmoddown (mv t (sbvmoddown arg1 arg2 arg3)))
                             (sbvlt
                                 (mv t (sbvlt-unguarded arg1 (ifix arg2) (ifix arg3))))
                             (sbvle (mv t (sbvle-unguarded arg1 arg2 arg3)))
                             (s (mv t (s arg1 arg2 arg3)))
                             (myif (mv t (myif arg1 arg2 arg3)))
                             (boolif (mv t (boolif arg1 arg2 arg3)))
                             (array-elem-2d
                               (mv t (array-elem-2d arg1 arg2 arg3)))
                             (bv-arrayp
                                  (mv t (bv-arrayp arg1 arg2 arg3)))
                             (update-nth (mv t (update-nth-unguarded arg1 arg2 arg3)))
                             (if (mv t (if arg1 arg2 arg3)))
                             (slice
                                  (mv t (slice-unguarded arg1 arg2 arg3)))
                             (bvshl (mv t (bvshl-unguarded arg1 arg2 arg3)))
                             ;; (keep-items-less-than (mv t (keep-items-less-than-unguarded arg1 arg2 arg3)))
                             (subrange (mv t
                                           (subrange-unguarded arg1
                                                               arg2
                                                               arg3)))
                             (bvxor-list
                                  (mv t
                                      (bvxor-list-unguarded arg1 arg2 arg3)))
                             (t (mv nil nil))))
                           (let ((args-to-walk-down (cdr args-to-walk-down)))
                            (if
                             (endp args-to-walk-down)
                             (let ((arg4 (nth 3 args))
                                   (arg3 (nth 2 args))
                                   (arg2 (nth 1 args))
                                   (arg1 (nth 0 args)))
                              (case fn
                               (dag-val-with-axe-evaluator
                                 (mv t
                                     (dag-val-with-axe-evaluator
                                          arg1 arg2 arg3 (+ 1 array-depth))))
                               (apply-axe-evaluator
                                    (mv t
                                        (apply-axe-evaluator
                                             arg1 arg2 arg3 array-depth)))
                               (update-subrange
                                  (mv t
                                      (update-subrange arg1 arg2 arg3 arg4)))
                               (update-nth2
                                    (mv t (update-nth2 arg1 arg2 arg3 arg4)))
                               (bv-array-clear
                                 (mv t (bv-array-clear arg1 arg2 arg3 arg4)))
                               (bvcat
                                  (mv t
                                      (bvcat-unguarded arg1 arg2 arg3 arg4)))
                               (bv-array-read (mv t
                                                  (bv-array-read-unguarded
                                                       arg1 arg2 arg3 arg4)))
                               (bvif
                                 (mv t (bvif-unguarded arg1 arg2 arg3 arg4)))
                               (t (mv nil nil))))
                             (let
                               ((args-to-walk-down (cdr args-to-walk-down)))
                              (if
                               (endp args-to-walk-down)
                               (let ((arg5 (nth 4 args))
                                     (arg4 (nth 3 args))
                                     (arg3 (nth 2 args))
                                     (arg2 (nth 1 args))
                                     (arg1 (nth 0 args)))
                                (case fn
                                 (update-subrange2
                                      (mv t
                                          (update-subrange2
                                               arg1 arg2 arg3 arg4 arg5)))
                                 (bv-array-write
                                   (mv t
                                       (bv-array-write-unguarded (nfix arg1)
                                                                 (nfix arg2)
                                                                 (nfix arg3)
                                                                 arg4 arg5)))
                                 (bv-array-clear-range
                                      (mv t
                                          (bv-array-clear-range
                                               arg1 arg2 arg3 arg4 arg5)))
                                 (t (mv nil nil))))
                               (let
                                ((args-to-walk-down (cdr args-to-walk-down)))
                                (if (endp args-to-walk-down)
                                    (mv nil nil)
                                 (let ((args-to-walk-down
                                            (cdr args-to-walk-down)))
                                  (if (endp args-to-walk-down)
                                      (mv nil nil)
                                   (let ((args-to-walk-down
                                              (cdr args-to-walk-down)))
                                    (if
                                     (endp args-to-walk-down)
                                     (let ((arg8 (nth 7 args))
                                           (arg7 (nth 6 args))
                                           (arg6 (nth 5 args))
                                           (arg5 (nth 4 args))
                                           (arg4 (nth 3 args))
                                           (arg3 (nth 2 args))
                                           (arg2 (nth 1 args))
                                           (arg1 (nth 0 args)))
                                      (declare (ignore arg8))
                                      (case fn
                                       (eval-dag-with-axe-evaluator
                                        (mv
                                         t
                                         (eval-dag-with-axe-evaluator
                                           arg1 arg2 arg3
                                           arg4 arg5 arg6 arg7 array-depth)))
                                       (t (mv nil nil))))
                                     (mv nil nil))))))))))))))))))
        (IF
         HIT VAL
         (LET
          ((MATCH (ASSOC-EQ FN INTERPRETED-FUNCTION-ALIST)))
          (IF
           (NOT MATCH)
           (ER HARD? 'APPLY-AXE-EVALUATOR "Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)"
               FN ARGS 'AXE-EVALUATOR)
           (LET* ((FN-INFO (CDR MATCH))
                  (FORMALS (FIRST FN-INFO))
                  (BODY (SECOND FN-INFO))
                  (ALIST (PAIRLIS$-FAST FORMALS ARGS)))
                 (EVAL-AXE-EVALUATOR
                  ALIST BODY INTERPRETED-FUNCTION-ALIST
                  ARRAY-DEPTH)))))))))
  (DEFUND EVAL-AXE-EVALUATOR (ALIST FORM INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
    (DECLARE (XARGS :VERIFY-GUARDS NIL
                    :GUARD (AND (SYMBOL-ALISTP ALIST)
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
        (AND (OR (EQ FN 'IF) (EQ FN 'MYIF))
             (= 3 (LEN (FARGS FORM))))
        (LET*
         ((TEST-FORM (FARG1 FORM))
          (TEST-RESULT (EVAL-AXE-EVALUATOR
                        ALIST
                        TEST-FORM INTERPRETED-FUNCTION-ALIST
                        ARRAY-DEPTH)))
         (EVAL-AXE-EVALUATOR
          ALIST
          (IF TEST-RESULT
              (FARG2 FORM)
              (FARG3 FORM))
          INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH))
        (LET
         ((ARGS
           (EVAL-LIST-AXE-EVALUATOR ALIST (FARGS FORM)
                                    INTERPRETED-FUNCTION-ALIST
                                    ARRAY-DEPTH)))
         (APPLY-AXE-EVALUATOR FN ARGS INTERPRETED-FUNCTION-ALIST
                              ARRAY-DEPTH)))))))
  (DEFUND
    EVAL-LIST-AXE-EVALUATOR
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
     (CONS (EVAL-AXE-EVALUATOR
            ALIST (CAR FORM-LST)
            INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
           (EVAL-LIST-AXE-EVALUATOR ALIST (CDR FORM-LST)
                                    INTERPRETED-FUNCTION-ALIST
                                    ARRAY-DEPTH))))
  (DEFUND
    DAG-VAL-WITH-AXE-EVALUATOR
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
      ((TOP-NODENUM (TOP-NODENUM-OF-DAG DAG))
       (DAG-ARRAY-NAME (PACK$ 'DAG-ARRAY-
                              ARRAY-DEPTH '-FOR-DAG-VAL))
       (DAG-ARRAY (MAKE-INTO-ARRAY DAG-ARRAY-NAME DAG))
       (EVAL-ARRAY-NAME (PACK$ 'EVAL-ARRAY-
                               ARRAY-DEPTH '-FOR-DAG-VAL))
       (EVAL-ARRAY
        (MAKE-EMPTY-ARRAY EVAL-ARRAY-NAME (+ 1 TOP-NODENUM))))
      (CAR (AREF1 EVAL-ARRAY-NAME
                  (EVAL-DAG-WITH-AXE-EVALUATOR
                   (LIST TOP-NODENUM)
                   DAG-ARRAY-NAME DAG-ARRAY
                   ALIST EVAL-ARRAY-NAME EVAL-ARRAY
                   INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
                  TOP-NODENUM)))))
  (DEFUND
    EVAL-DAG-WITH-AXE-EVALUATOR
    (NODENUM-WORKLIST DAG-ARRAY-NAME DAG-ARRAY VAR-VALUE-ALIST
                      EVAL-ARRAY-NAME EVAL-ARRAY
                      INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
    (DECLARE
     (XARGS
      :GUARD
      (AND
       (NAT-LISTP NODENUM-WORKLIST)
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
            (EVAL-DAG-WITH-AXE-EVALUATOR
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
              (EVAL-DAG-WITH-AXE-EVALUATOR
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
             (EVAL-DAG-WITH-AXE-EVALUATOR
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
               (EVAL-DAG-WITH-AXE-EVALUATOR
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
                 (EVAL-DAG-WITH-AXE-EVALUATOR
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
                  (EVAL-DAG-WITH-AXE-EVALUATOR
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
              (EVAL-DAG-WITH-AXE-EVALUATOR
               NODENUM-WORKLIST
               DAG-ARRAY-NAME DAG-ARRAY VAR-VALUE-ALIST
               EVAL-ARRAY-NAME EVAL-ARRAY
               INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
              (LET*
               ((ARG-VALUES
                 (GET-VALS-OF-ARGS-ARRAY
                  DARGS EVAL-ARRAY-NAME EVAL-ARRAY))
                (VALUE
                 (APPLY-AXE-EVALUATOR
                  FN ARG-VALUES INTERPRETED-FUNCTION-ALIST
                  ARRAY-DEPTH)))
               (EVAL-DAG-WITH-AXE-EVALUATOR
                (CDR NODENUM-WORKLIST)
                DAG-ARRAY-NAME DAG-ARRAY
                VAR-VALUE-ALIST EVAL-ARRAY-NAME
                (ASET1 EVAL-ARRAY-NAME
                       EVAL-ARRAY NODENUM (CONS VALUE NIL))
                INTERPRETED-FUNCTION-ALIST
                ARRAY-DEPTH)))))))))))))

 ;;outside the mutual-recursion:
 (DEFUN APPLY-AXE-EVALUATOR-TO-QUOTED-ARGS (FN ARGS INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
   (DECLARE (XARGS
             :GUARD
             (AND
              (OR (SYMBOLP FN) (PSEUDO-LAMBDAP FN))
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
     (EVAL-AXE-EVALUATOR
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
         (if
                      (endp args-to-walk-down)
                      (let ((arg1 (unquote (nth 0 args))))
                       (case fn
                        (quotep (mv t (quotep arg1)))
                        (natp (mv t (natp arg1)))
                        (posp (mv t (posp arg1)))
                        (integerp (mv t (integerp arg1)))
                        (rationalp (mv t (rationalp arg1)))
                        (print-constant (mv t (print-constant arg1)))
                        (not (mv t (not arg1)))
                        (power-of-2p (mv t (power-of-2p arg1)))
                        (lg (mv t (lg-unguarded arg1)))
                        (bool-to-bit (mv t (bool-to-bit arg1)))
                        (char-code (mv t (char-code-unguarded arg1)))
                        (code-char (mv t (code-char-unguarded arg1)))
                        (symbol-package-name
                             (mv t (symbol-package-name-unguarded arg1)))
                        (symbol-name (mv t (symbol-name-unguarded arg1)))
                        (all-same (mv t (all-same arg1)))
                        (bool-fix$inline (mv t (bool-fix$inline arg1)))
                        (booleanp (mv t (booleanp arg1)))
                        (list::2set (mv t (list::2set arg1)))
                        (rkeys (mv t (rkeys arg1)))
                        (key-list (mv t (key-list arg1)))
                        (true-list-fix (mv t (true-list-fix arg1)))
                        (all-integerp (mv t (all-integerp arg1)))
                        (no-duplicatesp-equal
                             (mv t (no-duplicatesp-equal-unguarded arg1)))
                        (strip-cdrs (mv t (strip-cdrs-unguarded arg1)))
                        (strip-cars (mv t (strip-cars-unguarded arg1)))
                        (stringp (mv t (stringp arg1)))
                        (true-listp (mv t (true-listp arg1)))
                        (consp (mv t (consp arg1)))
                        (bytes-to-bits (mv t (bytes-to-bits arg1)))
                        (width-of-widest-int
                             (mv t (width-of-widest-int-unguarded arg1)))
                        (all-natp (mv t (all-natp arg1)))
                        (endp (mv t (endp-unguarded arg1)))
                        (bitnot (mv t (bitnot-unguarded arg1)))
                        (logmaskp (mv t (logmaskp arg1)))
                        (integer-length
                             (mv t (integer-length-unguarded arg1)))
                        (ceiling-of-lg (mv t (ceiling-of-lg-unguarded arg1)))
                        (unary-/ (mv t (unary-/-unguarded arg1)))
                        (nfix (mv t (nfix arg1)))
                        (ifix (mv t (ifix arg1)))
                        (len (mv t (len arg1)))
                        (reverse-list (mv t (reverse-list-unguarded arg1)))
                        (acl2-numberp (mv t (acl2-numberp arg1)))
                        (zp (mv t (zp-unguarded arg1)))
                        (unary-- (mv t (unary---unguarded arg1)))
                        (atom (mv t (atom arg1)))
                        (car (mv t (car-unguarded arg1)))
                        (cdr (mv t (cdr-unguarded arg1)))
                        (map-reverse-list (mv t (map-reverse-list-unguarded arg1)))
                        (realpart (mv t (realpart-unguarded arg1)))
                        (imagpart (mv t (imagpart-unguarded arg1)))
                        (symbolp (mv t (symbolp arg1)))
                        (characterp (mv t (characterp arg1)))
                        (complex-rationalp (mv t (complex-rationalp arg1)))
                        (denominator (mv t (denominator-unguarded arg1)))
                        (numerator (mv t (numerator-unguarded arg1)))
                        (t (mv nil nil))))
                      (let ((args-to-walk-down (cdr args-to-walk-down)))
                       (if
                        (endp args-to-walk-down)
                        (let ((arg2 (unquote (nth 1 args)))
                              (arg1 (unquote (nth 0 args))))
                         (case fn
                           (mv-nth (mv t (mv-nth-unguarded arg1 arg2)))
                           (items-have-len
                                (mv t (items-have-len-unguarded arg1 arg2)))
                           (all-all-unsigned-byte-p
                                (mv t (all-all-unsigned-byte-p arg1 arg2)))
                           (add-to-end (mv t (add-to-end arg1 arg2)))
                           (coerce (mv t (coerce-unguarded arg1 arg2)))
                           (< (mv t (<-unguarded arg1 arg2)))
                           (equal (mv t (equal arg1 arg2)))
                           (eql (mv t (equal arg1 arg2)))
                           (= (mv t (equal arg1 arg2)))
                           (list-equiv (mv t (list-equiv arg1 arg2)))
                           (prefixp (mv t (prefixp arg1 arg2)))
                           (lookup-equal (mv t (lookup-equal-unguarded arg1 arg2)))
                           (lookup (mv t (lookup arg1 arg2)))
                           (bvnot (mv t (bvnot-unguarded arg1 arg2)))
                           (bvuminus (mv t (bvuminus-unguarded arg1 arg2)))
                           (assoc-equal
                                (mv t (assoc-equal-unguarded arg1 arg2)))
                           (unsigned-byte-p-forced
                                (mv t (unsigned-byte-p-forced arg1 arg2)))
                           (trim (mv t (trim-unguarded arg1 arg2)))
                           (binary-+ (mv t (binary-+-unguarded arg1 arg2)))
                           ;; (all-items-less-than (mv t (all-items-less-than arg1 arg2)))
                           (every-nth (mv t (every-nth-unguarded arg1 arg2)))
                           (intersection-equal
                                (mv t (intersection-equal-unguarded arg1 arg2)))
                           (all-equal$ (mv t (all-equal$-unguarded arg1 arg2)))
                           (repeatbit (mv t (repeatbit-unguarded arg1 arg2)))
                           (implies (mv t (implies arg1 arg2)))
                           (first-non-member
                                (mv t (first-non-member-unguarded arg1 arg2)))
                           (booland (mv t (booland arg1 arg2)))
                           (boolor (mv t (boolor arg1 arg2)))
                           (getbit-list (mv t (getbit-list-unguarded arg1 arg2)))
                           (set::union (mv t (set::union arg1 arg2)))
                           (leftrotate32
                                (mv t (leftrotate32-unguarded arg1 arg2)))
                           (set::insert (mv t (set::insert arg1 arg2)))
                           (floor (mv t (floor-unguarded arg1 arg2)))
                           (member-equal
                                (mv t (member-equal-unguarded arg1 arg2)))
                           (g (mv t (g arg1 arg2)))
                           (nthcdr (mv t (nthcdr-unguarded arg1 arg2)))
                           (take (mv t (take-unguarded arg1 arg2)))
                           (firstn (mv t (firstn-unguarded arg1 arg2)))
                           (binary-append
                                (mv t (binary-append-unguarded arg1 arg2)))
                           (signed-byte-p (mv t (signed-byte-p arg1 arg2)))
                           (unsigned-byte-p
                                (mv t (unsigned-byte-p arg1 arg2)))
                           (bvchop-list
                                (mv t (bvchop-list-unguarded arg1 arg2)))
                           (all-unsigned-byte-p
                                (mv t (all-unsigned-byte-p arg1 arg2)))
                           (all-signed-byte-p
                                (mv t (all-signed-byte-p arg1 arg2)))
                           (bitor (mv t (bitor-unguarded arg1 arg2)))
                           (bitand (mv t (bitand-unguarded arg1 arg2)))
                           (bitxor (mv t (bitxor-unguarded arg1 arg2)))
                           (expt (mv t (expt-unguarded arg1 arg2)))
                           (min (mv t (min-unguarded arg1 arg2)))
                           (max (mv t (max-unguarded arg1 arg2)))
                           (mod (mv t (mod-unguarded arg1 arg2)))
                           (getbit (mv t (getbit-unguarded arg1 arg2)))
                           (cons (mv t (cons arg1 arg2)))
                           (bvchop (mv t (bvchop-unguarded arg1 arg2)))
                           (logtail$inline
                                (mv t (logtail$inline-unguarded arg1 arg2)))
                           (logext (mv t (logext-unguarded arg1 arg2)))
                           (nth (mv t (nth-unguarded arg1 arg2)))
                           (binary-* (mv t (binary-*-unguarded arg1 arg2)))
                           (bvnot-list
                                (mv t (bvnot-list-unguarded arg1 arg2)))
                           (eq (mv t (equal arg1 arg2)))
                           (ceiling (mv t (ceiling-unguarded arg1 arg2)))
                           (lookup-eq (mv t (lookup-eq arg1 arg2)))
                           (lookup (mv t (lookup arg1 arg2)))
                           (group (mv t (group arg1 arg2)))
                           (group2 (mv t (group2 arg1 arg2)))
                           (set::in (mv t (set::in-unguarded arg1 arg2)))
                           (symbol< (mv t (symbol<-unguarded arg1 arg2)))
                           (t (mv nil nil))))
                        (let ((args-to-walk-down (cdr args-to-walk-down)))
                         (if
                          (endp args-to-walk-down)
                          (let ((arg3 (unquote (nth 2 args)))
                                (arg2 (unquote (nth 1 args)))
                                (arg1 (unquote (nth 0 args))))
                           (case fn
                            (repeat-tail (mv t (repeat-tail arg1 arg2 arg3)))
                            (negated-elems-listp (mv t
                                                     (negated-elems-listp-unguarded
                                                          arg1 arg2 arg3)))
                            (leftrotate (mv t (leftrotate-unguarded arg1 arg2 arg3)))
                            (acons (mv t (acons-unguarded arg1 arg2 arg3)))
                            (bvshr (mv t (bvshr-unguarded arg1 arg2 arg3)))
                            (bvashr (mv t (bvashr-unguarded arg1 arg2 arg3)))
                            (packbv (mv t (packbv-unguarded arg1 arg2 arg3)))
                            (unpackbv
                                 (mv t
                                     (unpackbv-less-guarded arg1 arg2 arg3)))
;;                            (bvplus-lst (mv t (bvplus-lst arg1 arg2 arg3)))
                            (bvequal
                                 (mv t (bvequal-unguarded arg1 arg2 arg3)))
                            (bvlt (mv t (bvlt-unguarded arg1 arg2 arg3)))
                            (bvle (mv t (bvle-unguarded arg1 arg2 arg3)))
                            (bvxor (mv t (bvxor-unguarded arg1 arg2 arg3)))
                            (bvor (mv t (bvor-unguarded arg1 arg2 arg3)))
                            (bvand (mv t (bvand-unguarded arg1 arg2 arg3)))
                            (bvmult (mv t (bvmult-unguarded arg1 arg2 arg3)))
                            (bvplus (mv t (bvplus-unguarded arg1 arg2 arg3)))
                            (bvminus
                                 (mv t (bvminus-unguarded arg1 arg2 arg3)))
                            (bvmod (mv t (bvmod-unguarded arg1 arg2 arg3)))
                            (bvdiv (mv t (bvdiv-unguarded arg1 arg2 arg3)))
                            (bvsx (mv t (bvsx-unguarded arg1 arg2 arg3)))
                            (sbvdiv (mv t (sbvdiv-unguarded arg1 arg2 arg3)))
                            (sbvdivdown (mv t (sbvdivdown arg1 arg2 arg3)))
                            (sbvrem (mv t (sbvrem arg1 arg2 arg3)))
                            (sbvmoddown (mv t (sbvmoddown arg1 arg2 arg3)))
                            (sbvlt
                                 (mv t (sbvlt-unguarded arg1 (ifix arg2) (ifix arg3))))
                            (sbvle (mv t (sbvle-unguarded arg1 arg2 arg3)))
                            (s (mv t (s arg1 arg2 arg3)))
                            (myif (mv t (myif arg1 arg2 arg3)))
                            (boolif (mv t (boolif arg1 arg2 arg3)))
                            (array-elem-2d
                              (mv t (array-elem-2d arg1 arg2 arg3)))
                            (bv-arrayp
                                 (mv t (bv-arrayp arg1 arg2 arg3)))
                            (update-nth (mv t (update-nth-unguarded arg1 arg2 arg3)))
                            (if (mv t (if arg1 arg2 arg3)))
                            (slice
                                 (mv t (slice-unguarded arg1 arg2 arg3)))
                            (bvshl (mv t (bvshl-unguarded arg1 arg2 arg3)))
                            ;; (keep-items-less-than (mv t (keep-items-less-than-unguarded arg1 arg2 arg3)))
                            (subrange (mv t
                                          (subrange-unguarded arg1
                                                              arg2
                                                              arg3)))
                            (bvxor-list
                                 (mv t
                                     (bvxor-list-unguarded arg1 arg2 arg3)))
                            (t (mv nil nil))))
                          (let ((args-to-walk-down (cdr args-to-walk-down)))
                           (if
                            (endp args-to-walk-down)
                            (let ((arg4 (unquote (nth 3 args)))
                                  (arg3 (unquote (nth 2 args)))
                                  (arg2 (unquote (nth 1 args)))
                                  (arg1 (unquote (nth 0 args))))
                             (case fn
                              (dag-val-with-axe-evaluator
                                 (mv t
                                     (dag-val-with-axe-evaluator
                                          arg1 arg2 arg3 (+ 1 array-depth))))
                              (apply-axe-evaluator
                                   (mv t
                                       (apply-axe-evaluator
                                            arg1 arg2 arg3 array-depth)))
                              (update-subrange
                                  (mv t
                                      (update-subrange arg1 arg2 arg3 arg4)))
                              (update-nth2
                                   (mv t (update-nth2 arg1 arg2 arg3 arg4)))
                              (bv-array-clear
                                 (mv t (bv-array-clear arg1 arg2 arg3 arg4)))
                              (bvcat
                                  (mv t
                                      (bvcat-unguarded arg1 arg2 arg3 arg4)))
                              (bv-array-read (mv t
                                                 (bv-array-read-unguarded
                                                      arg1 arg2 arg3 arg4)))
                              (bvif
                                 (mv t (bvif-unguarded arg1 arg2 arg3 arg4)))
                              (t (mv nil nil))))
                            (let
                               ((args-to-walk-down (cdr args-to-walk-down)))
                             (if
                              (endp args-to-walk-down)
                              (let ((arg5 (unquote (nth 4 args)))
                                    (arg4 (unquote (nth 3 args)))
                                    (arg3 (unquote (nth 2 args)))
                                    (arg2 (unquote (nth 1 args)))
                                    (arg1 (unquote (nth 0 args))))
                               (case fn
                                (update-subrange2
                                     (mv t
                                         (update-subrange2
                                              arg1 arg2 arg3 arg4 arg5)))
                                (bv-array-write
                                   (mv t
                                       (bv-array-write-unguarded (nfix arg1)
                                                                 (nfix arg2)
                                                                 (nfix arg3)
                                                                 arg4 arg5)))
                                (bv-array-clear-range
                                     (mv t
                                         (bv-array-clear-range
                                              arg1 arg2 arg3 arg4 arg5)))
                                (t (mv nil nil))))
                              (let
                               ((args-to-walk-down (cdr args-to-walk-down)))
                               (if (endp args-to-walk-down)
                                   (mv nil nil)
                                (let ((args-to-walk-down
                                           (cdr args-to-walk-down)))
                                 (if (endp args-to-walk-down)
                                     (mv nil nil)
                                  (let ((args-to-walk-down
                                             (cdr args-to-walk-down)))
                                   (if
                                    (endp args-to-walk-down)
                                    (let ((arg8 (unquote (nth 7 args)))
                                          (arg7 (unquote (nth 6 args)))
                                          (arg6 (unquote (nth 5 args)))
                                          (arg5 (unquote (nth 4 args)))
                                          (arg4 (unquote (nth 3 args)))
                                          (arg3 (unquote (nth 2 args)))
                                          (arg2 (unquote (nth 1 args)))
                                          (arg1 (unquote (nth 0 args))))
                                     (declare (ignore arg8))
                                     (case fn
                                      (eval-dag-with-axe-evaluator
                                       (mv
                                        t
                                        (eval-dag-with-axe-evaluator
                                           arg1 arg2 arg3
                                           arg4 arg5 arg6 arg7 array-depth)))
                                      (t (mv nil nil))))
                                    (mv nil nil))))))))))))))))))
                   (IF
                    HIT VAL
                    (LET
                     ((MATCH (ASSOC-EQ FN INTERPRETED-FUNCTION-ALIST)))
                     (IF
                      (NOT MATCH)
                      (ER
                       HARD?
                       'APPLY-AXE-EVALUATOR-TO-QUOTED-ARGS
                       "Unknown function: ~x0 applied to args ~x1 (pass it as an interpreted function, or add to the list of built-ins, or check the arity of the call)."
                       FN ARGS)
                      (LET*
                        ((FN-INFO (CDR MATCH))
                         (FORMALS (FIRST FN-INFO))
                         (BODY (SECOND FN-INFO))
                         (ALIST
                              (PAIRLIS$-FAST FORMALS (UNQUOTE-LIST ARGS))))
                        (EVAL-AXE-EVALUATOR
                             ALIST BODY INTERPRETED-FUNCTION-ALIST
                             ARRAY-DEPTH))))))))))
