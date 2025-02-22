; Tests of make-axe-syntaxp-evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-axe-syntaxp-evaluator")
(include-book "std/testing/must-be-redundant" :dir :system)

(make-axe-syntaxp-evaluator 'foo '())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-axe-syntaxp-evaluator 'bar '(syntactic-variablep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-axe-syntaxp-evaluator 'baz '(syntactic-variablep
                                   lighter-dargp
                                   should-reverse-equality ;this one uses the dag-array
                                   ))

;; expected result:
(must-be-redundant

 (DEFUN EVAL-AXE-SYNTAXP-EXPR-BAZ (EXPR ALIST DAG-ARRAY)
   (DECLARE (XARGS
             :GUARD
             (AND (PSEUDO-TERMP EXPR)
                  (AXE-SYNTAXP-EXPRP EXPR)
                  (SYMBOL-ALISTP ALIST)
                  (DARG-LISTP (STRIP-CDRS ALIST))
                  (SUBSETP-EQ (FREE-VARS-IN-TERM EXPR)
                              (STRIP-CARS ALIST))
                  (PSEUDO-DAG-ARRAYP 'DAG-ARRAY DAG-ARRAY (+ 1 (LARGEST-NON-QUOTEP (STRIP-CDRS ALIST)))))
             :GUARD-HINTS
             (("Goal"
               :IN-THEORY (ENABLE FREE-VARS-IN-TERM AXE-SYNTAXP-EXPRP
                                  AXE-SYNTAXP-FUNCTION-APPLICATIONP)
               :EXPAND (AXE-SYNTAXP-EXPRP EXPR)
               :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)))))
   (LET
    ((FN (FFN-SYMB EXPR)))
    (CASE
      FN
      '(UNQUOTE EXPR) ; this case for QUOTE prints weirdly
      (IF (IF (EVAL-AXE-SYNTAXP-EXPR-BAZ (FARG1 EXPR)
                                         ALIST DAG-ARRAY)
              (EVAL-AXE-SYNTAXP-EXPR-BAZ (FARG2 EXPR)
                                         ALIST DAG-ARRAY)
              (EVAL-AXE-SYNTAXP-EXPR-BAZ (FARG3 EXPR)
                                         ALIST DAG-ARRAY)))
      (NOT (NOT (EVAL-AXE-SYNTAXP-EXPR-BAZ (FARG1 EXPR)
                                           ALIST DAG-ARRAY)))
      (T (EVAL-AXE-SYNTAXP-FUNCTION-APPLICATION-BAZ
          FN (FARGS EXPR)
          ALIST DAG-ARRAY)))))

 (DEFUN EVAL-AXE-SYNTAXP-FUNCTION-APPLICATION-BAZ (FN ARGS ALIST DAG-ARRAY)
   (DECLARE (XARGS :GUARD
                   (AND (SYMBOLP FN)
                        (LIST-OF-VARIABLES-AND-CONSTANTSP ARGS)
                        (SYMBOL-ALISTP ALIST)
                        (DARG-LISTP (STRIP-CDRS ALIST))
                        (SUBSETP-EQ (FREE-VARS-IN-TERMS ARGS)
                                    (STRIP-CARS ALIST))
                        (IMPLIES (EQ FN 'AXE-QUOTEP)
                                 (VARIABLEP (FIRST ARGS)))
                        (PSEUDO-DAG-ARRAYP
                          'DAG-ARRAY
                          DAG-ARRAY
                          (+ 1
                             (LARGEST-NON-QUOTEP (STRIP-CDRS ALIST)))))
                   :GUARD-HINTS
                   (("Goal"
                     :IN-THEORY
                     (E/D
                       (LIST-OF-VARIABLES-AND-CONSTANTSP FREE-VARS-IN-TERMS-OPENER)
                       (DARGP))
                     :EXPAND ((FREE-VARS-IN-TERMS ARGS)
                              (FREE-VARS-IN-TERM (CAR ARGS))))))
            (IGNORABLE DAG-ARRAY))
   (IF
       (ATOM ARGS)
       (ER HARD?
           'EVAL-AXE-SYNTAXP-FUNCTION-APPLICATION-BAZ
           "Unrecognized function in axe-syntaxp rule: ~x0."
           FN)
     (if (eq fn 'axe-quotep)
         (axe-quotep (lookup-eq (first args) alist)) ; special case
       (LET* ((ARG0 (FIRST ARGS))
              (arg0-val (if (consp arg0)
                            arg0
                          (lookup-eq arg0 alist)))
              (ARGS (REST ARGS)))
         (declare (ignorable args arg0 arg0-val))

         (IF
             (ATOM ARGS)
             ;; these are the unary functions (not counting the dag-array argument):
             (CASE FN
               (SYNTACTIC-VARIABLEP (SYNTACTIC-VARIABLEP arg0-val dag-array))
               (t (ER HARD?
                      'EVAL-AXE-SYNTAXP-FUNCTION-APPLICATION-BAZ
                      "Unrecognized function in axe-syntaxp rule: ~x0."
                      FN)))
           (LET* ((ARG1 (FIRST ARGS))
                  (arg1-val (if (consp arg1)
                                arg1
                              (lookup-eq arg1 alist)))
                  (ARGS (REST ARGS)))
             (DECLARE (IGNORABLE ARGS ARG1 arg1-val))
             (IF
                 (ATOM ARGS)
                 ;; these are the binary functions (not counting the dag-array argument):
                 (CASE
                   FN
                   (SHOULD-REVERSE-EQUALITY
                     ;; For this, only 2 args are given in the call (dag-array has been
                     ;; removed), but we know that it takes dag-array as the final param,
                     ;; so we pass it separately:
                     (SHOULD-REVERSE-EQUALITY
                       arg0-val arg1-val
                       ;; this one takes the dag-array too, which we pass around separately:
                       DAG-ARRAY))
                   (LIGHTER-DARGP
                     ;; this one does not take a dag-array param:
                     (LIGHTER-DARGP arg0-val arg1-val))
                   (T
                     (ER HARD?
                         'EVAL-AXE-SYNTAXP-FUNCTION-APPLICATION-BAZ
                         "Unrecognized function in axe-syntaxp rule: ~x0."
                         FN)))
               (ER HARD?
                   'EVAL-AXE-SYNTAXP-FUNCTION-APPLICATION-BAZ
                   "Unrecognized function in axe-syntaxp rule: ~x0."
                   FN))))))))
 )
