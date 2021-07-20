; Tests of the evaluator
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
         (LET
          ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
          (IF
           (ENDP ARGS-TO-WALK-DOWN)
           (LET
            ((ARG1 (NTH 0 ARGS)))
            (IF
             (EQ 'COMPLEX-RATIONALP FN)
             (MV T (COMPLEX-RATIONALP ARG1))
             (IF
              (EQ 'CHARACTERP FN)
              (MV T (CHARACTERP ARG1))
              (IF
               (EQ 'SYMBOLP FN)
               (MV T (SYMBOLP ARG1))
               (IF
                (EQ 'IMAGPART FN)
                (MV T (IMAGPART-UNGUARDED ARG1))
                (IF
                 (EQ 'REALPART FN)
                 (MV T (REALPART-UNGUARDED ARG1))
                 (IF
                  (EQ 'MAP-REVERSE-LIST FN)
                  (MV T (MAP-REVERSE-LIST ARG1))
                  (IF
                   (EQ 'CDR FN)
                   (MV T (CDR-UNGUARDED ARG1))
                   (IF
                    (EQ 'CAR FN)
                    (MV T (CAR-UNGUARDED ARG1))
                    (IF
                     (EQ 'ATOM FN)
                     (MV T (ATOM ARG1))
                     (IF
                      (EQ 'UNARY-- FN)
                      (MV T (UNARY---UNGUARDED ARG1))
                      (IF
                       (EQ 'ZP FN)
                       (MV T (ZP-UNGUARDED ARG1))
                       (IF
                        (EQ 'ACL2-NUMBERP FN)
                        (MV T (ACL2-NUMBERP ARG1))
                        (IF
                         (EQ 'REVERSE-LIST FN)
                         (MV T (REVERSE-LIST-UNGUARDED ARG1))
                         (IF
                          (EQ 'LEN FN)
                          (MV T (LEN ARG1))
                          (IF
                           (EQ 'IFIX FN)
                           (MV T (IFIX ARG1))
                           (IF
                            (EQ 'NFIX FN)
                            (MV T (NFIX ARG1))
                            (IF
                             (EQ 'UNARY-/ FN)
                             (MV T (UNARY-/-UNGUARDED ARG1))
                             (IF
                              (EQ 'CEILING-OF-LG FN)
                              (MV T (CEILING-OF-LG ARG1))
                              (IF
                               (EQ 'INTEGER-LENGTH FN)
                               (MV
                                T
                                (INTEGER-LENGTH-UNGUARDED ARG1))
                               (IF
                                (EQ 'LOGMASKP FN)
                                (MV T (LOGMASKP ARG1))
                                (IF
                                 (EQ 'BITNOT FN)
                                 (MV T (BITNOT-UNGUARDED ARG1))
                                 (IF
                                  (EQ 'ENDP FN)
                                  (MV T (ENDP-UNGUARDED ARG1))
                                  (IF
                                   (EQ 'ALL-NATP FN)
                                   (MV T (ALL-NATP ARG1))
                                   (IF
                                    (EQ 'WIDTH-OF-WIDEST-INT FN)
                                    (MV
                                     T
                                     (WIDTH-OF-WIDEST-INT ARG1))
                                    (IF
                                     (EQ 'BYTES-TO-BITS FN)
                                     (MV T (BYTES-TO-BITS ARG1))
                                     (IF
                                      (EQ 'CONSP FN)
                                      (MV T (CONSP ARG1))
                                      (IF
                                       (EQ 'TRUE-LISTP FN)
                                       (MV T (TRUE-LISTP ARG1))
                                       (IF
                                        (EQ 'STRINGP FN)
                                        (MV T (STRINGP ARG1))
                                        (IF
                                         (EQ 'STRIP-CARS FN)
                                         (MV T
                                             (STRIP-CARS-UNGUARDED
                                              ARG1))
                                         (IF
                                          (EQ 'STRIP-CDRS FN)
                                          (MV T
                                              (STRIP-CDRS-UNGUARDED
                                               ARG1))
                                          (IF
                                           (EQ 'NO-DUPLICATESP-EQUAL FN)
                                           (MV
                                            T (NO-DUPLICATESP-EQUAL ARG1))
                                           (IF
                                            (EQ 'ALL-INTEGERP FN)
                                            (MV
                                             T
                                             (ALL-INTEGERP ARG1))
                                            (IF
                                             (EQ 'TRUE-LIST-FIX
                                                 FN)
                                             (MV T
                                                 (TRUE-LIST-FIX
                                                  ARG1))
                                             (IF
                                              (EQ 'KEY-LIST FN)
                                              (MV
                                               T (KEY-LIST ARG1))
                                              (IF
                                               (EQ 'RKEYS FN)
                                               (MV
                                                T (RKEYS ARG1))
                                               (IF
                                                (EQ 'LIST::2SET
                                                    FN)
                                                (MV T
                                                    (LIST::2SET
                                                     ARG1))
                                                (IF
                                                 (EQ 'BOOLEANP
                                                     FN)
                                                 (MV T
                                                     (BOOLEANP
                                                      ARG1))
                                                 (IF
                                                  (EQ
                                                   'BOOL-FIX$INLINE
                                                   FN)
                                                  (MV T
                                                      (BOOL-FIX$INLINE
                                                       ARG1))
                                                  (IF
                                                   (EQ 'ALL-SAME
                                                       FN)
                                                   (MV
                                                    T
                                                    (ALL-SAME
                                                     ARG1))
                                                   (IF
                                                    (EQ
                                                     'SYMBOL-NAME
                                                     FN)
                                                    (MV
                                                     T
                                                     (SYMBOL-NAME-UNGUARDED
                                                      ARG1))
                                                    (IF
                                                     (EQ
                                                      'SYMBOL-PACKAGE-NAME
                                                      FN)
                                                     (MV
                                                      T
                                                      (SYMBOL-PACKAGE-NAME-UNGUARDED
                                                       ARG1))
                                                     (IF
                                                      (EQ
                                                       'CODE-CHAR
                                                       FN)
                                                      (MV
                                                       T
                                                       (CODE-CHAR-UNGUARDED
                                                        ARG1))
                                                      (IF
                                                       (EQ
                                                        'CHAR-CODE
                                                        FN)
                                                       (MV
                                                        T
                                                        (CHAR-CODE-UNGUARDED
                                                         ARG1))
                                                       (IF
                                                        (EQ
                                                         'BOOL-TO-BIT
                                                         FN)
                                                        (MV
                                                         T
                                                         (BOOL-TO-BIT
                                                          ARG1))
                                                        (IF
                                                         (EQ 'LG
                                                             FN)
                                                         (MV
                                                          T
                                                          (LG-UNGUARDED
                                                           ARG1))
                                                         (IF
                                                          (EQ
                                                           'POWER-OF-2P
                                                           FN)
                                                          (MV
                                                           T
                                                           (POWER-OF-2P
                                                            ARG1))
                                                          (IF
                                                           (EQ
                                                            'NOT
                                                            FN)
                                                           (MV
                                                            T
                                                            (NOT
                                                             ARG1))
                                                           (IF
                                                            (EQ
                                                             'PRINT-CONSTANT
                                                             FN)
                                                            (MV
                                                             T
                                                             (PRINT-CONSTANT
                                                              ARG1))
                                                            (IF
                                                             (EQ
                                                              'RATIONALP
                                                              FN)
                                                             (MV
                                                              T
                                                              (RATIONALP
                                                               ARG1))
                                                             (IF
                                                              (EQ
                                                               'INTEGERP
                                                               FN)
                                                              (MV
                                                               T
                                                               (INTEGERP
                                                                ARG1))
                                                              (IF
                                                               (EQ
                                                                'POSP
                                                                FN)
                                                               (MV
                                                                T
                                                                (POSP
                                                                 ARG1))
                                                               (IF
                                                                (EQ
                                                                 'NATP
                                                                 FN)
                                                                (MV
                                                                 T
                                                                 (NATP
                                                                  ARG1))
                                                                (IF
                                                                 (EQ
                                                                  'QUOTEP
                                                                  FN)
                                                                 (MV
                                                                  T
                                                                  (QUOTEP ARG1))
                                                                 (MV
                                                                  NIL
                                                                  NIL)))))))))))))))))))))))))))))))))))))))))))))))))))))))
           (LET
            ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
            (IF
             (ENDP ARGS-TO-WALK-DOWN)
             (LET
              ((ARG2 (NTH 1 ARGS))
               (ARG1 (NTH 0 ARGS)))
              (IF
               (EQ 'SYMBOL< FN)
               (MV T (SYMBOL<-UNGUARDED ARG1 ARG2))
              (IF
               (EQ 'SET::IN FN)
               (MV T (SET::IN-UNGUARDED ARG1 ARG2))
               (IF
                (EQ 'GROUP2 FN)
                (MV T (GROUP2 ARG1 ARG2))
                (IF
                 (EQ 'GROUP FN)
                 (MV T (GROUP ARG1 ARG2))
                 (IF
                  (EQ 'LOOKUP FN)
                  (MV T (LOOKUP ARG1 ARG2))
                  (IF
                   (EQ 'LOOKUP-EQ FN)
                   (MV T (LOOKUP-EQ ARG1 ARG2))
                   (IF
                    (EQ 'CEILING FN)
                    (MV T (CEILING-UNGUARDED ARG1 ARG2))
                    (IF
                     (EQ 'EQ FN)
                     (MV T (EQUAL ARG1 ARG2))
                     (IF
                      (EQ 'BVNOT-LIST FN)
                      (MV T (BVNOT-LIST-UNGUARDED ARG1 ARG2))
                      (IF
                       (EQ 'BINARY-* FN)
                       (MV T (BINARY-*-UNGUARDED ARG1 ARG2))
                       (IF
                        (EQ 'NTH FN)
                        (MV T (NTH-UNGUARDED ARG1 ARG2))
                        (IF
                         (EQ 'LOGEXT FN)
                         (MV T (LOGEXT ARG1 (IFIX ARG2)))
                         (IF
                          (EQ 'LOGTAIL$INLINE FN)
                          (MV T (LOGTAIL-UNGUARDED ARG1 ARG2))
                          (IF
                           (EQ 'BVCHOP FN)
                           (MV T (BVCHOP-UNGUARDED ARG1 ARG2))
                           (IF
                            (EQ 'CONS FN)
                            (MV T (CONS ARG1 ARG2))
                            (IF
                             (EQ 'GETBIT FN)
                             (MV T (GETBIT-UNGUARDED ARG1 ARG2))
                             (IF
                              (EQ 'MOD FN)
                              (MV T (MOD ARG1 ARG2))
                              (IF
                               (EQ 'MAX FN)
                               (MV T (MAX-UNGUARDED ARG1 ARG2))
                               (IF
                                (EQ 'MIN FN)
                                (MV T (MIN-UNGUARDED ARG1 ARG2))
                                (IF
                                 (EQ 'EXPT FN)
                                 (MV
                                  T (EXPT-UNGUARDED ARG1 ARG2))
                                 (IF
                                  (EQ 'BITXOR FN)
                                  (MV
                                   T
                                   (BITXOR-UNGUARDED ARG1 ARG2))
                                  (IF
                                   (EQ 'BITAND FN)
                                   (MV
                                    T
                                    (BITAND-UNGUARDED ARG1 ARG2))
                                   (IF
                                    (EQ 'BITOR FN)
                                    (MV
                                     T
                                     (BITOR-UNGUARDED ARG1 ARG2))
                                    (IF
                                     (EQ 'ALL-SIGNED-BYTE-P FN)
                                     (MV T
                                         (ALL-SIGNED-BYTE-P
                                          ARG1 ARG2))
                                     (IF
                                      (EQ 'ALL-UNSIGNED-BYTE-P
                                          FN)
                                      (MV T
                                          (ALL-UNSIGNED-BYTE-P
                                           ARG1 ARG2))
                                      (IF
                                       (EQ 'BVCHOP-LIST FN)
                                       (MV T
                                           (BVCHOP-LIST-UNGUARDED
                                            ARG1 ARG2))
                                       (IF
                                        (EQ 'UNSIGNED-BYTE-P FN)
                                        (MV T
                                            (UNSIGNED-BYTE-P
                                             ARG1 ARG2))
                                        (IF
                                         (EQ 'SIGNED-BYTE-P FN)
                                         (MV T
                                             (SIGNED-BYTE-P
                                              ARG1 ARG2))
                                         (IF
                                          (EQ 'GETBIT-IS-ALWAYS-1
                                              FN)
                                          (MV T
                                              (GETBIT-IS-ALWAYS-1-UNGUARDED
                                               ARG1 ARG2))
                                          (IF
                                           (EQ
                                            'GETBIT-IS-ALWAYS-0
                                            FN)
                                           (MV T
                                               (GETBIT-IS-ALWAYS-0-UNGUARDED
                                                ARG1 ARG2))
                                           (IF
                                            (EQ 'BINARY-APPEND
                                                FN)
                                            (MV T
                                                (BINARY-APPEND-UNGUARDED
                                                 ARG1 ARG2))
                                            (IF
                                             (EQ 'FIRSTN FN)
                                             (MV T
                                                 (FIRSTN-UNGUARDED
                                                  ARG1 ARG2))
                                             (IF
                                              (EQ 'TAKE FN)
                                              (MV
                                               T
                                               (TAKE-UNGUARDED
                                                ARG1 ARG2))
                                              (IF
                                               (EQ 'NTHCDR FN)
                                               (MV
                                                T
                                                (NTHCDR-UNGUARDED
                                                 ARG1 ARG2))
                                               (IF
                                                (EQ 'G FN)
                                                (MV
                                                 T (G ARG1 ARG2))
                                                (IF
                                                 (EQ
                                                  'MEMBER-EQUAL
                                                  FN)
                                                 (MV
                                                  T
                                                  (MEMBER-EQUAL
                                                   ARG1 ARG2))
                                                 (IF
                                                  (EQ 'FLOOR FN)
                                                  (MV
                                                   T
                                                   (FLOOR
                                                    ARG1 ARG2))
                                                  (IF
                                                   (EQ
                                                    'SET::INSERT
                                                    FN)
                                                   (MV
                                                    T
                                                    (SET::INSERT
                                                     ARG1 ARG2))
                                                   (IF
                                                    (EQ
                                                     'LEFTROTATE32
                                                     FN)
                                                    (MV
                                                     T
                                                     (LEFTROTATE32-UNGUARDED
                                                      ARG1 ARG2))
                                                    (IF
                                                     (EQ
                                                      'SET::UNION
                                                      FN)
                                                     (MV
                                                      T
                                                      (SET::UNION
                                                       ARG1
                                                       ARG2))
                                                     (IF
                                                      (EQ
                                                       'GETBIT-LIST
                                                       FN)
                                                      (MV
                                                       T
                                                       (GETBIT-LIST
                                                        ARG1
                                                        ARG2))
                                                      (IF
                                                       (EQ
                                                        'BOOLOR
                                                        FN)
                                                       (MV
                                                        T
                                                        (BOOLOR
                                                         ARG1
                                                         ARG2))
                                                       (IF
                                                        (EQ
                                                         'BOOLAND
                                                         FN)
                                                        (MV
                                                         T
                                                         (BOOLAND
                                                          ARG1
                                                          ARG2))
                                                        (IF
                                                         (EQ
                                                          'FIRST-NON-MEMBER
                                                          FN)
                                                         (MV
                                                          T
                                                          (FIRST-NON-MEMBER
                                                           ARG1
                                                           ARG2))
                                                         (IF
                                                          (EQ
                                                           'IMPLIES
                                                           FN)
                                                          (MV
                                                           T
                                                           (IMPLIES
                                                            ARG1
                                                            ARG2))
                                                          ;; (IF
                                                          ;;  (EQ
                                                          ;;   'BINARY-AND
                                                          ;;   FN)
                                                          ;;  (MV
                                                          ;;   T
                                                          ;;   (BINARY-AND
                                                          ;;    ARG1
                                                          ;;    ARG2))
                                                           (IF
                                                            (EQ
                                                             'REPEATBIT
                                                             FN)
                                                            (MV
                                                             T
                                                             (REPEATBIT
                                                              ARG1
                                                              ARG2))
                                                            (IF
                                                             (EQ
                                                              'ALL-EQUAL$
                                                              FN)
                                                             (MV
                                                              T
                                                              (ALL-EQUAL$
                                                               ARG1
                                                               ARG2))
                                                             (IF
                                                              (EQ
                                                               'INTERSECTION-EQUAL
                                                               FN)
                                                              (MV
                                                               T
                                                               (INTERSECTION-EQUAL
                                                                ARG1
                                                                ARG2))
                                                              (IF
                                                               (EQ
                                                                'TAKE-EVERY-NTH
                                                                FN)
                                                               (MV
                                                                T
                                                                (TAKE-EVERY-NTH
                                                                 ARG1
                                                                 ARG2))
                                                               (IF
                                                                (EQ
                                                                 'ALL-ITEMS-LESS-THAN
                                                                 FN)
                                                                (MV
                                                                 T
                                                                 (ALL-ITEMS-LESS-THAN
                                                                  ARG1
                                                                  ARG2))
                                                                (IF
                                                                 (EQ
                                                                  'BINARY-+
                                                                  FN)
                                                                 (MV
                                                                  T
                                                                  (BINARY-+-UNGUARDED

                                                                   ARG1

                                                                   ARG2))
                                                                 (IF
                                                                  (EQ

                                                                   'TRIM

                                                                   FN)
                                                                  (MV

                                                                   T

                                                                   (TRIM-UNGUARDED

                                                                    ARG1

                                                                    ARG2))
                                                                  (IF

                                                                   (EQ

                                                                    'UNSIGNED-BYTE-P-FORCED

                                                                    FN)

                                                                   (MV

                                                                    T

                                                                    (UNSIGNED-BYTE-P-FORCED

                                                                     ARG1

                                                                     ARG2))

                                                                   (IF

                                                                    (EQ

                                                                     'ASSOC-EQUAL

                                                                     FN)

                                                                    (MV

                                                                     T

                                                                     (ASSOC-EQUAL-UNGUARDED

                                                                      ARG1

                                                                      ARG2))

                                                                    (IF

                                                                     (EQ

                                                                      'BVUMINUS

                                                                      FN)

                                                                     (MV

                                                                      T

                                                                      (BVUMINUS-UNGUARDED

                                                                       ARG1

                                                                       ARG2))

                                                                     (IF

                                                                      (EQ

                                                                       'BVNOT

                                                                       FN)

                                                                      (MV

                                                                       T

                                                                       (BVNOT-UNGUARDED

                                                                        ARG1

                                                                        ARG2))

                                                                      (IF

                                                                       (EQ

                                                                        'LOOKUP

                                                                        FN)

                                                                       (MV

                                                                        T

                                                                        (LOOKUP

                                                                         ARG1

                                                                         ARG2))

                                                                       (IF

                                                                        (EQ

                                                                         'LOOKUP-EQUAL

                                                                         FN)

                                                                        (MV

                                                                         T

                                                                         (LOOKUP-EQUAL

                                                                          ARG1

                                                                          ARG2))

                                                                        (IF

                                                                         (EQ

                                                                          'PREFIXP

                                                                          FN)

                                                                         (MV

                                                                          T

                                                                          (PREFIXP

                                                                           ARG1

                                                                           ARG2))

                                                                         (IF

                                                                          (EQ

                                                                           'LIST-EQUIV

                                                                           FN)

                                                                          (MV

                                                                           T

                                                                           (LIST-EQUIV

                                                                            ARG1

                                                                            ARG2))

                                                                          (IF

                                                                           (EQ

                                                                            'EQL

                                                                            FN)

                                                                           (MV

                                                                            T

                                                                            (EQUAL

                                                                             ARG1

                                                                             ARG2))

                                                                           (IF

                                                                            (EQ

                                                                             'EQUAL

                                                                             FN)

                                                                            (MV

                                                                             T

                                                                             (EQUAL

                                                                              ARG1

                                                                              ARG2))

                                                                            (IF

                                                                             (EQ

                                                                              '<

                                                                              FN)

                                                                             (MV

                                                                              T

                                                                              (<-UNGUARDED

                                                                               ARG1

                                                                               ARG2))

                                                                             (IF

                                                                              (EQ

                                                                               'COERCE

                                                                               FN)

                                                                              (MV

                                                                               T

                                                                               (COERCE-UNGUARDED

                                                                                ARG1

                                                                                ARG2))

                                                                              (IF

                                                                               (EQ

                                                                                'ADD-TO-END

                                                                                FN)

                                                                               (MV

                                                                                T

                                                                                (ADD-TO-END

                                                                                 ARG1

                                                                                 ARG2))

                                                                               (IF

                                                                                (EQ

                                                                                 'ALL-ALL-UNSIGNED-BYTE-P

                                                                                 FN)

                                                                                (MV

                                                                                 T

                                                                                 (ALL-ALL-UNSIGNED-BYTE-P

                                                                                  ARG1

                                                                                  ARG2))

                                                                                (IF

                                                                                 (EQ

                                                                                  'ITEMS-HAVE-LEN

                                                                                  FN)

                                                                                 (MV

                                                                                  T

                                                                                  (ITEMS-HAVE-LEN-UNGUARDED

                                                                                   ARG1

                                                                                   ARG2))
                                                                                 (IF (EQ 'MV-NTH FN)
                                                                                     (MV T (MV-NTH-UNGUARDED ARG1 ARG2))
                                                                                 (MV

                                                                                  NIL

                                                                                  NIL))))))))))))))))))))))))
                                                           ;;)
                                                           ))))))))))))))))))))))))))))))))))))))))))))))
             (LET
              ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
              (IF
               (ENDP ARGS-TO-WALK-DOWN)
               (LET
                ((ARG3 (NTH 2 ARGS))
                 (ARG2 (NTH 1 ARGS))
                 (ARG1 (NTH 0 ARGS)))
                (IF
                 (EQ 'BVXOR-LIST FN)
                 (MV T (BVXOR-LIST-UNGUARDED ARG1 ARG2 ARG3))
                 (IF
                  (EQ 'SUBRANGE FN)
                  (MV T
                      (SUBRANGE (NFIX ARG1) (NFIX ARG2) ARG3))
                  (IF
                   (EQ 'KEEP-ITEMS-LESS-THAN FN)
                   (MV T
                       (KEEP-ITEMS-LESS-THAN-UNGUARDED
                        ARG1 ARG2 ARG3))
                   (IF
                    (EQ 'BVSHL FN)
                    (MV T (BVSHL ARG1 ARG2 ARG3))
                    (IF
                     (EQ 'SLICE FN)
                     (MV T (SLICE-LESS-GUARDED ARG1 ARG2 ARG3))
                     (IF
                      (EQ 'IF FN)
                      (MV T (IF ARG1 ARG2 ARG3))
                      (IF
                       (EQ 'UPDATE-NTH FN)
                       (MV T (UPDATE-NTH ARG1 ARG2 ARG3))
                       (IF
                        (EQ 'ARRAY-ELEM-2D FN)
                        (MV T (ARRAY-ELEM-2D ARG1 ARG2 ARG3))
                        (IF
                         (EQ 'BOOLIF FN)
                         (MV T (BOOLIF ARG1 ARG2 ARG3))
                         (IF
                          (EQ 'MYIF FN)
                          (MV T (MYIF ARG1 ARG2 ARG3))
                          (IF
                           (EQ 'NTH2 FN)
                           (MV T (NTH2 ARG1 ARG2 ARG3))
                           (IF
                            (EQ 'S FN)
                            (MV T (S ARG1 ARG2 ARG3))
                            (IF
                             (EQ 'SBVLE FN)
                             (MV T (SBVLE ARG1 ARG2 ARG3))
                             (IF
                              (EQ 'SBVLT FN)
                              (MV T
                                  (SBVLT ARG1 (IFIX ARG2)
                                         (IFIX ARG3)))
                              (IF
                               (EQ 'SBVMODDOWN FN)
                               (MV T (SBVMODDOWN ARG1 ARG2 ARG3))
                               (IF
                                (EQ 'SBVREM FN)
                                (MV T (SBVREM ARG1 ARG2 ARG3))
                                (IF
                                 (EQ 'SBVDIVDOWN FN)
                                 (MV
                                  T (SBVDIVDOWN ARG1 ARG2 ARG3))
                                 (IF
                                  (EQ 'SBVDIV FN)
                                  (MV T (SBVDIV ARG1 ARG2 ARG3))
                                  (IF
                                   (EQ 'BVSX FN)
                                   (MV T (BVSX ARG1 ARG2 ARG3))
                                   (IF
                                    (EQ 'BVDIV FN)
                                    (MV T
                                        (BVDIV-UNGUARDED
                                         ARG1 ARG2 ARG3))
                                    (IF
                                     (EQ 'BVMOD FN)
                                     (MV T
                                         (BVMOD-UNGUARDED
                                          ARG1 ARG2 ARG3))
                                     (IF
                                      (EQ 'BVMINUS FN)
                                      (MV T
                                          (BVMINUS-UNGUARDED
                                           ARG1 ARG2 ARG3))
                                      (IF
                                       (EQ 'BVPLUS FN)
                                       (MV T
                                           (BVPLUS-UNGUARDED
                                            ARG1 ARG2 ARG3))
                                       (IF
                                        (EQ 'BVMULT FN)
                                        (MV T
                                            (BVMULT-UNGUARDED
                                             ARG1 ARG2 ARG3))
                                        (IF
                                         (EQ 'BVAND FN)
                                         (MV
                                          T
                                          (BVAND-UNGUARDED
                                           ARG1 ARG2 ARG3))
                                         (IF
                                          (EQ 'BVOR FN)
                                          (MV
                                           T
                                           (BVOR-UNGUARDED
                                            ARG1 ARG2 ARG3))
                                          (IF
                                           (EQ 'BVXOR FN)
                                           (MV
                                            T
                                            (BVXOR-UNGUARDED
                                             ARG1 ARG2 ARG3))
                                           (IF
                                            (EQ 'BVLE FN)
                                            (MV
                                             T
                                             (BVLE-UNGUARDED
                                              ARG1 ARG2 ARG3))
                                            (IF
                                             (EQ 'BVLT FN)
                                             (MV
                                              T
                                              (BVLT-UNGUARDED
                                               ARG1 ARG2 ARG3))
                                             (IF
                                              (EQ 'BVPLUS-LST FN)
                                              (MV
                                               T
                                               (BVPLUS-LST
                                                ARG1 ARG2 ARG3))
                                              (IF
                                               (EQ 'UNPACKBV FN)
                                               (MV
                                                T
                                                (UNPACKBV-LESS-GUARDED
                                                 ARG1 ARG2 ARG3))
                                               (IF
                                                (EQ 'PACKBV FN)
                                                (MV
                                                 T
                                                 (PACKBV
                                                  ARG1
                                                  ARG2 ARG3))
                                                (IF
                                                 (EQ
                                                  'BVASHR
                                                  FN)
                                                 (MV
                                                  T
                                                  (BVASHR
                                                   ARG1
                                                   ARG2 ARG3))
                                                 (IF
                                                  (EQ 'BVSHR FN)
                                                  (MV
                                                   T
                                                   (BVSHR
                                                    ARG1
                                                    ARG2 ARG3))
                                                  (IF
                                                   (EQ 'ACONS FN)
                                                   (MV
                                                    T
                                                    (ACONS
                                                     ARG1
                                                     ARG2 ARG3))
                                                   (IF
                                                    (EQ
                                                     'LEFTROTATE
                                                     FN)
                                                    (MV
                                                     T
                                                     (LEFTROTATE
                                                      ARG1
                                                      ARG2 ARG3))
                                                    (IF
                                                     (EQ
                                                      'NEGATED-ELEMS-LISTP
                                                      FN)
                                                     (MV
                                                      T
                                                      (NEGATED-ELEMS-LISTP-UNGUARDED
                                                       ARG1 ARG2
                                                       ARG3))
                                                     (IF
                                                      (EQ
                                                       'REPEAT-TAIL
                                                       FN)
                                                      (MV
                                                       T
                                                       (REPEAT-TAIL
                                                        ARG1 ARG2
                                                        ARG3))
                                                      (MV
                                                       NIL
                                                       NIL))))))))))))))))))))))))))))))))))))))))
               (LET
                ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                (IF
                 (ENDP ARGS-TO-WALK-DOWN)
                 (LET
                  ((ARG4 (NTH 3 ARGS))
                   (ARG3 (NTH 2 ARGS))
                   (ARG2 (NTH 1 ARGS))
                   (ARG1 (NTH 0 ARGS)))
                  (IF
                   (EQ 'BVIF FN)
                   (MV T (BVIF-UNGUARDED ARG1 ARG2 ARG3 ARG4))
                   (IF
                    (EQ 'BV-ARRAY-READ FN)
                    (MV T
                        (BV-ARRAY-READ-UNGUARDED
                         ARG1 ARG2 ARG3 ARG4))
                    (IF
                     (EQ 'BVNTH FN)
                     (MV T (BVNTH ARG1 ARG2 (NFIX ARG3) ARG4))
                     (IF
                      (EQ 'BVCAT FN)
                      (MV
                       T (BVCAT-UNGUARDED ARG1 ARG2 ARG3 ARG4))
                      (IF
                       (EQ 'BV-ARRAY-CLEAR FN)
                       (MV
                        T (BV-ARRAY-CLEAR ARG1 ARG2 ARG3 ARG4))
                       (IF
                        (EQ 'UPDATE-NTH2 FN)
                        (MV T (UPDATE-NTH2 ARG1 ARG2 ARG3 ARG4))
                        (IF
                         (EQ 'UPDATE-SUBRANGE FN)
                         (MV
                          T
                          (UPDATE-SUBRANGE ARG1 ARG2 ARG3 ARG4))
                         (IF
                          (EQ 'APPLY-AXE-EVALUATOR FN)
                          (MV T
                              (APPLY-AXE-EVALUATOR
                               ARG1 ARG2 ARG3 ARRAY-DEPTH))
                          (IF
                           (EQ 'DAG-VAL-WITH-AXE-EVALUATOR FN)
                           (MV
                            T
                            (DAG-VAL-WITH-AXE-EVALUATOR
                             ARG1 ARG2 ARG3 (+ 1 ARRAY-DEPTH)))
                           (MV NIL NIL)))))))))))
                 (LET
                  ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                  (IF
                   (ENDP ARGS-TO-WALK-DOWN)
                   (LET
                    ((ARG5 (NTH 4 ARGS))
                     (ARG4 (NTH 3 ARGS))
                     (ARG3 (NTH 2 ARGS))
                     (ARG2 (NTH 1 ARGS))
                     (ARG1 (NTH 0 ARGS)))
                    (IF
                     (EQ 'BV-ARRAY-CLEAR-RANGE FN)
                     (MV T
                         (BV-ARRAY-CLEAR-RANGE
                          ARG1 ARG2 ARG3 ARG4 ARG5))
                     (IF (EQ 'BV-ARRAY-WRITE FN)
                         (MV T
                             (BV-ARRAY-WRITE-UNGUARDED (NFIX ARG1)
                                             (NFIX ARG2)
                                             (NFIX ARG3)
                                             ARG4 ARG5))
                         (IF (EQ 'UPDATE-SUBRANGE2 FN)
                             (MV T
                                 (UPDATE-SUBRANGE2
                                  ARG1 ARG2 ARG3 ARG4 ARG5))
                             (MV NIL NIL)))))
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
                          (DECLARE (IGNORE ARG8)) ;since we use array-depth instead
                          (IF
                           (EQ 'EVAL-DAG-WITH-AXE-EVALUATOR FN)
                           (MV
                            T
                            (EVAL-DAG-WITH-AXE-EVALUATOR
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
                (< (LEN DAG) 2147483646)))
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
               (EVAL-DAG-WITH-AXE-EVALUATOR
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
              ARGS EVAL-ARRAY-NAME
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
                  ARGS EVAL-ARRAY-NAME EVAL-ARRAY))
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
         (IF
          (ENDP ARGS-TO-WALK-DOWN)
          (LET
           ((ARG1 (UNQUOTE (NTH 0 ARGS))))
           (IF
            (EQ 'COMPLEX-RATIONALP FN)
            (MV T (COMPLEX-RATIONALP ARG1))
            (IF
             (EQ 'CHARACTERP FN)
             (MV T (CHARACTERP ARG1))
             (IF
              (EQ 'SYMBOLP FN)
              (MV T (SYMBOLP ARG1))
              (IF
               (EQ 'IMAGPART FN)
               (MV T (IMAGPART-UNGUARDED ARG1))
               (IF
                (EQ 'REALPART FN)
                (MV T (REALPART-UNGUARDED ARG1))
                (IF
                 (EQ 'MAP-REVERSE-LIST FN)
                 (MV T (MAP-REVERSE-LIST ARG1))
                 (IF
                  (EQ 'CDR FN)
                  (MV T (CDR-UNGUARDED ARG1))
                  (IF
                   (EQ 'CAR FN)
                   (MV T (CAR-UNGUARDED ARG1))
                   (IF
                    (EQ 'ATOM FN)
                    (MV T (ATOM ARG1))
                    (IF
                     (EQ 'UNARY-- FN)
                     (MV T (UNARY---UNGUARDED ARG1))
                     (IF
                      (EQ 'ZP FN)
                      (MV T (ZP-UNGUARDED ARG1))
                      (IF
                       (EQ 'ACL2-NUMBERP FN)
                       (MV T (ACL2-NUMBERP ARG1))
                       (IF
                        (EQ 'REVERSE-LIST FN)
                        (MV T (REVERSE-LIST-UNGUARDED ARG1))
                        (IF
                         (EQ 'LEN FN)
                         (MV T (LEN ARG1))
                         (IF
                          (EQ 'IFIX FN)
                          (MV T (IFIX ARG1))
                          (IF
                           (EQ 'NFIX FN)
                           (MV T (NFIX ARG1))
                           (IF
                            (EQ 'UNARY-/ FN)
                            (MV T (UNARY-/-UNGUARDED ARG1))
                            (IF
                             (EQ 'CEILING-OF-LG FN)
                             (MV T (CEILING-OF-LG ARG1))
                             (IF
                              (EQ 'INTEGER-LENGTH FN)
                              (MV
                               T (INTEGER-LENGTH-UNGUARDED ARG1))
                              (IF
                               (EQ 'LOGMASKP FN)
                               (MV T (LOGMASKP ARG1))
                               (IF
                                (EQ 'BITNOT FN)
                                (MV T (BITNOT-UNGUARDED ARG1))
                                (IF
                                 (EQ 'ENDP FN)
                                 (MV T (ENDP-UNGUARDED ARG1))
                                 (IF
                                  (EQ 'ALL-NATP FN)
                                  (MV T (ALL-NATP ARG1))
                                  (IF
                                   (EQ 'WIDTH-OF-WIDEST-INT FN)
                                   (MV
                                    T (WIDTH-OF-WIDEST-INT ARG1))
                                   (IF
                                    (EQ 'BYTES-TO-BITS FN)
                                    (MV T (BYTES-TO-BITS ARG1))
                                    (IF
                                     (EQ 'CONSP FN)
                                     (MV T (CONSP ARG1))
                                     (IF
                                      (EQ 'TRUE-LISTP FN)
                                      (MV T (TRUE-LISTP ARG1))
                                      (IF
                                       (EQ 'STRINGP FN)
                                       (MV T (STRINGP ARG1))
                                       (IF
                                        (EQ 'STRIP-CARS FN)
                                        (MV T
                                            (STRIP-CARS-UNGUARDED
                                             ARG1))
                                        (IF
                                         (EQ 'STRIP-CDRS FN)
                                         (MV T
                                             (STRIP-CDRS-UNGUARDED
                                              ARG1))
                                         (IF
                                          (EQ 'no-duplicatesp-equal FN)
                                          (MV
                                           T (no-duplicatesp-equal ARG1))
                                          (IF
                                           (EQ 'ALL-INTEGERP FN)
                                           (MV
                                            T
                                            (ALL-INTEGERP ARG1))
                                           (IF
                                            (EQ 'TRUE-LIST-FIX
                                                FN)
                                            (MV T
                                                (TRUE-LIST-FIX
                                                 ARG1))
                                            (IF
                                             (EQ 'KEY-LIST FN)
                                             (MV
                                              T (KEY-LIST ARG1))
                                             (IF
                                              (EQ 'RKEYS FN)
                                              (MV T (RKEYS ARG1))
                                              (IF
                                               (EQ 'LIST::2SET
                                                   FN)
                                               (MV T
                                                   (LIST::2SET
                                                    ARG1))
                                               (IF
                                                (EQ 'BOOLEANP FN)
                                                (MV
                                                 T
                                                 (BOOLEANP ARG1))
                                                (IF
                                                 (EQ
                                                  'BOOL-FIX$INLINE
                                                  FN)
                                                 (MV T
                                                     (BOOL-FIX$INLINE
                                                      ARG1))
                                                 (IF
                                                  (EQ 'ALL-SAME
                                                      FN)
                                                  (MV T
                                                      (ALL-SAME
                                                       ARG1))
                                                  (IF
                                                   (EQ
                                                    'SYMBOL-NAME
                                                    FN)
                                                   (MV
                                                    T
                                                    (SYMBOL-NAME-UNGUARDED
                                                     ARG1))
                                                   (IF
                                                    (EQ
                                                     'SYMBOL-PACKAGE-NAME
                                                     FN)
                                                    (MV
                                                     T
                                                     (SYMBOL-PACKAGE-NAME-UNGUARDED
                                                      ARG1))
                                                    (IF
                                                     (EQ
                                                      'CODE-CHAR
                                                      FN)
                                                     (MV
                                                      T
                                                      (CODE-CHAR-UNGUARDED
                                                       ARG1))
                                                     (IF
                                                      (EQ
                                                       'CHAR-CODE
                                                       FN)
                                                      (MV
                                                       T
                                                       (CHAR-CODE-UNGUARDED
                                                        ARG1))
                                                      (IF
                                                       (EQ
                                                        'BOOL-TO-BIT
                                                        FN)
                                                       (MV
                                                        T
                                                        (BOOL-TO-BIT
                                                         ARG1))
                                                       (IF
                                                        (EQ 'LG
                                                            FN)
                                                        (MV
                                                         T
                                                         (LG-UNGUARDED
                                                          ARG1))
                                                        (IF
                                                         (EQ
                                                          'POWER-OF-2P
                                                          FN)
                                                         (MV
                                                          T
                                                          (POWER-OF-2P
                                                           ARG1))
                                                         (IF
                                                          (EQ
                                                           'NOT
                                                           FN)
                                                          (MV
                                                           T
                                                           (NOT
                                                            ARG1))
                                                          (IF
                                                           (EQ
                                                            'PRINT-CONSTANT
                                                            FN)
                                                           (MV
                                                            T
                                                            (PRINT-CONSTANT
                                                             ARG1))
                                                           (IF
                                                            (EQ
                                                             'RATIONALP
                                                             FN)
                                                            (MV
                                                             T
                                                             (RATIONALP
                                                              ARG1))
                                                            (IF
                                                             (EQ
                                                              'INTEGERP
                                                              FN)
                                                             (MV
                                                              T
                                                              (INTEGERP
                                                               ARG1))
                                                             (IF
                                                              (EQ
                                                               'POSP
                                                               FN)
                                                              (MV
                                                               T
                                                               (POSP
                                                                ARG1))
                                                              (IF
                                                               (EQ
                                                                'NATP
                                                                FN)
                                                               (MV
                                                                T
                                                                (NATP
                                                                 ARG1))
                                                               (IF
                                                                (EQ
                                                                 'QUOTEP
                                                                 FN)
                                                                (MV
                                                                 T
                                                                 (QUOTEP
                                                                  ARG1))
                                                                (MV
                                                                 NIL
                                                                 NIL)))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (LET
           ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
           (IF
            (ENDP ARGS-TO-WALK-DOWN)
            (LET
             ((ARG2 (UNQUOTE (NTH 1 ARGS)))
              (ARG1 (UNQUOTE (NTH 0 ARGS))))
             (IF
              (EQ 'symbol< FN)
              (MV T (symbol<-unguarded ARG1 ARG2))
              (IF
               (EQ 'SET::IN FN)
               (MV T (SET::IN-UNGUARDED ARG1 ARG2))
               (IF
                (EQ 'GROUP2 FN)
                (MV T (GROUP2 ARG1 ARG2))
                (IF
                 (EQ 'GROUP FN)
                 (MV T (GROUP ARG1 ARG2))
                 (IF
                  (EQ 'LOOKUP FN)
                  (MV T (LOOKUP ARG1 ARG2))
                  (IF
                   (EQ 'LOOKUP-EQ FN)
                   (MV T (LOOKUP-EQ ARG1 ARG2))
                   (IF
                    (EQ 'CEILING FN)
                    (MV T (CEILING-UNGUARDED ARG1 ARG2))
                    (IF
                     (EQ 'EQ FN)
                     (MV T (EQUAL ARG1 ARG2))
                     (IF
                      (EQ 'BVNOT-LIST FN)
                      (MV T (BVNOT-LIST-UNGUARDED ARG1 ARG2))
                      (IF
                       (EQ 'BINARY-* FN)
                       (MV T (BINARY-*-UNGUARDED ARG1 ARG2))
                       (IF
                        (EQ 'NTH FN)
                        (MV T (NTH-UNGUARDED ARG1 ARG2))
                        (IF
                         (EQ 'LOGEXT FN)
                         (MV T (LOGEXT ARG1 (IFIX ARG2)))
                         (IF
                          (EQ 'LOGTAIL$INLINE FN)
                          (MV T (LOGTAIL-UNGUARDED ARG1 ARG2))
                          (IF
                           (EQ 'BVCHOP FN)
                           (MV T (BVCHOP-UNGUARDED ARG1 ARG2))
                           (IF
                            (EQ 'CONS FN)
                            (MV T (CONS ARG1 ARG2))
                            (IF
                             (EQ 'GETBIT FN)
                             (MV T (GETBIT-UNGUARDED ARG1 ARG2))
                             (IF
                              (EQ 'MOD FN)
                              (MV T (MOD ARG1 ARG2))
                              (IF
                               (EQ 'MAX FN)
                               (MV T (MAX-UNGUARDED ARG1 ARG2))
                               (IF
                                (EQ 'MIN FN)
                                (MV T (MIN-UNGUARDED ARG1 ARG2))
                                (IF
                                 (EQ 'EXPT FN)
                                 (MV T (EXPT-UNGUARDED ARG1 ARG2))
                                 (IF
                                  (EQ 'BITXOR FN)
                                  (MV
                                   T (BITXOR-UNGUARDED ARG1 ARG2))
                                  (IF
                                   (EQ 'BITAND FN)
                                   (MV
                                    T
                                    (BITAND-UNGUARDED ARG1 ARG2))
                                   (IF
                                    (EQ 'BITOR FN)
                                    (MV
                                     T
                                     (BITOR-UNGUARDED ARG1 ARG2))
                                    (IF
                                     (EQ 'ALL-SIGNED-BYTE-P FN)
                                     (MV T
                                         (ALL-SIGNED-BYTE-P
                                          ARG1 ARG2))
                                     (IF
                                      (EQ 'ALL-UNSIGNED-BYTE-P FN)
                                      (MV T
                                          (ALL-UNSIGNED-BYTE-P
                                           ARG1 ARG2))
                                      (IF
                                       (EQ 'BVCHOP-LIST FN)
                                       (MV T
                                           (BVCHOP-LIST-UNGUARDED
                                            ARG1 ARG2))
                                       (IF
                                        (EQ 'UNSIGNED-BYTE-P FN)
                                        (MV T
                                            (UNSIGNED-BYTE-P
                                             ARG1 ARG2))
                                        (IF
                                         (EQ 'SIGNED-BYTE-P FN)
                                         (MV T
                                             (SIGNED-BYTE-P
                                              ARG1 ARG2))
                                         (IF
                                          (EQ 'GETBIT-IS-ALWAYS-1
                                              FN)
                                          (MV T
                                              (GETBIT-IS-ALWAYS-1-UNGUARDED
                                               ARG1 ARG2))
                                          (IF
                                           (EQ 'GETBIT-IS-ALWAYS-0
                                               FN)
                                           (MV T
                                               (GETBIT-IS-ALWAYS-0-UNGUARDED
                                                ARG1 ARG2))
                                           (IF
                                            (EQ 'BINARY-APPEND FN)
                                            (MV T
                                                (BINARY-APPEND-UNGUARDED
                                                 ARG1 ARG2))
                                            (IF
                                             (EQ 'FIRSTN FN)
                                             (MV T
                                                 (FIRSTN-UNGUARDED
                                                  ARG1 ARG2))
                                             (IF
                                              (EQ 'TAKE FN)
                                              (MV T
                                                  (TAKE-UNGUARDED
                                                   ARG1 ARG2))
                                              (IF
                                               (EQ 'NTHCDR FN)
                                               (MV
                                                T
                                                (NTHCDR-UNGUARDED
                                                 ARG1 ARG2))
                                               (IF
                                                (EQ 'G FN)
                                                (MV
                                                 T (G ARG1 ARG2))
                                                (IF
                                                 (EQ 'MEMBER-EQUAL
                                                     FN)
                                                 (MV
                                                  T
                                                  (MEMBER-EQUAL
                                                   ARG1 ARG2))
                                                 (IF
                                                  (EQ 'FLOOR FN)
                                                  (MV
                                                   T
                                                   (FLOOR
                                                    ARG1 ARG2))
                                                  (IF
                                                   (EQ
                                                    'SET::INSERT
                                                    FN)
                                                   (MV
                                                    T
                                                    (SET::INSERT
                                                     ARG1 ARG2))
                                                   (IF
                                                    (EQ
                                                     'LEFTROTATE32
                                                     FN)
                                                    (MV
                                                     T
                                                     (LEFTROTATE32-UNGUARDED
                                                      ARG1 ARG2))
                                                    (IF
                                                     (EQ
                                                      'SET::UNION
                                                      FN)
                                                     (MV
                                                      T
                                                      (SET::UNION
                                                       ARG1 ARG2))
                                                     (IF
                                                      (EQ
                                                       'GETBIT-LIST
                                                       FN)
                                                      (MV
                                                       T
                                                       (GETBIT-LIST
                                                        ARG1
                                                        ARG2))
                                                      (IF
                                                       (EQ 'BOOLOR
                                                           FN)
                                                       (MV
                                                        T
                                                        (BOOLOR
                                                         ARG1
                                                         ARG2))
                                                       (IF
                                                        (EQ
                                                         'BOOLAND
                                                         FN)
                                                        (MV
                                                         T
                                                         (BOOLAND
                                                          ARG1
                                                          ARG2))
                                                        (IF
                                                         (EQ
                                                          'FIRST-NON-MEMBER
                                                          FN)
                                                         (MV
                                                          T
                                                          (FIRST-NON-MEMBER
                                                           ARG1
                                                           ARG2))
                                                         (IF
                                                          (EQ
                                                           'IMPLIES
                                                           FN)
                                                          (MV
                                                           T
                                                           (IMPLIES
                                                            ARG1
                                                            ARG2))
                                                          ;; (IF
                                                          ;;  (EQ
                                                          ;;   'BINARY-AND
                                                          ;;   FN)
                                                          ;;  (MV
                                                          ;;   T
                                                          ;;   (BINARY-AND
                                                          ;;    ARG1
                                                          ;;    ARG2))
                                                           (IF
                                                            (EQ
                                                             'REPEATBIT
                                                             FN)
                                                            (MV
                                                             T
                                                             (REPEATBIT
                                                              ARG1
                                                              ARG2))
                                                            (IF
                                                             (EQ
                                                              'ALL-EQUAL$
                                                              FN)
                                                             (MV
                                                              T
                                                              (ALL-EQUAL$
                                                               ARG1
                                                               ARG2))
                                                             (IF
                                                              (EQ
                                                               'INTERSECTION-EQUAL
                                                               FN)
                                                              (MV
                                                               T
                                                               (INTERSECTION-EQUAL
                                                                ARG1
                                                                ARG2))
                                                              (IF
                                                               (EQ
                                                                'TAKE-EVERY-NTH
                                                                FN)
                                                               (MV
                                                                T
                                                                (TAKE-EVERY-NTH
                                                                 ARG1
                                                                 ARG2))
                                                               (IF
                                                                (EQ
                                                                 'ALL-ITEMS-LESS-THAN
                                                                 FN)
                                                                (MV
                                                                 T
                                                                 (ALL-ITEMS-LESS-THAN
                                                                  ARG1
                                                                  ARG2))
                                                                (IF
                                                                 (EQ
                                                                  'BINARY-+
                                                                  FN)
                                                                 (MV
                                                                  T
                                                                  (BINARY-+-UNGUARDED
                                                                   ARG1
                                                                   ARG2))
                                                                 (IF
                                                                  (EQ
                                                                   'TRIM
                                                                   FN)
                                                                  (MV
                                                                   T
                                                                   (TRIM-UNGUARDED

                                                                    ARG1

                                                                    ARG2))
                                                                  (IF
                                                                   (EQ

                                                                    'UNSIGNED-BYTE-P-FORCED

                                                                    FN)
                                                                   (MV

                                                                    T

                                                                    (UNSIGNED-BYTE-P-FORCED

                                                                     ARG1

                                                                     ARG2))
                                                                   (IF

                                                                    (EQ

                                                                     'ASSOC-EQUAL

                                                                     FN)

                                                                    (MV

                                                                     T

                                                                     (ASSOC-EQUAL-UNGUARDED

                                                                      ARG1

                                                                      ARG2))

                                                                    (IF

                                                                     (EQ

                                                                      'BVUMINUS

                                                                      FN)

                                                                     (MV

                                                                      T

                                                                      (BVUMINUS-UNGUARDED

                                                                       ARG1

                                                                       ARG2))

                                                                     (IF

                                                                      (EQ

                                                                       'BVNOT

                                                                       FN)

                                                                      (MV

                                                                       T

                                                                       (BVNOT-UNGUARDED

                                                                        ARG1

                                                                        ARG2))

                                                                      (IF

                                                                       (EQ

                                                                        'LOOKUP

                                                                        FN)

                                                                       (MV

                                                                        T

                                                                        (LOOKUP

                                                                         ARG1

                                                                         ARG2))

                                                                       (IF

                                                                        (EQ

                                                                         'LOOKUP-EQUAL

                                                                         FN)

                                                                        (MV

                                                                         T

                                                                         (LOOKUP-EQUAL

                                                                          ARG1

                                                                          ARG2))

                                                                        (IF

                                                                         (EQ

                                                                          'PREFIXP

                                                                          FN)

                                                                         (MV

                                                                          T

                                                                          (PREFIXP

                                                                           ARG1

                                                                           ARG2))

                                                                         (IF

                                                                          (EQ

                                                                           'LIST-EQUIV

                                                                           FN)

                                                                          (MV

                                                                           T

                                                                           (LIST-EQUIV

                                                                            ARG1

                                                                            ARG2))

                                                                          (IF

                                                                           (EQ

                                                                            'EQL

                                                                            FN)

                                                                           (MV

                                                                            T

                                                                            (EQUAL

                                                                             ARG1

                                                                             ARG2))

                                                                           (IF

                                                                            (EQ

                                                                             'EQUAL

                                                                             FN)

                                                                            (MV

                                                                             T

                                                                             (EQUAL

                                                                              ARG1

                                                                              ARG2))

                                                                            (IF

                                                                             (EQ

                                                                              '<

                                                                              FN)

                                                                             (MV

                                                                              T

                                                                              (<-UNGUARDED

                                                                               ARG1

                                                                               ARG2))

                                                                             (IF

                                                                              (EQ

                                                                               'COERCE

                                                                               FN)

                                                                              (MV

                                                                               T

                                                                               (COERCE-UNGUARDED

                                                                                ARG1

                                                                                ARG2))

                                                                              (IF

                                                                               (EQ

                                                                                'ADD-TO-END

                                                                                FN)

                                                                               (MV

                                                                                T

                                                                                (ADD-TO-END

                                                                                 ARG1

                                                                                 ARG2))

                                                                               (IF

                                                                                (EQ

                                                                                 'ALL-ALL-UNSIGNED-BYTE-P

                                                                                 FN)

                                                                                (MV

                                                                                 T

                                                                                 (ALL-ALL-UNSIGNED-BYTE-P

                                                                                  ARG1

                                                                                  ARG2))

                                                                                (IF (EQ 'ITEMS-HAVE-LEN FN)

                                                                                    (MV T (ITEMS-HAVE-LEN-UNGUARDED ARG1 ARG2))
                                                                                    (IF (EQ 'mv-nth FN)

                                                                                        (MV T (mv-nth-unguarded ARG1 ARG2))

                                                                                        (MV

                                                                                         NIL

                                                                                         NIL))))))))))))))))))))))))
                                                           ;;)
                                                           ))))))))))))))))))))))))))))))))))))))))))))))
                        (LET
                         ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                         (IF
                          (ENDP ARGS-TO-WALK-DOWN)
                          (LET
                           ((ARG3 (UNQUOTE (NTH 2 ARGS)))
                            (ARG2 (UNQUOTE (NTH 1 ARGS)))
                            (ARG1 (UNQUOTE (NTH 0 ARGS))))
                           (IF
                            (EQ 'BVXOR-LIST FN)
                            (MV T (BVXOR-LIST-UNGUARDED ARG1 ARG2 ARG3))
                            (IF
                             (EQ 'SUBRANGE FN)
                             (MV T
                                 (SUBRANGE (NFIX ARG1) (NFIX ARG2) ARG3))
                             (IF
                              (EQ 'KEEP-ITEMS-LESS-THAN FN)
                              (MV T
                                  (KEEP-ITEMS-LESS-THAN-UNGUARDED
                                       ARG1 ARG2 ARG3))
                              (IF
                               (EQ 'BVSHL FN)
                               (MV T (BVSHL ARG1 ARG2 ARG3))
                               (IF
                                (EQ 'SLICE FN)
                                (MV T (SLICE-LESS-GUARDED ARG1 ARG2 ARG3))
                                (IF
                                 (EQ 'IF FN)
                                 (MV T (IF ARG1 ARG2 ARG3))
                                 (IF
                                  (EQ 'UPDATE-NTH FN)
                                  (MV T (UPDATE-NTH ARG1 ARG2 ARG3))
                                  (IF
                                   (EQ 'ARRAY-ELEM-2D FN)
                                   (MV T (ARRAY-ELEM-2D ARG1 ARG2 ARG3))
                                   (IF
                                    (EQ 'BOOLIF FN)
                                    (MV T (BOOLIF ARG1 ARG2 ARG3))
                                    (IF
                                     (EQ 'MYIF FN)
                                     (MV T (MYIF ARG1 ARG2 ARG3))
                                     (IF
                                      (EQ 'NTH2 FN)
                                      (MV T (NTH2 ARG1 ARG2 ARG3))
                                      (IF
                                       (EQ 'S FN)
                                       (MV T (S ARG1 ARG2 ARG3))
                                       (IF
                                        (EQ 'SBVLE FN)
                                        (MV T (SBVLE ARG1 ARG2 ARG3))
                                        (IF
                                         (EQ 'SBVLT FN)
                                         (MV T
                                             (SBVLT ARG1 (IFIX ARG2)
                                                    (IFIX ARG3)))
                                         (IF
                                          (EQ 'SBVMODDOWN FN)
                                          (MV T (SBVMODDOWN ARG1 ARG2 ARG3))
                                          (IF
                                           (EQ 'SBVREM FN)
                                           (MV T (SBVREM ARG1 ARG2 ARG3))
                                           (IF
                                            (EQ 'SBVDIVDOWN FN)
                                            (MV
                                               T (SBVDIVDOWN ARG1 ARG2 ARG3))
                                            (IF
                                             (EQ 'SBVDIV FN)
                                             (MV T (SBVDIV ARG1 ARG2 ARG3))
                                             (IF
                                              (EQ 'BVSX FN)
                                              (MV T (BVSX ARG1 ARG2 ARG3))
                                              (IF
                                               (EQ 'BVDIV FN)
                                               (MV T
                                                   (BVDIV-UNGUARDED
                                                        ARG1 ARG2 ARG3))
                                               (IF
                                                (EQ 'BVMOD FN)
                                                (MV T
                                                    (BVMOD-UNGUARDED
                                                         ARG1 ARG2 ARG3))
                                                (IF
                                                 (EQ 'BVMINUS FN)
                                                 (MV T
                                                     (BVMINUS-UNGUARDED
                                                          ARG1 ARG2 ARG3))
                                                 (IF
                                                  (EQ 'BVPLUS FN)
                                                  (MV T
                                                      (BVPLUS-UNGUARDED
                                                           ARG1 ARG2 ARG3))
                                                  (IF
                                                   (EQ 'BVMULT FN)
                                                   (MV T
                                                       (BVMULT-UNGUARDED
                                                            ARG1 ARG2 ARG3))
                                                   (IF
                                                    (EQ 'BVAND FN)
                                                    (MV T
                                                        (BVAND-UNGUARDED
                                                             ARG1 ARG2 ARG3))
                                                    (IF
                                                     (EQ 'BVOR FN)
                                                     (MV
                                                        T
                                                        (BVOR-UNGUARDED
                                                             ARG1 ARG2 ARG3))
                                                     (IF
                                                      (EQ 'BVXOR FN)
                                                      (MV
                                                        T
                                                        (BVXOR-UNGUARDED
                                                             ARG1 ARG2 ARG3))
                                                      (IF
                                                       (EQ 'BVLE FN)
                                                       (MV
                                                        T
                                                        (BVLE-UNGUARDED
                                                             ARG1 ARG2 ARG3))
                                                       (IF
                                                        (EQ 'BVLT FN)
                                                        (MV
                                                         T
                                                         (BVLT-UNGUARDED
                                                             ARG1 ARG2 ARG3))
                                                        (IF
                                                         (EQ 'BVPLUS-LST FN)
                                                         (MV
                                                          T
                                                          (BVPLUS-LST
                                                             ARG1 ARG2 ARG3))
                                                         (IF
                                                          (EQ 'UNPACKBV FN)
                                                          (MV
                                                           T
                                                           (UNPACKBV-LESS-GUARDED
                                                             ARG1 ARG2 ARG3))
                                                          (IF
                                                           (EQ 'PACKBV FN)
                                                           (MV
                                                            T
                                                            (PACKBV
                                                             ARG1 ARG2 ARG3))
                                                           (IF
                                                            (EQ
                                                               'BVASHR
                                                               FN)
                                                            (MV
                                                             T
                                                             (BVASHR
                                                                  ARG1
                                                                  ARG2 ARG3))
                                                            (IF
                                                             (EQ 'BVSHR FN)
                                                             (MV
                                                              T
                                                              (BVSHR
                                                                  ARG1
                                                                  ARG2 ARG3))
                                                             (IF
                                                              (EQ 'ACONS FN)
                                                              (MV
                                                               T
                                                               (ACONS
                                                                  ARG1
                                                                  ARG2 ARG3))
                                                              (IF
                                                               (EQ
                                                                  'LEFTROTATE
                                                                  FN)
                                                               (MV
                                                                T
                                                                (LEFTROTATE
                                                                  ARG1
                                                                  ARG2 ARG3))
                                                               (IF
                                                                (EQ
                                                                 'NEGATED-ELEMS-LISTP
                                                                 FN)
                                                                (MV
                                                                 T
                                                                 (NEGATED-ELEMS-LISTP-UNGUARDED
                                                                  ARG1
                                                                  ARG2 ARG3))
                                                                (IF
                                                                 (EQ
                                                                  'REPEAT-TAIL
                                                                  FN)
                                                                 (MV
                                                                  T
                                                                  (REPEAT-TAIL
                                                                    ARG1 ARG2
                                                                    ARG3))
                                                                 (MV
                                                                  NIL
                                                                  NIL))))))))))))))))))))))))))))))))))))))))
                          (LET
                           ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                           (IF
                            (ENDP ARGS-TO-WALK-DOWN)
                            (LET
                             ((ARG4 (UNQUOTE (NTH 3 ARGS)))
                              (ARG3 (UNQUOTE (NTH 2 ARGS)))
                              (ARG2 (UNQUOTE (NTH 1 ARGS)))
                              (ARG1 (UNQUOTE (NTH 0 ARGS))))
                             (IF
                              (EQ 'BVIF FN)
                              (MV T (BVIF-UNGUARDED ARG1 ARG2 ARG3 ARG4))
                              (IF
                               (EQ 'BV-ARRAY-READ FN)
                               (MV T
                                   (BV-ARRAY-READ-UNGUARDED
                                        ARG1 ARG2 ARG3 ARG4))
                               (IF
                                (EQ 'BVNTH FN)
                                (MV T (BVNTH ARG1 ARG2 (NFIX ARG3) ARG4))
                                (IF
                                 (EQ 'BVCAT FN)
                                 (MV T (BVCAT-UNGUARDED ARG1 ARG2 ARG3 ARG4))
                                 (IF
                                  (EQ 'BV-ARRAY-CLEAR FN)
                                  (MV T (BV-ARRAY-CLEAR ARG1 ARG2 ARG3 ARG4))
                                  (IF
                                   (EQ 'UPDATE-NTH2 FN)
                                   (MV T (UPDATE-NTH2 ARG1 ARG2 ARG3 ARG4))
                                   (IF
                                    (EQ 'UPDATE-SUBRANGE FN)
                                    (MV
                                     T (UPDATE-SUBRANGE ARG1 ARG2 ARG3 ARG4))
                                    (IF
                                     (EQ 'APPLY-AXE-EVALUATOR FN)
                                     (MV T
                                         (APPLY-AXE-EVALUATOR
                                              ARG1 ARG2 ARG3 ARRAY-DEPTH))
                                     (IF
                                      (EQ 'DAG-VAL-WITH-AXE-EVALUATOR FN)
                                      (MV
                                       T
                                       (DAG-VAL-WITH-AXE-EVALUATOR
                                           ARG1 ARG2 ARG3 (+ 1 ARRAY-DEPTH)))
                                      (MV NIL NIL)))))))))))
                            (LET
                             ((ARGS-TO-WALK-DOWN (CDR ARGS-TO-WALK-DOWN)))
                             (IF
                              (ENDP ARGS-TO-WALK-DOWN)
                              (LET
                               ((ARG5 (UNQUOTE (NTH 4 ARGS)))
                                (ARG4 (UNQUOTE (NTH 3 ARGS)))
                                (ARG3 (UNQUOTE (NTH 2 ARGS)))
                                (ARG2 (UNQUOTE (NTH 1 ARGS)))
                                (ARG1 (UNQUOTE (NTH 0 ARGS))))
                               (IF
                                  (EQ 'BV-ARRAY-CLEAR-RANGE FN)
                                  (MV T
                                      (BV-ARRAY-CLEAR-RANGE
                                           ARG1 ARG2 ARG3 ARG4 ARG5))
                                  (IF (EQ 'BV-ARRAY-WRITE FN)
                                      (MV T
                                          (BV-ARRAY-WRITE-UNGUARDED (NFIX ARG1)
                                                          (NFIX ARG2)
                                                          (NFIX ARG3)
                                                          ARG4 ARG5))
                                      (IF (EQ 'UPDATE-SUBRANGE2 FN)
                                          (MV T
                                              (UPDATE-SUBRANGE2
                                                   ARG1 ARG2 ARG3 ARG4 ARG5))
                                          (MV NIL NIL)))))
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
                                      (EQ 'EVAL-DAG-WITH-AXE-EVALUATOR FN)
                                      (MV
                                       T
                                       (EVAL-DAG-WITH-AXE-EVALUATOR
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
