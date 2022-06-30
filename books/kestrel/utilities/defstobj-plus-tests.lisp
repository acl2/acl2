; Tests of defstobj+
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defstobj-plus")
(include-book "kestrel/utilities/deftest" :dir :system)

;; TODO: Add more tests

(deftest
  (defund mypred (x) (declare (xargs :guard t)) (and (consp x) (integerp (car x)) (<= (car x) 3)))
  (defstobj+ my-stobj0
    (scalar-field-1 :type integer :initially 7)
    (scalar-field-2 :type (satisfies mypred) :initially (3 . 4))
    (scalar-field-3 :type (integer 10 20) :initially 15)
    (array-field-1 :type (array integer (100)) :initially 3)
    (array-field-2 :type (array (satisfies mypred) (200)) :initially (3 . 4))
    (array-field-3 :type (array (integer 10 20) (300)) :initially 15)
    )
  ;; expected results:
  (must-be-redundant
   ;; The defstobj:
   (DEFSTOBJ MY-STOBJ0
     (SCALAR-FIELD-1 :TYPE INTEGER :INITIALLY 7)
     (SCALAR-FIELD-2 :TYPE (SATISFIES MYPRED) :INITIALLY (3 . 4))
     (SCALAR-FIELD-3 :TYPE (INTEGER 10 20) :INITIALLY 15)
     (ARRAY-FIELD-1 :TYPE (ARRAY INTEGER (100)) :INITIALLY 3)
     (ARRAY-FIELD-2 :TYPE (ARRAY (SATISFIES MYPRED) (200)) :INITIALLY (3 . 4))
     (ARRAY-FIELD-3 :TYPE (ARRAY (INTEGER 10 20) (300)) :INITIALLY 15)
     )
   (IN-THEORY (DISABLE MY-STOBJ0P
                       CREATE-MY-STOBJ0
                       SCALAR-FIELD-1P ; just integerp
                       SCALAR-FIELD-1
                       UPDATE-SCALAR-FIELD-1
                       SCALAR-FIELD-2P ; just mypred
                       SCALAR-FIELD-2
                       UPDATE-SCALAR-FIELD-2
                       SCALAR-FIELD-3P ; not already a notion with a name
                       SCALAR-FIELD-3
                       UPDATE-SCALAR-FIELD-3
                       ARRAY-FIELD-1P ; recognizes a list of integers
                       ARRAY-FIELD-1I UPDATE-ARRAY-FIELD-1I
                       ARRAY-FIELD-1-LENGTH
                       RESIZE-ARRAY-FIELD-1
                       ARRAY-FIELD-2P ; recognizes a list of mypreds
                       ARRAY-FIELD-2I
                       UPDATE-ARRAY-FIELD-2I
                       ARRAY-FIELD-2-LENGTH
                       RESIZE-ARRAY-FIELD-2
                       ARRAY-FIELD-3P
                       ARRAY-FIELD-3I UPDATE-ARRAY-FIELD-3I
                       ARRAY-FIELD-3-LENGTH
                       RESIZE-ARRAY-FIELD-3))


   (DEFTHM MY-STOBJ0P-OF-UPDATE-SCALAR-FIELD-1
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (INTEGERP V))
              (MY-STOBJ0P (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))))
   (DEFTHM SCALAR-FIELD-1-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (SCALAR-FIELD-1 (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            V))

   ;; updating the same field twice:
   (DEFTHM UPDATE-SCALAR-FIELD-1-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (UPDATE-SCALAR-FIELD-1 V2 (UPDATE-SCALAR-FIELD-1 V1 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0)))
   (DEFTHM INTEGERP-OF-SCALAR-FIELD-1
     (IMPLIES (MY-STOBJ0P MY-STOBJ0)
              (INTEGERP (SCALAR-FIELD-1 MY-STOBJ0))))
   ;; read over write
   (DEFTHM SCALAR-FIELD-2-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (SCALAR-FIELD-2 (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            (SCALAR-FIELD-2 MY-STOBJ0)))
   ;; write over write
   (DEFTHM UPDATE-SCALAR-FIELD-2-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (UPDATE-SCALAR-FIELD-2 V1 (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2
                                   (UPDATE-SCALAR-FIELD-2 V1 MY-STOBJ0))))
   ;; read over write
   (DEFTHM SCALAR-FIELD-3-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (SCALAR-FIELD-3 (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            (SCALAR-FIELD-3 MY-STOBJ0)))
   ;; write over write
   (DEFTHM UPDATE-SCALAR-FIELD-3-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (UPDATE-SCALAR-FIELD-3 V1 (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2 (UPDATE-SCALAR-FIELD-3 V1 MY-STOBJ0))))
   ;; read over write
   (DEFTHM ARRAY-FIELD-1I-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (ARRAY-FIELD-1I I (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            (ARRAY-FIELD-1I I MY-STOBJ0)))
   ;; read over write
   (DEFTHM ARRAY-FIELD-1-LENGTH-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (ARRAY-FIELD-1-LENGTH (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            (ARRAY-FIELD-1-LENGTH MY-STOBJ0)))
   ;; write over write
   (DEFTHM UPDATE-ARRAY-FIELD-1I-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (UPDATE-ARRAY-FIELD-1I I V1 (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2 (UPDATE-ARRAY-FIELD-1I I V1 MY-STOBJ0))))
   ;; write over write
   (DEFTHM RESIZE-ARRAY-FIELD-1-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (RESIZE-ARRAY-FIELD-1 I (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2 (RESIZE-ARRAY-FIELD-1 I MY-STOBJ0))))
   (DEFTHM ARRAY-FIELD-2I-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (ARRAY-FIELD-2I I (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            (ARRAY-FIELD-2I I MY-STOBJ0)))
   (DEFTHM ARRAY-FIELD-2-LENGTH-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (ARRAY-FIELD-2-LENGTH (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            (ARRAY-FIELD-2-LENGTH MY-STOBJ0)))
   (DEFTHM UPDATE-ARRAY-FIELD-2I-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (UPDATE-ARRAY-FIELD-2I I
                                   V1 (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2
                                   (UPDATE-ARRAY-FIELD-2I I V1 MY-STOBJ0))))
   (DEFTHM
     RESIZE-ARRAY-FIELD-2-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (RESIZE-ARRAY-FIELD-2 I (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2 (RESIZE-ARRAY-FIELD-2 I MY-STOBJ0))))
   (DEFTHM
     ARRAY-FIELD-3I-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (ARRAY-FIELD-3I I (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            (ARRAY-FIELD-3I I MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-3-LENGTH-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (ARRAY-FIELD-3-LENGTH (UPDATE-SCALAR-FIELD-1 V MY-STOBJ0))
            (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (UPDATE-ARRAY-FIELD-3I I
                                   V1 (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2
                                   (UPDATE-ARRAY-FIELD-3I I V1 MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-3-OF-UPDATE-SCALAR-FIELD-1
     (EQUAL (RESIZE-ARRAY-FIELD-3 I (UPDATE-SCALAR-FIELD-1 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-1 V2 (RESIZE-ARRAY-FIELD-3 I MY-STOBJ0)))
     )
   (DEFTHM MY-STOBJ0P-OF-UPDATE-SCALAR-FIELD-2
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (MYPRED V))
              (MY-STOBJ0P (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))))
   (DEFTHM
     SCALAR-FIELD-2-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (SCALAR-FIELD-2 (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            V))
   (DEFTHM
     UPDATE-SCALAR-FIELD-2-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (UPDATE-SCALAR-FIELD-2 V2 (UPDATE-SCALAR-FIELD-2 V1 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-2 V2 MY-STOBJ0)))
   (DEFTHM
     MYPRED-OF-SCALAR-FIELD-2
     (IMPLIES (MY-STOBJ0P MY-STOBJ0)
              (MYPRED (SCALAR-FIELD-2 MY-STOBJ0))))
   (DEFTHM
     SCALAR-FIELD-1-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (SCALAR-FIELD-1 (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            (SCALAR-FIELD-1 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-3-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (SCALAR-FIELD-3 (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            (SCALAR-FIELD-3 MY-STOBJ0)))
   (DEFTHM
     UPDATE-SCALAR-FIELD-3-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (UPDATE-SCALAR-FIELD-3 V1 (UPDATE-SCALAR-FIELD-2 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-2 V2
                                   (UPDATE-SCALAR-FIELD-3 V1 MY-STOBJ0))))
   (DEFTHM
     ARRAY-FIELD-1I-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (ARRAY-FIELD-1I I (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            (ARRAY-FIELD-1I I MY-STOBJ0)))
   (DEFTHM ARRAY-FIELD-1-LENGTH-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (ARRAY-FIELD-1-LENGTH (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            (ARRAY-FIELD-1-LENGTH MY-STOBJ0)))
   (DEFTHM
     UPDATE-ARRAY-FIELD-1I-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (UPDATE-ARRAY-FIELD-1I I
                                   V1 (UPDATE-SCALAR-FIELD-2 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-2 V2
                                   (UPDATE-ARRAY-FIELD-1I I V1 MY-STOBJ0))))
   (DEFTHM
     RESIZE-ARRAY-FIELD-1-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (RESIZE-ARRAY-FIELD-1 I (UPDATE-SCALAR-FIELD-2 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-2 V2 (RESIZE-ARRAY-FIELD-1 I MY-STOBJ0))))
   (DEFTHM
     ARRAY-FIELD-2I-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (ARRAY-FIELD-2I I (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            (ARRAY-FIELD-2I I MY-STOBJ0)))
   (DEFTHM ARRAY-FIELD-2-LENGTH-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (ARRAY-FIELD-2-LENGTH (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            (ARRAY-FIELD-2-LENGTH MY-STOBJ0)))
   (DEFTHM
     UPDATE-ARRAY-FIELD-2I-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (UPDATE-ARRAY-FIELD-2I I
                                   V1 (UPDATE-SCALAR-FIELD-2 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-2 V2
                                   (UPDATE-ARRAY-FIELD-2I I V1 MY-STOBJ0))))
   (DEFTHM
     RESIZE-ARRAY-FIELD-2-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (RESIZE-ARRAY-FIELD-2 I (UPDATE-SCALAR-FIELD-2 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-2 V2 (RESIZE-ARRAY-FIELD-2 I MY-STOBJ0))))
   (DEFTHM
     ARRAY-FIELD-3I-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (ARRAY-FIELD-3I I (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            (ARRAY-FIELD-3I I MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-3-LENGTH-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (ARRAY-FIELD-3-LENGTH (UPDATE-SCALAR-FIELD-2 V MY-STOBJ0))
            (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (UPDATE-ARRAY-FIELD-3I I
                                   V1 (UPDATE-SCALAR-FIELD-2 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-2 V2
                                   (UPDATE-ARRAY-FIELD-3I I V1 MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-3-OF-UPDATE-SCALAR-FIELD-2
     (EQUAL (RESIZE-ARRAY-FIELD-3 I (UPDATE-SCALAR-FIELD-2 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-2 V2 (RESIZE-ARRAY-FIELD-3 I MY-STOBJ0)))
     )
   (DEFTHM MY-STOBJ0P-OF-UPDATE-SCALAR-FIELD-3
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (IF (INTEGERP V)
                       (IF (NOT (< V '10))
                           (NOT (< '20 V))
                           'NIL)
                       'NIL))
              (MY-STOBJ0P (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0)))
     )
   (DEFTHM
     SCALAR-FIELD-3-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (SCALAR-FIELD-3 (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            V)
     )
   (DEFTHM
     UPDATE-SCALAR-FIELD-3-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (UPDATE-SCALAR-FIELD-3 V2 (UPDATE-SCALAR-FIELD-3 V1 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-3 V2 MY-STOBJ0))
     )
   (DEFTHM
     FIELD-TYPE-OF-SCALAR-FIELD-3
     (IMPLIES (MY-STOBJ0P MY-STOBJ0)
              (IF (INTEGERP (SCALAR-FIELD-3 MY-STOBJ0))
                  (IF (NOT (< (SCALAR-FIELD-3 MY-STOBJ0) '10))
                      (NOT (< '20 (SCALAR-FIELD-3 MY-STOBJ0)))
                      'NIL)
                  'NIL))
     )
   (DEFTHM
     SCALAR-FIELD-1-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (SCALAR-FIELD-1 (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            (SCALAR-FIELD-1 MY-STOBJ0))
     )
   (DEFTHM
     SCALAR-FIELD-2-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (SCALAR-FIELD-2 (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            (SCALAR-FIELD-2 MY-STOBJ0))
     )
   (DEFTHM
     ARRAY-FIELD-1I-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (ARRAY-FIELD-1I I (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            (ARRAY-FIELD-1I I MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-1-LENGTH-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (ARRAY-FIELD-1-LENGTH (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            (ARRAY-FIELD-1-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-1I-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (UPDATE-ARRAY-FIELD-1I I
                                   V1 (UPDATE-SCALAR-FIELD-3 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-3 V2
                                   (UPDATE-ARRAY-FIELD-1I I V1 MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-1-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (RESIZE-ARRAY-FIELD-1 I (UPDATE-SCALAR-FIELD-3 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-3 V2 (RESIZE-ARRAY-FIELD-1 I MY-STOBJ0)))
     )
   (DEFTHM
     ARRAY-FIELD-2I-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (ARRAY-FIELD-2I I (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            (ARRAY-FIELD-2I I MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-2-LENGTH-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (ARRAY-FIELD-2-LENGTH (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            (ARRAY-FIELD-2-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-2I-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (UPDATE-ARRAY-FIELD-2I I
                                   V1 (UPDATE-SCALAR-FIELD-3 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-3 V2
                                   (UPDATE-ARRAY-FIELD-2I I V1 MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-2-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (RESIZE-ARRAY-FIELD-2 I (UPDATE-SCALAR-FIELD-3 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-3 V2 (RESIZE-ARRAY-FIELD-2 I MY-STOBJ0)))
     )
   (DEFTHM
     ARRAY-FIELD-3I-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (ARRAY-FIELD-3I I (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            (ARRAY-FIELD-3I I MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-3-LENGTH-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (ARRAY-FIELD-3-LENGTH (UPDATE-SCALAR-FIELD-3 V MY-STOBJ0))
            (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (UPDATE-ARRAY-FIELD-3I I
                                   V1 (UPDATE-SCALAR-FIELD-3 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-3 V2
                                   (UPDATE-ARRAY-FIELD-3I I V1 MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-3-OF-UPDATE-SCALAR-FIELD-3
     (EQUAL (RESIZE-ARRAY-FIELD-3 I (UPDATE-SCALAR-FIELD-3 V2 MY-STOBJ0))
            (UPDATE-SCALAR-FIELD-3 V2 (RESIZE-ARRAY-FIELD-3 I MY-STOBJ0)))
     )

   ;; don't export?  disable?
   (DEFTHM ARRAY-FIELD-1P-OF-MAKE-LIST-AC
     (IMPLIES (ARRAY-FIELD-1P ACC)
              (ARRAY-FIELD-1P (MAKE-LIST-AC N '3 ACC))))
   ;; don't export?  disable?
   (DEFTHM ARRAY-FIELD-1P-OF-UPDATE-NTH
     (IMPLIES (AND (ARRAY-FIELD-1P L)
                   (NATP KEY)
                   (< KEY (LEN L))
                   (INTEGERP VAL))
              (ARRAY-FIELD-1P (UPDATE-NTH KEY VAL L))))
   (DEFTHM MY-STOBJ0P-OF-UPDATE-ARRAY-FIELD-1I
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (< I (ARRAY-FIELD-1-LENGTH MY-STOBJ0))
                   (NATP I)
                   (INTEGERP V))
              (MY-STOBJ0P (UPDATE-ARRAY-FIELD-1I I V MY-STOBJ0))))
   (DEFTHM
     ARRAY-FIELD-1-LENGTH-OF-UPDATE-ARRAY-FIELD-1I
     (IMPLIES
      (AND (< I (ARRAY-FIELD-1-LENGTH MY-STOBJ0))
           (NATP I))
      (EQUAL (ARRAY-FIELD-1-LENGTH (UPDATE-ARRAY-FIELD-1I I V MY-STOBJ0))
             (ARRAY-FIELD-1-LENGTH MY-STOBJ0))))

   (DEFTHM
     ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-1I-SAME
     (EQUAL (ARRAY-FIELD-1I I (UPDATE-ARRAY-FIELD-1I I V MY-STOBJ0))
            V))
   (DEFTHM
     ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-1I-DIFF
     (IMPLIES (NOT (EQUAL (NFIX I1) (NFIX I2)))
              (EQUAL (ARRAY-FIELD-1I I1
                                     (UPDATE-ARRAY-FIELD-1I I2 V MY-STOBJ0))
                     (ARRAY-FIELD-1I I1 MY-STOBJ0))))
   (DEFTHMD ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-1I-SPLIT
     (EQUAL (ARRAY-FIELD-1I I1
                            (UPDATE-ARRAY-FIELD-1I I2 V MY-STOBJ0))
            (IF (EQUAL (NFIX I1) (NFIX I2))
                V (ARRAY-FIELD-1I I1 MY-STOBJ0))))
   (DEFTHM
     UPDATE-ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-1I-SAME
     (EQUAL (UPDATE-ARRAY-FIELD-1I I V1
                                   (UPDATE-ARRAY-FIELD-1I I V2 MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-1I I V1 MY-STOBJ0)))
   (DEFTHM
     UPDATE-ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-1I-DIFF
     (IMPLIES
      (AND (SYNTAXP (NOT (TERM-ORDER I1 I2)))
           (NOT (EQUAL (NFIX I1) (NFIX I2))))
      (EQUAL (UPDATE-ARRAY-FIELD-1I I1 V1
                                    (UPDATE-ARRAY-FIELD-1I I2 V2 MY-STOBJ0))
             (UPDATE-ARRAY-FIELD-1I I2 V2
                                    (UPDATE-ARRAY-FIELD-1I I1 V1 MY-STOBJ0)))))
   (DEFTHM
     UPDATE-ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-1I-SPLIT
     (IMPLIES
      (SYNTAXP (NOT (TERM-ORDER I1 I2)))
      (EQUAL
       (UPDATE-ARRAY-FIELD-1I I1 V1
                              (UPDATE-ARRAY-FIELD-1I I2 V2 MY-STOBJ0))
       (IF (EQUAL (NFIX I1) (NFIX I2))
           (UPDATE-ARRAY-FIELD-1I I1 V1 MY-STOBJ0)
           (UPDATE-ARRAY-FIELD-1I I2 V2
                                  (UPDATE-ARRAY-FIELD-1I I1 V1 MY-STOBJ0))))))
   (DEFTHM
     UPDATE-ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-1I-SAME-VALUES
     (IMPLIES
      (SYNTAXP (NOT (TERM-ORDER I1 I2)))
      (EQUAL (UPDATE-ARRAY-FIELD-1I I1 V
                                    (UPDATE-ARRAY-FIELD-1I I2 V MY-STOBJ0))
             (UPDATE-ARRAY-FIELD-1I I2 V
                                    (UPDATE-ARRAY-FIELD-1I I1 V MY-STOBJ0)))))
   ;; don't export?  disable?
   (DEFTHMD INTEGERP-OF-NTH-WHEN-ARRAY-FIELD-1P
     (IMPLIES (AND (ARRAY-FIELD-1P L)
                   (NATP N)
                   (< N (LEN L)))
              (INTEGERP (NTH N L))))
   (DEFTHM
     INTEGERP-OF-ARRAY-FIELD-1I
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (NATP I)
                   (< I (ARRAY-FIELD-1-LENGTH MY-STOBJ0)))
              (INTEGERP (ARRAY-FIELD-1I I MY-STOBJ0))))
   (DEFTHM
     SCALAR-FIELD-1-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (SCALAR-FIELD-1 (UPDATE-ARRAY-FIELD-1I I V MY-STOBJ0))
            (SCALAR-FIELD-1 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-1-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (SCALAR-FIELD-1 (RESIZE-ARRAY-FIELD-1 I MY-STOBJ0))
            (SCALAR-FIELD-1 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-2-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (SCALAR-FIELD-2 (UPDATE-ARRAY-FIELD-1I I V MY-STOBJ0))
            (SCALAR-FIELD-2 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-2-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (SCALAR-FIELD-2 (RESIZE-ARRAY-FIELD-1 I MY-STOBJ0))
            (SCALAR-FIELD-2 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-3-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (SCALAR-FIELD-3 (UPDATE-ARRAY-FIELD-1I I V MY-STOBJ0))
            (SCALAR-FIELD-3 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-3-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (SCALAR-FIELD-3 (RESIZE-ARRAY-FIELD-1 I MY-STOBJ0))
            (SCALAR-FIELD-3 MY-STOBJ0)))
   (DEFTHM
     ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (ARRAY-FIELD-2I I1
                            (UPDATE-ARRAY-FIELD-1I I2 V MY-STOBJ0))
            (ARRAY-FIELD-2I I1 MY-STOBJ0)))
   (DEFTHM ARRAY-FIELD-2-LENGTH-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (ARRAY-FIELD-2-LENGTH (UPDATE-ARRAY-FIELD-1I I V MY-STOBJ0))
            (ARRAY-FIELD-2-LENGTH MY-STOBJ0)))
   (DEFTHM
     ARRAY-FIELD-2I-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (ARRAY-FIELD-2I I1 (RESIZE-ARRAY-FIELD-1 I2 MY-STOBJ0))
            (ARRAY-FIELD-2I I1 MY-STOBJ0)))
   (DEFTHM ARRAY-FIELD-2-LENGTH-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (ARRAY-FIELD-2-LENGTH (RESIZE-ARRAY-FIELD-1 I MY-STOBJ0))
            (ARRAY-FIELD-2-LENGTH MY-STOBJ0)))
   (DEFTHM
     UPDATE-ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (UPDATE-ARRAY-FIELD-2I I1 V1
                                   (UPDATE-ARRAY-FIELD-1I I2 V2 MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-1I I2 V2
                                   (UPDATE-ARRAY-FIELD-2I I1 V1 MY-STOBJ0))))
   (DEFTHM
     RESIZE-ARRAY-FIELD-2-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (RESIZE-ARRAY-FIELD-2 I1
                                  (UPDATE-ARRAY-FIELD-1I I2 V MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-1I I2
                                   V (RESIZE-ARRAY-FIELD-2 I1 MY-STOBJ0))))
   (DEFTHM
     UPDATE-ARRAY-FIELD-2I-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (UPDATE-ARRAY-FIELD-2I I1
                                   V (RESIZE-ARRAY-FIELD-1 I2 MY-STOBJ0))
            (RESIZE-ARRAY-FIELD-1 I2
                                  (UPDATE-ARRAY-FIELD-2I I1 V MY-STOBJ0))))
   (DEFTHM
     RESIZE-ARRAY-FIELD-2-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (RESIZE-ARRAY-FIELD-2 I1 (RESIZE-ARRAY-FIELD-1 I2 MY-STOBJ0))
            (RESIZE-ARRAY-FIELD-1 I2 (RESIZE-ARRAY-FIELD-2 I1 MY-STOBJ0))))
   (DEFTHM
     ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (ARRAY-FIELD-3I I1
                            (UPDATE-ARRAY-FIELD-1I I2 V MY-STOBJ0))
            (ARRAY-FIELD-3I I1 MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-3-LENGTH-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (ARRAY-FIELD-3-LENGTH (UPDATE-ARRAY-FIELD-1I I V MY-STOBJ0))
            (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     ARRAY-FIELD-3I-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (ARRAY-FIELD-3I I1 (RESIZE-ARRAY-FIELD-1 I2 MY-STOBJ0))
            (ARRAY-FIELD-3I I1 MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-3-LENGTH-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (ARRAY-FIELD-3-LENGTH (RESIZE-ARRAY-FIELD-1 I MY-STOBJ0))
            (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (UPDATE-ARRAY-FIELD-3I I1 V1
                                   (UPDATE-ARRAY-FIELD-1I I2 V2 MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-1I I2 V2
                                   (UPDATE-ARRAY-FIELD-3I I1 V1 MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-3-OF-UPDATE-ARRAY-FIELD-1I
     (EQUAL (RESIZE-ARRAY-FIELD-3 I1
                                  (UPDATE-ARRAY-FIELD-1I I2 V MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-1I I2
                                   V (RESIZE-ARRAY-FIELD-3 I1 MY-STOBJ0)))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (UPDATE-ARRAY-FIELD-3I I1
                                   V (RESIZE-ARRAY-FIELD-1 I2 MY-STOBJ0))
            (RESIZE-ARRAY-FIELD-1 I2
                                  (UPDATE-ARRAY-FIELD-3I I1 V MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-3-OF-RESIZE-ARRAY-FIELD-1
     (EQUAL (RESIZE-ARRAY-FIELD-3 I1 (RESIZE-ARRAY-FIELD-1 I2 MY-STOBJ0))
            (RESIZE-ARRAY-FIELD-1 I2 (RESIZE-ARRAY-FIELD-3 I1 MY-STOBJ0)))
     )
   (DEFTHM ARRAY-FIELD-2P-OF-MAKE-LIST-AC
     (IMPLIES (ARRAY-FIELD-2P ACC)
              (ARRAY-FIELD-2P (MAKE-LIST-AC N '(3 . 4) ACC))))
   (DEFTHM ARRAY-FIELD-2P-OF-UPDATE-NTH
     (IMPLIES (AND (ARRAY-FIELD-2P L)
                   (NATP KEY)
                   (< KEY (LEN L))
                   (MYPRED VAL))
              (ARRAY-FIELD-2P (UPDATE-NTH KEY VAL L))))
   (DEFTHM
     MY-STOBJ0P-OF-UPDATE-ARRAY-FIELD-2I
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (< I (ARRAY-FIELD-2-LENGTH MY-STOBJ0))
                   (NATP I)
                   (MYPRED V))
              (MY-STOBJ0P (UPDATE-ARRAY-FIELD-2I I V MY-STOBJ0))))
   (DEFTHM
     ARRAY-FIELD-2-LENGTH-OF-UPDATE-ARRAY-FIELD-2I
     (IMPLIES
      (AND (< I (ARRAY-FIELD-2-LENGTH MY-STOBJ0))
           (NATP I))
      (EQUAL (ARRAY-FIELD-2-LENGTH (UPDATE-ARRAY-FIELD-2I I V MY-STOBJ0))
             (ARRAY-FIELD-2-LENGTH MY-STOBJ0))))

   (DEFTHM
     ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-2I-SAME
     (EQUAL (ARRAY-FIELD-2I I (UPDATE-ARRAY-FIELD-2I I V MY-STOBJ0))
            V))
   (DEFTHM
     ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-2I-DIFF
     (IMPLIES (NOT (EQUAL (NFIX I1) (NFIX I2)))
              (EQUAL (ARRAY-FIELD-2I I1
                                     (UPDATE-ARRAY-FIELD-2I I2 V MY-STOBJ0))
                     (ARRAY-FIELD-2I I1 MY-STOBJ0))))
   (DEFTHMD ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-2I-SPLIT
     (EQUAL (ARRAY-FIELD-2I I1
                            (UPDATE-ARRAY-FIELD-2I I2 V MY-STOBJ0))
            (IF (EQUAL (NFIX I1) (NFIX I2))
                V (ARRAY-FIELD-2I I1 MY-STOBJ0))))
   (DEFTHM
     UPDATE-ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-2I-SAME
     (EQUAL (UPDATE-ARRAY-FIELD-2I I V1
                                   (UPDATE-ARRAY-FIELD-2I I V2 MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-2I I V1 MY-STOBJ0)))
   (DEFTHM
     UPDATE-ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-2I-DIFF
     (IMPLIES
      (AND (SYNTAXP (NOT (TERM-ORDER I1 I2)))
           (NOT (EQUAL (NFIX I1) (NFIX I2))))
      (EQUAL (UPDATE-ARRAY-FIELD-2I I1 V1
                                    (UPDATE-ARRAY-FIELD-2I I2 V2 MY-STOBJ0))
             (UPDATE-ARRAY-FIELD-2I I2 V2
                                    (UPDATE-ARRAY-FIELD-2I I1 V1 MY-STOBJ0)))))
   (DEFTHM
     UPDATE-ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-2I-SPLIT
     (IMPLIES
      (SYNTAXP (NOT (TERM-ORDER I1 I2)))
      (EQUAL
       (UPDATE-ARRAY-FIELD-2I I1 V1
                              (UPDATE-ARRAY-FIELD-2I I2 V2 MY-STOBJ0))
       (IF (EQUAL (NFIX I1) (NFIX I2))
           (UPDATE-ARRAY-FIELD-2I I1 V1 MY-STOBJ0)
           (UPDATE-ARRAY-FIELD-2I I2 V2
                                  (UPDATE-ARRAY-FIELD-2I I1 V1 MY-STOBJ0))))))
   (DEFTHM
     UPDATE-ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-2I-SAME-VALUES
     (IMPLIES
      (SYNTAXP (NOT (TERM-ORDER I1 I2)))
      (EQUAL (UPDATE-ARRAY-FIELD-2I I1 V
                                    (UPDATE-ARRAY-FIELD-2I I2 V MY-STOBJ0))
             (UPDATE-ARRAY-FIELD-2I I2 V
                                    (UPDATE-ARRAY-FIELD-2I I1 V MY-STOBJ0)))))
   (DEFTHMD MYPRED-OF-NTH-WHEN-ARRAY-FIELD-2P
     (IMPLIES (AND (ARRAY-FIELD-2P L)
                   (NATP N)
                   (< N (LEN L)))
              (MYPRED (NTH N L))))
   (DEFTHM
     MYPRED-OF-ARRAY-FIELD-2I
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (NATP I)
                   (< I (ARRAY-FIELD-2-LENGTH MY-STOBJ0)))
              (MYPRED (ARRAY-FIELD-2I I MY-STOBJ0))))
   (DEFTHM
     SCALAR-FIELD-1-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (SCALAR-FIELD-1 (UPDATE-ARRAY-FIELD-2I I V MY-STOBJ0))
            (SCALAR-FIELD-1 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-1-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (SCALAR-FIELD-1 (RESIZE-ARRAY-FIELD-2 I MY-STOBJ0))
            (SCALAR-FIELD-1 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-2-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (SCALAR-FIELD-2 (UPDATE-ARRAY-FIELD-2I I V MY-STOBJ0))
            (SCALAR-FIELD-2 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-2-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (SCALAR-FIELD-2 (RESIZE-ARRAY-FIELD-2 I MY-STOBJ0))
            (SCALAR-FIELD-2 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-3-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (SCALAR-FIELD-3 (UPDATE-ARRAY-FIELD-2I I V MY-STOBJ0))
            (SCALAR-FIELD-3 MY-STOBJ0)))
   (DEFTHM
     SCALAR-FIELD-3-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (SCALAR-FIELD-3 (RESIZE-ARRAY-FIELD-2 I MY-STOBJ0))
            (SCALAR-FIELD-3 MY-STOBJ0)))
   (DEFTHM
     ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (ARRAY-FIELD-1I I1
                            (UPDATE-ARRAY-FIELD-2I I2 V MY-STOBJ0))
            (ARRAY-FIELD-1I I1 MY-STOBJ0)))
   (DEFTHM ARRAY-FIELD-1-LENGTH-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (ARRAY-FIELD-1-LENGTH (UPDATE-ARRAY-FIELD-2I I V MY-STOBJ0))
            (ARRAY-FIELD-1-LENGTH MY-STOBJ0)))
   (DEFTHM
     ARRAY-FIELD-1I-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (ARRAY-FIELD-1I I1 (RESIZE-ARRAY-FIELD-2 I2 MY-STOBJ0))
            (ARRAY-FIELD-1I I1 MY-STOBJ0)))
   (DEFTHM ARRAY-FIELD-1-LENGTH-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (ARRAY-FIELD-1-LENGTH (RESIZE-ARRAY-FIELD-2 I MY-STOBJ0))
            (ARRAY-FIELD-1-LENGTH MY-STOBJ0)))
   (DEFTHM
     ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (ARRAY-FIELD-3I I1
                            (UPDATE-ARRAY-FIELD-2I I2 V MY-STOBJ0))
            (ARRAY-FIELD-3I I1 MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-3-LENGTH-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (ARRAY-FIELD-3-LENGTH (UPDATE-ARRAY-FIELD-2I I V MY-STOBJ0))
            (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     ARRAY-FIELD-3I-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (ARRAY-FIELD-3I I1 (RESIZE-ARRAY-FIELD-2 I2 MY-STOBJ0))
            (ARRAY-FIELD-3I I1 MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-3-LENGTH-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (ARRAY-FIELD-3-LENGTH (RESIZE-ARRAY-FIELD-2 I MY-STOBJ0))
            (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (UPDATE-ARRAY-FIELD-3I I1 V1
                                   (UPDATE-ARRAY-FIELD-2I I2 V2 MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-2I I2 V2
                                   (UPDATE-ARRAY-FIELD-3I I1 V1 MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-3-OF-UPDATE-ARRAY-FIELD-2I
     (EQUAL (RESIZE-ARRAY-FIELD-3 I1
                                  (UPDATE-ARRAY-FIELD-2I I2 V MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-2I I2
                                   V (RESIZE-ARRAY-FIELD-3 I1 MY-STOBJ0)))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (UPDATE-ARRAY-FIELD-3I I1
                                   V (RESIZE-ARRAY-FIELD-2 I2 MY-STOBJ0))
            (RESIZE-ARRAY-FIELD-2 I2
                                  (UPDATE-ARRAY-FIELD-3I I1 V MY-STOBJ0)))
     )
   (DEFTHM
     RESIZE-ARRAY-FIELD-3-OF-RESIZE-ARRAY-FIELD-2
     (EQUAL (RESIZE-ARRAY-FIELD-3 I1 (RESIZE-ARRAY-FIELD-2 I2 MY-STOBJ0))
            (RESIZE-ARRAY-FIELD-2 I2 (RESIZE-ARRAY-FIELD-3 I1 MY-STOBJ0)))
     )
   (DEFTHM ARRAY-FIELD-3P-OF-MAKE-LIST-AC
     (IMPLIES (ARRAY-FIELD-3P ACC)
              (ARRAY-FIELD-3P (MAKE-LIST-AC N '15 ACC)))
     )
   (DEFTHM ARRAY-FIELD-3P-OF-UPDATE-NTH
     (IMPLIES (AND (ARRAY-FIELD-3P L)
                   (NATP KEY)
                   (< KEY (LEN L))
                   (IF (INTEGERP VAL)
                       (IF (NOT (< VAL '10))
                           (NOT (< '20 VAL))
                           'NIL)
                       'NIL))
              (ARRAY-FIELD-3P (UPDATE-NTH KEY VAL L)))
     )
   (DEFTHM
     MY-STOBJ0P-OF-UPDATE-ARRAY-FIELD-3I
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (< I (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
                   (NATP I)
                   (IF (INTEGERP V)
                       (IF (NOT (< V '10))
                           (NOT (< '20 V))
                           'NIL)
                       'NIL))
              (MY-STOBJ0P (UPDATE-ARRAY-FIELD-3I I V MY-STOBJ0)))
     )
   (DEFTHM
     ARRAY-FIELD-3-LENGTH-OF-UPDATE-ARRAY-FIELD-3I
     (IMPLIES
      (AND (< I (ARRAY-FIELD-3-LENGTH MY-STOBJ0))
           (NATP I))
      (EQUAL (ARRAY-FIELD-3-LENGTH (UPDATE-ARRAY-FIELD-3I I V MY-STOBJ0))
             (ARRAY-FIELD-3-LENGTH MY-STOBJ0)))
     )
   (DEFTHM
     ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-3I-SAME
     (EQUAL (ARRAY-FIELD-3I I (UPDATE-ARRAY-FIELD-3I I V MY-STOBJ0))
            V)
     )
   (DEFTHM
     ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-3I-DIFF
     (IMPLIES (NOT (EQUAL (NFIX I1) (NFIX I2)))
              (EQUAL (ARRAY-FIELD-3I I1
                                     (UPDATE-ARRAY-FIELD-3I I2 V MY-STOBJ0))
                     (ARRAY-FIELD-3I I1 MY-STOBJ0)))
     )
   (DEFTHMD ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-3I-SPLIT
     (EQUAL (ARRAY-FIELD-3I I1
                            (UPDATE-ARRAY-FIELD-3I I2 V MY-STOBJ0))
            (IF (EQUAL (NFIX I1) (NFIX I2))
                V (ARRAY-FIELD-3I I1 MY-STOBJ0))))
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-3I-SAME
     (EQUAL (UPDATE-ARRAY-FIELD-3I I V1
                                   (UPDATE-ARRAY-FIELD-3I I V2 MY-STOBJ0))
            (UPDATE-ARRAY-FIELD-3I I V1 MY-STOBJ0))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-3I-DIFF
     (IMPLIES
      (AND (SYNTAXP (NOT (TERM-ORDER I1 I2)))
           (NOT (EQUAL (NFIX I1) (NFIX I2))))
      (EQUAL (UPDATE-ARRAY-FIELD-3I I1 V1
                                    (UPDATE-ARRAY-FIELD-3I I2 V2 MY-STOBJ0))
             (UPDATE-ARRAY-FIELD-3I I2 V2
                                    (UPDATE-ARRAY-FIELD-3I I1 V1 MY-STOBJ0))))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-3I-SPLIT
     (IMPLIES
      (SYNTAXP (NOT (TERM-ORDER I1 I2)))
      (EQUAL
       (UPDATE-ARRAY-FIELD-3I I1 V1
                              (UPDATE-ARRAY-FIELD-3I I2 V2 MY-STOBJ0))
       (IF (EQUAL (NFIX I1) (NFIX I2))
           (UPDATE-ARRAY-FIELD-3I I1 V1 MY-STOBJ0)
           (UPDATE-ARRAY-FIELD-3I I2 V2
                                  (UPDATE-ARRAY-FIELD-3I I1 V1 MY-STOBJ0)))))
     )
   (DEFTHM
     UPDATE-ARRAY-FIELD-3I-OF-UPDATE-ARRAY-FIELD-3I-SAME-VALUES
     (IMPLIES
      (SYNTAXP (NOT (TERM-ORDER I1 I2)))
      (EQUAL (UPDATE-ARRAY-FIELD-3I I1 V
                                    (UPDATE-ARRAY-FIELD-3I I2 V MY-STOBJ0))
             (UPDATE-ARRAY-FIELD-3I I2 V
                                    (UPDATE-ARRAY-FIELD-3I I1 V MY-STOBJ0))))
     )
   (DEFTHMD ELEMENT-TYPE-OF-NTH-WHEN-ARRAY-FIELD-3P
     (IMPLIES (AND (ARRAY-FIELD-3P L)
                   (NATP N)
                   (< N (LEN L)))
              (IF (INTEGERP (NTH N L))
                  (IF (NOT (< (NTH N L) '10))
                      (NOT (< '20 (NTH N L)))
                      'NIL)
                  'NIL))
     )
   (DEFTHM
     ELEMENT-TYPE-OF-ARRAY-FIELD-3I
     (IMPLIES (AND (MY-STOBJ0P MY-STOBJ0)
                   (NATP I)
                   (< I (ARRAY-FIELD-3-LENGTH MY-STOBJ0)))
              (IF (INTEGERP (ARRAY-FIELD-3I I MY-STOBJ0))
                  (IF (NOT (< (ARRAY-FIELD-3I I MY-STOBJ0) '10))
                      (NOT (< '20 (ARRAY-FIELD-3I I MY-STOBJ0)))
                      'NIL)
                  'NIL))
     )
   (DEFTHM
     SCALAR-FIELD-1-OF-UPDATE-ARRAY-FIELD-3I
     (EQUAL (SCALAR-FIELD-1 (UPDATE-ARRAY-FIELD-3I I V MY-STOBJ0))
            (SCALAR-FIELD-1 MY-STOBJ0))
     )
   (DEFTHM
     SCALAR-FIELD-1-OF-RESIZE-ARRAY-FIELD-3
     (EQUAL (SCALAR-FIELD-1 (RESIZE-ARRAY-FIELD-3 I MY-STOBJ0))
            (SCALAR-FIELD-1 MY-STOBJ0))
     )
   (DEFTHM
     SCALAR-FIELD-2-OF-UPDATE-ARRAY-FIELD-3I
     (EQUAL (SCALAR-FIELD-2 (UPDATE-ARRAY-FIELD-3I I V MY-STOBJ0))
            (SCALAR-FIELD-2 MY-STOBJ0))
     )
   (DEFTHM
     SCALAR-FIELD-2-OF-RESIZE-ARRAY-FIELD-3
     (EQUAL (SCALAR-FIELD-2 (RESIZE-ARRAY-FIELD-3 I MY-STOBJ0))
            (SCALAR-FIELD-2 MY-STOBJ0))
     )
   (DEFTHM
     SCALAR-FIELD-3-OF-UPDATE-ARRAY-FIELD-3I
     (EQUAL (SCALAR-FIELD-3 (UPDATE-ARRAY-FIELD-3I I V MY-STOBJ0))
            (SCALAR-FIELD-3 MY-STOBJ0))
     )
   (DEFTHM
     SCALAR-FIELD-3-OF-RESIZE-ARRAY-FIELD-3
     (EQUAL (SCALAR-FIELD-3 (RESIZE-ARRAY-FIELD-3 I MY-STOBJ0))
            (SCALAR-FIELD-3 MY-STOBJ0))
     )
   (DEFTHM
     ARRAY-FIELD-1I-OF-UPDATE-ARRAY-FIELD-3I
     (EQUAL (ARRAY-FIELD-1I I1
                            (UPDATE-ARRAY-FIELD-3I I2 V MY-STOBJ0))
            (ARRAY-FIELD-1I I1 MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-1-LENGTH-OF-UPDATE-ARRAY-FIELD-3I
     (EQUAL (ARRAY-FIELD-1-LENGTH (UPDATE-ARRAY-FIELD-3I I V MY-STOBJ0))
            (ARRAY-FIELD-1-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     ARRAY-FIELD-1I-OF-RESIZE-ARRAY-FIELD-3
     (EQUAL (ARRAY-FIELD-1I I1 (RESIZE-ARRAY-FIELD-3 I2 MY-STOBJ0))
            (ARRAY-FIELD-1I I1 MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-1-LENGTH-OF-RESIZE-ARRAY-FIELD-3
     (EQUAL (ARRAY-FIELD-1-LENGTH (RESIZE-ARRAY-FIELD-3 I MY-STOBJ0))
            (ARRAY-FIELD-1-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     ARRAY-FIELD-2I-OF-UPDATE-ARRAY-FIELD-3I
     (EQUAL (ARRAY-FIELD-2I I1
                            (UPDATE-ARRAY-FIELD-3I I2 V MY-STOBJ0))
            (ARRAY-FIELD-2I I1 MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-2-LENGTH-OF-UPDATE-ARRAY-FIELD-3I
     (EQUAL (ARRAY-FIELD-2-LENGTH (UPDATE-ARRAY-FIELD-3I I V MY-STOBJ0))
            (ARRAY-FIELD-2-LENGTH MY-STOBJ0))
     )
   (DEFTHM
     ARRAY-FIELD-2I-OF-RESIZE-ARRAY-FIELD-3
     (EQUAL (ARRAY-FIELD-2I I1 (RESIZE-ARRAY-FIELD-3 I2 MY-STOBJ0))
            (ARRAY-FIELD-2I I1 MY-STOBJ0))
     )
   (DEFTHM ARRAY-FIELD-2-LENGTH-OF-RESIZE-ARRAY-FIELD-3
     (EQUAL (ARRAY-FIELD-2-LENGTH (RESIZE-ARRAY-FIELD-3 I MY-STOBJ0))
            (ARRAY-FIELD-2-LENGTH MY-STOBJ0))
     )

   ;; stobj creator returns a well-formed stobj:
   (DEFTHM MY-STOBJ0P-OF-CREATE-MY-STOBJ0
     (MY-STOBJ0P (CREATE-MY-STOBJ0)))

   ))

(defstobj+ my-stobj1
  (my-array-field :type (array integer (10000)) :initially 0)
  )

;; example (lots of theorems generated, since there are quite a few fields)
(defstobj+ my-stobj2
  (my-array1 :type (array integer (10000)) :initially 0)
  ;; resizable:
  (my-array2 :type (array integer (10000)) :resizable t :initially 0)
  ;; predicate is a conjunction:
  (my-array3 :type (array (satisfies natp) (10000)) :resizable t :initially 0)
  ;; predicate is t:
  (my-array4 :type (array t (10000)) :resizable t :initially 0)
  ;; element predicate is a call to satisfies:
  (my-array5 :type (array (satisfies consp) (10000)) :resizable t :initially (a b))
  ;; an element type which NIL satisfies (nicer theorems):
  (my-array6 :type (array (satisfies atom) (10000)) :resizable t :initially nil)
  ;; element predicate is a call to AND:
  (my-array7 :type (array (and integer (satisfies posp)) (10000)) :resizable t :initially 7)

  (my-scalar1 :type integer :initially 0)
  ;; A "scalar" field that is actually a cons ("scalar field" means not an array field, hash table field, etc.):
  (my-scalar2 :type (satisfies consp) :initially (a b))
  ;; predicate is t:
  (my-scalar3 :type t :initially 0)
  ;; a type-spec that is an AND:
  (my-scalar4 :type (and integer (satisfies posp)) :initially 100)
  my-scalar5
  )

;; A test with a hash-table field (note that defstobj+ doesn't generate theorems about the operations on it yet):
(defstobj+ my-stobj3
  (an-array-field :type (array integer (10000)) :initially 0 :resizable t)
  (a-scalar-field :type integer :initially 0)
  (a-hash-table-field :type (hash-table equal 200))
  )

;; A test where the field name is in the common-lisp package
(defstobj+ foo (print :type atom)
  :renaming ((common-lisp::print get-print)
             (common-lisp::printp printp)
             (common-lisp::update-print update-print)))

;; test of the renaming:
(defstobj+ foo2 (bar :type atom)
  :renaming ((bar get-bar)
             (barp my-barp)
             (update-bar my-update-bar)))

;; In this one, the field is in a different package and we use more exotic names:
(defstobj+ foo3 (print :type atom)
  :renaming ((common-lisp::print my-get-print)
             (common-lisp::printp my-printp)
             (common-lisp::update-print put-print)))

;; todo: uncomment/fix (evenp may not be legal below)
;; Test with some scalar types
;; (defstobj+ foo3
;;   (f1 :type atom :initially nil)
;;   (bar :type (integer 200 300) :initially 250)
;;   (baz :type t :initially 250) ; some theorems get suppressed since :type is t
;;   (evenf :type (satisfies evenp) :initially 250) ; some theorems get suppressed since :type is t
;;   ))

(defstobj+ foo4
  (f1 :type atom :initially nil)
  (bar :type (integer 200 300) :initially 250)
  (baz :type t :initially 250) ; some theorems get suppressed since :type is t
  (posf :type (satisfies posp) :initially 250) ; some theorems get suppressed since :type is t
  )
