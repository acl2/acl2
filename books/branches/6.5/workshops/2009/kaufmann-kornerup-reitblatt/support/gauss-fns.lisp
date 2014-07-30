;;; Edit for ACL2 workshop supporting materials:
;;; Deleted ACL2s-Preamble.

(IN-PACKAGE "ACL2")

(LOGIC)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFLABEL START-GAUSS)

(DEFUN-N CONSTANT[0]-0 (IN)
         (S* :|_T_0| 0))

(DEFUN-W CONSTANT[0]-0<_T_0> (IN)
         (G :|_T_0| (CONSTANT[0]-0 IN)))

(DEFUN-W INPUT1<_T_0> (IN)
         (G :INPUT1 IN))

(DEFUN-W |_N_8<_T_5>| (IN)
         (G :|_T_5| IN))

(DEFUN-W |_N_8<_T_6>| (IN)
         (G :|_T_6| IN))

(DEFUN-W |_N_8<_T_3>| (IN)
         (G :|_T_3| IN))

(DEFUN-W |_N_8<_T_4>| (IN) (G :LC IN))

(DEFUN-N DECREMENT-0 (IN)
         (S* :|_T_1| (1- (|_N_8<_T_6>| IN))))

(DEFUN-N ADD-0 (IN)
         (S* :|_T_2| (+ (|_N_8<_T_6>| IN)
                        (|_N_8<_T_5>| IN))))

(DEFUN-W |_N_33<_T_4>| (IN)
         (G :|_T_4| IN))

(DEFUN-W |_N_33<_T_3>| (IN)
         (G :|_T_3| IN))

(DEFUN-W |_N_33<_T_2>| (IN)
         (G :|_T_2| IN))

(DEFUN-W |_N_33<_T_1>| (IN)
         (G :|_T_1| IN))

(DEFUN-N CONSTANT[2]-1 (IN)
         (S* :|_T_0| 2))

(DEFUN-W CONSTANT[2]-1<_T_0> (IN)
         (G :|_T_0| (CONSTANT[2]-1 IN)))

(DEFUN-N CONSTANT[2]-2 (IN)
         (S* :|_T_0| 2))

(DEFUN-W CONSTANT[2]-2<_T_0> (IN)
         (G :|_T_0| (CONSTANT[2]-2 IN)))

(DEFUN-N SUBTRACT-0 (IN)
         (S* :|_T_2| (- (|_N_33<_T_2>| IN)
                        (|_N_33<_T_4>| IN))))

(DEFUN-N INCREMENT-0 (IN)
         (S* :|_T_1| (1+ (|_N_33<_T_3>| IN))))

(DEFUN-N INCREMENT-1 (IN)
         (S* :|_T_1| (1+ (|_N_33<_T_2>| IN))))

(DEFUN-W SUBTRACT-0<_T_2> (IN)
         (G :|_T_2| (SUBTRACT-0 IN)))

(DEFUN-W INCREMENT-0<_T_1> (IN)
         (G :|_T_1| (INCREMENT-0 IN)))

(DEFUN-W INCREMENT-1<_T_1> (IN)
         (G :|_T_1| (INCREMENT-1 IN)))

(DEFUN-N EQUAL?-0 (IN)
         (S* :|_T_2| (EQUAL (SUBTRACT-0<_T_2> IN)
                            (|_N_33<_T_3>| IN))))

(DEFUN-N MULTIPLY-0 (IN)
         (S* :|_T_2| (* (|_N_33<_T_3>| IN)
                        (INCREMENT-0<_T_1> IN))))

(DEFUN-N MULTIPLY-1 (IN)
         (S* :|_T_2| (* (|_N_33<_T_2>| IN)
                        (INCREMENT-1<_T_1> IN))))

(DEFUN-W EQUAL?-0<_T_2> (IN)
         (G :|_T_2| (EQUAL?-0 IN)))

(DEFUN-W MULTIPLY-0<_T_2> (IN)
         (G :|_T_2| (MULTIPLY-0 IN)))

(DEFUN-W MULTIPLY-1<_T_2> (IN)
         (G :|_T_2| (MULTIPLY-1 IN)))

(DEFUN-N DIVIDE-0 (IN)
         (S* :|_T_2| (/ (MULTIPLY-0<_T_2> IN)
                        (CONSTANT[2]-1<_T_0> IN))))

(DEFUN-N DIVIDE-1 (IN)
         (S* :|_T_2| (/ (MULTIPLY-1<_T_2> IN)
                        (CONSTANT[2]-2<_T_0> IN))))

(DEFUN-W DIVIDE-0<_T_2> (IN)
         (G :|_T_2| (DIVIDE-0 IN)))

(DEFUN-W DIVIDE-1<_T_2> (IN)
         (G :|_T_2| (DIVIDE-1 IN)))

(DEFUN-N SUBTRACT-1 (IN)
         (S* :|_T_2| (- (DIVIDE-1<_T_2> IN)
                        (DIVIDE-0<_T_2> IN))))

(DEFUN-W SUBTRACT-1<_T_2> (IN)
         (G :|_T_2| (SUBTRACT-1 IN)))

(DEFUN-N EQUAL?-1 (IN)
         (S* :|_T_2| (EQUAL (SUBTRACT-1<_T_2> IN)
                            (|_N_33<_T_1>| IN))))

(DEFUN-W EQUAL?-1<_T_2> (IN)
         (G :|_T_2| (EQUAL?-1 IN)))

(DEFUN-N AND-0 (IN)
         (S* :|_T_2| (AND (EQUAL?-0<_T_2> IN)
                          (EQUAL?-1<_T_2> IN))))

(DEFUN-W AND-0<_T_2> (IN)
         (G :|_T_2| (AND-0 IN)))

(DEFUN-N |_N_33| (IN)
         (S* :ASN (AND-0<_T_2> IN)))

(DEFUN |_N_33$INIT| (IN)
       (S* :|_T_1| (|_N_8<_T_5>| IN)
           :|_T_2| (|_N_8<_T_3>| IN)
           :|_T_3| (|_N_8<_T_6>| IN)
           :|_T_4| (|_N_8<_T_4>| IN)))

(DEFUN-ASN ACL2-LOOP-INV (IN)
           (|_N_33| (|_N_33$INIT| IN)))

(DEFUN-W DECREMENT-0<_T_1> (IN)
         (G :|_T_1| (DECREMENT-0 IN)))

(DEFUN-W ADD-0<_T_2> (IN)
         (G :|_T_2| (ADD-0 IN)))

(DEFUN-N |_N_8| (IN)
         (S* :|_T_1| (ADD-0<_T_2> IN)
             :|_T_2| (DECREMENT-0<_T_1> IN)))

(DEFUN |_N_8$STEP| (IN)
       (S :|_T_5| (G :|_T_1| (|_N_8| IN))
          (S :|_T_6| (G :|_T_2| (|_N_8| IN)) IN)))

(DEFUN |_N_8$LOOP| (N IN)
       (DECLARE (XARGS :MEASURE (NFIX (- N (G :LC IN)))))
       (COND ((OR (>= (G :LC IN) N)
                  (NOT (NATP N))
                  (NOT (NATP (G :LC IN))))
              IN)
             (T (|_N_8$LOOP| N
                             (S :LC (1+ (G :LC IN))
                                (|_N_8$STEP| IN))))))

(DEFUN |_N_8$LOOP$INIT| (IN)
       (S* :LC 0
           :|_T_3| (INPUT1<_T_0> IN)
           :|_T_5| (CONSTANT[0]-0<_T_0> IN)
           :|_T_6| (INPUT1<_T_0> IN)))

(DEFUN-N ACL2-LOOP (IN)
         (|_N_8$LOOP| (INPUT1<_T_0> IN)
                      (|_N_8$LOOP$INIT| IN)))

(DEFUN-W ACL2-LOOP<_T_5> (IN)
         (G :|_T_5| (ACL2-LOOP IN)))

(DEFUN-W |_N_5<_T_2>| (IN)
         (G :|_T_2| IN))

(DEFUN-W |_N_5<_T_1>| (IN)
         (G :|_T_1| IN))

(DEFUN-N CONSTANT[2]-3 (IN)
         (S* :|_T_0| 2))

(DEFUN-W CONSTANT[2]-3<_T_0> (IN)
         (G :|_T_0| (CONSTANT[2]-3 IN)))

(DEFUN-N INCREMENT-2 (IN)
         (S* :|_T_1| (1+ (|_N_5<_T_1>| IN))))

(DEFUN-W INCREMENT-2<_T_1> (IN)
         (G :|_T_1| (INCREMENT-2 IN)))

(DEFUN-N MULTIPLY-2 (IN)
         (S* :|_T_2| (* (|_N_5<_T_1>| IN)
                        (INCREMENT-2<_T_1> IN))))

(DEFUN-W MULTIPLY-2<_T_2> (IN)
         (G :|_T_2| (MULTIPLY-2 IN)))

(DEFUN-N DIVIDE-2 (IN)
         (S* :|_T_2| (/ (MULTIPLY-2<_T_2> IN)
                        (CONSTANT[2]-3<_T_0> IN))))

(DEFUN-W DIVIDE-2<_T_2> (IN)
         (G :|_T_2| (DIVIDE-2 IN)))

(DEFUN-N EQUAL?-2 (IN)
         (S* :|_T_2| (EQUAL (DIVIDE-2<_T_2> IN)
                            (|_N_5<_T_2>| IN))))

(DEFUN-W EQUAL?-2<_T_2> (IN)
         (G :|_T_2| (EQUAL?-2 IN)))

(DEFUN-N |_N_5| (IN)
         (S* :ASN (EQUAL?-2<_T_2> IN)))

(DEFUN |_N_5$INIT| (IN)
       (S* :|_T_1| (INPUT1<_T_0> IN)
           :|_T_2| (ACL2-LOOP<_T_5> IN)))

(DEFUN-ASN ACL2-TOP-INV (IN)
           (|_N_5| (|_N_5$INIT| IN)))

(DEFUN-W ACL2-TOP-INV<_T_2> (IN)
         (G :|_T_2| (ACL2-TOP-INV IN)))

(DEFUN GAUSS$INPUT-HYPS (IN)
       (AND (NATP (G :INPUT1 IN))))

(DEFTHEORY GAUSS
           (SET-DIFFERENCE-THEORIES (CURRENT-THEORY :HERE)
                                    (CURRENT-THEORY 'START-GAUSS)))

