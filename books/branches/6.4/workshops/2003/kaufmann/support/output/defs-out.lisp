(IN-PACKAGE "ACL2")

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(SET-BOGUS-MUTUAL-RECURSION-OK T)

(DEFUND G1 (X Y) (IF (ZP X) X Y))

(DEFUND G2 (X Y)
        (IF (CONSP X) (G2 (CDR X) Y) (G1 X Y)))

(MUTUAL-RECURSION
     (DEFUND REG1 (N)
             (DECLARE (XARGS :MEASURE (MAKE-ORD 1 (1+ (NFIX N)) 0)))
             (IF (ZP N)
                 0
                 (LOGXOR (WIRE1 (+ -1 N))
                         (INPUT1 (+ -1 N)))))
     (DEFUND REG2 (N)
             (DECLARE (XARGS :MEASURE (MAKE-ORD 1 (1+ (NFIX N)) 1)))
             (IF (ZP N)
                 (REG1 N)
                 (LOGAND (WIRE1 (+ -1 N))
                         (WIRE2 (+ -1 N)))))
     (DEFUND WIRE1 (N)
             (DECLARE (XARGS :MEASURE (MAKE-ORD 1 (1+ (NFIX N)) 2)))
             (LOGIOR (REG1 N) (INPUT2 N)))
     (DEFUND WIRE2 (N)
             (DECLARE (XARGS :MEASURE (MAKE-ORD 1 (1+ (NFIX N)) 3)))
             (+ -1 (- (WIRE1 N)))))

