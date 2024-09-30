(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUND CDLL_EXP NIL 13)

(DEFUND CDLL_MSB NIL (- (CDLL_EXP) 1))

(DEFUND CDLL_MAX_NODE1 NIL 8191)

(DEFUND CDLL_MAX_NODE NIL
  (- (CDLL_MAX_NODE1) 1))

(DEFUND CDLL_INITNODES-LOOP-0 (I CDOBJ)
  (DECLARE (XARGS :MEASURE (NFIX (- (CDLL_MAX_NODE1) I))))
  (IF (AND (INTEGERP I)
           (INTEGERP (CDLL_MAX_NODE1))
           (< I (CDLL_MAX_NODE1)))
      (LET* ((CDOBJ (AS 'NODEARR
                        (AS I
                            (AS 'ALLOC
                                (BITS 2 1 0)
                                (AG I (AG 'NODEARR CDOBJ)))
                            (AG 'NODEARR CDOBJ))
                        CDOBJ))
             (CDOBJ (AS 'NODEARR
                        (AS I
                            (AS 'VAL
                                (BITS 0 63 0)
                                (AG I (AG 'NODEARR CDOBJ)))
                            (AG 'NODEARR CDOBJ))
                        CDOBJ))
             (CDOBJ (AS 'NODEARR
                        (AS I
                            (AS 'PREV I (AG I (AG 'NODEARR CDOBJ)))
                            (AG 'NODEARR CDOBJ))
                        CDOBJ))
             (CDOBJ (AS 'NODEARR
                        (AS I
                            (AS 'NEXT I (AG I (AG 'NODEARR CDOBJ)))
                            (AG 'NODEARR CDOBJ))
                        CDOBJ)))
        (CDLL_INITNODES-LOOP-0 (+ I 1) CDOBJ))
    CDOBJ))

(DEFUND CDLL_INITNODES (CDOBJ)
  (LET* ((CDOBJ (AS 'NODEARR
                    (AS 0
                        (AS 'ALLOC
                            (BITS 2 1 0)
                            (AG 0 (AG 'NODEARR CDOBJ)))
                        (AG 'NODEARR CDOBJ))
                    CDOBJ))
         (CDOBJ (AS 'NODEARR
                    (AS 0
                        (AS 'VAL
                            (BITS 0 63 0)
                            (AG 0 (AG 'NODEARR CDOBJ)))
                        (AG 'NODEARR CDOBJ))
                    CDOBJ))
         (CDOBJ (AS 'NODEARR
                    (AS 0
                        (AS 'PREV 0 (AG 0 (AG 'NODEARR CDOBJ)))
                        (AG 'NODEARR CDOBJ))
                    CDOBJ))
         (CDOBJ (AS 'NODEARR
                    (AS 0
                        (AS 'NEXT 0 (AG 0 (AG 'NODEARR CDOBJ)))
                        (AG 'NODEARR CDOBJ))
                    CDOBJ)))
    (CDLL_INITNODES-LOOP-0 1 CDOBJ)))

(DEFUND CDLL_INITALL (CDOBJ)
  (LET* ((CDOBJ (AS 'NODEHD 0 CDOBJ))
         (CDOBJ (AS 'NODECOUNT 0 CDOBJ)))
    (CDLL_INITNODES CDOBJ)))

(DEFUND CDLL_ISEMPTY (CDOBJ)
  (LOG= (AG 'NODECOUNT CDOBJ) 0))

(DEFUND CDLL_ISFULL (CDOBJ)
  (LOG= (AG 'NODECOUNT CDOBJ)
        (CDLL_MAX_NODE1)))

(DEFUND CDLL_SIZEOF (CDOBJ)
  (AG 'NODECOUNT CDOBJ))

(DEFUND CDLL_FIND_EDGE_INDEX_FOR_NODE-LOOP-0 (I CDOBJ NINDEX)
  (DECLARE (XARGS :MEASURE (NFIX (- (CDLL_MAX_NODE1) I))))
  (IF (AND (INTEGERP I)
           (INTEGERP (CDLL_MAX_NODE1))
           (AND (< I (CDLL_MAX_NODE1))
                (OR (EQL (AG 'ALLOC (AG I (AG 'NODEARR CDOBJ)))
                         2)
                    (AND (NOT (EQL (AG 'PREV (AG I (AG 'NODEARR CDOBJ)))
                                   NINDEX))
                         (NOT (EQL (AG 'NEXT (AG I (AG 'NODEARR CDOBJ)))
                                   NINDEX))))))
      (CDLL_FIND_EDGE_INDEX_FOR_NODE-LOOP-0 (+ I 1)
                                            CDOBJ NINDEX)
    I))

(DEFUND CDLL_FIND_EDGE_INDEX_FOR_NODE (NINDEX CDOBJ)
  (LET ((I 0))
    (CDLL_FIND_EDGE_INDEX_FOR_NODE-LOOP-0 0 CDOBJ NINDEX)))

(DEFUND CDLL_FIND_FREE_NODE-LOOP-0 (I ARR)
  (DECLARE (XARGS :MEASURE (NFIX (- (CDLL_MAX_NODE1) I))))
  (IF (AND (INTEGERP I)
           (INTEGERP (CDLL_MAX_NODE1))
           (AND (< I (CDLL_MAX_NODE1))
                (NOT (EQL (AG 'ALLOC (AG I ARR)) 2))))
      (CDLL_FIND_FREE_NODE-LOOP-0 (+ I 1) ARR)
    I))

(DEFUND CDLL_FIND_FREE_NODE (NDCOUNT ARR)
  (IF1 (LOG= NDCOUNT (CDLL_MAX_NODE1))
       (CDLL_MAX_NODE1)
       (LET ((I 0))
         (CDLL_FIND_FREE_NODE-LOOP-0 0 ARR))))

(DEFUND CDLL_ADD_NODE_AT_INDEX (INDEX V CDOBJ)
  (IF1 (LOGAND1 (LOG<> (AG 'NODECOUNT CDOBJ)
                       (CDLL_MAX_NODE1))
                (LOG<> (SI V 64)
                       (* (* -2 2147483648) 2147483648)))
       (LET* ((CDOBJ (AS 'NODEARR
                         (AS INDEX
                             (AS 'ALLOC
                                 (BITS 3 1 0)
                                 (AG INDEX (AG 'NODEARR CDOBJ)))
                             (AG 'NODEARR CDOBJ))
                         CDOBJ))
              (CDOBJ (AS 'NODECOUNT
                         (+ (AG 'NODECOUNT CDOBJ) 1)
                         CDOBJ))
              (CDOBJ (AS 'NODEARR
                         (AS INDEX
                             (AS 'PREV
                                 INDEX (AG INDEX (AG 'NODEARR CDOBJ)))
                             (AG 'NODEARR CDOBJ))
                         CDOBJ))
              (CDOBJ (AS 'NODEARR
                         (AS INDEX
                             (AS 'NEXT
                                 INDEX (AG INDEX (AG 'NODEARR CDOBJ)))
                             (AG 'NODEARR CDOBJ))
                         CDOBJ)))
         (AS 'NODEARR
             (AS INDEX
                 (AS 'VAL
                     V (AG INDEX (AG 'NODEARR CDOBJ)))
                 (AG 'NODEARR CDOBJ))
             CDOBJ))
       CDOBJ))

(DEFUND CDLL_ADD_NODE (V CDOBJ)
  (IF1 (LOGAND1 (LOG<> (AG 'NODECOUNT CDOBJ)
                       (CDLL_MAX_NODE1))
                (LOG<> (SI V 64)
                       (* (* -2 2147483648) 2147483648)))
       (LET ((INDEX (CDLL_FIND_FREE_NODE (AG 'NODECOUNT CDOBJ)
                                         (AG 'NODEARR CDOBJ))))
         (IF1 (LOG< INDEX (CDLL_MAX_NODE1))
              (LET* ((CDOBJ (AS 'NODEARR
                                (AS INDEX
                                    (AS 'ALLOC
                                        (BITS 3 1 0)
                                        (AG INDEX (AG 'NODEARR CDOBJ)))
                                    (AG 'NODEARR CDOBJ))
                                CDOBJ))
                     (CDOBJ (AS 'NODECOUNT
                                (+ (AG 'NODECOUNT CDOBJ) 1)
                                CDOBJ))
                     (CDOBJ (AS 'NODEARR
                                (AS INDEX
                                    (AS 'PREV
                                        INDEX (AG INDEX (AG 'NODEARR CDOBJ)))
                                    (AG 'NODEARR CDOBJ))
                                CDOBJ))
                     (CDOBJ (AS 'NODEARR
                                (AS INDEX
                                    (AS 'NEXT
                                        INDEX (AG INDEX (AG 'NODEARR CDOBJ)))
                                    (AG 'NODEARR CDOBJ))
                                CDOBJ)))
                (AS 'NODEARR
                    (AS INDEX
                        (AS 'VAL
                            V (AG INDEX (AG 'NODEARR CDOBJ)))
                        (AG 'NODEARR CDOBJ))
                    CDOBJ))
              CDOBJ))
       CDOBJ))

(DEFUND CDLL_DELETE_NODE_REFS_FROM_EDGES-LOOP-0 (N NDEL CDOBJ)
  (DECLARE (XARGS :MEASURE (NFIX (- N 0))))
  (IF (AND (INTEGERP N) (> N 0))
      (LET* ((CDOBJ (IF1 (LOG= (AG 'PREV
                                   (AG (- N 1) (AG 'NODEARR CDOBJ)))
                               NDEL)
                         (AS 'NODEARR
                             (AS (- N 1)
                                 (AS 'PREV
                                     (- N 1)
                                     (AG (- N 1) (AG 'NODEARR CDOBJ)))
                                 (AG 'NODEARR CDOBJ))
                             CDOBJ)
                         CDOBJ))
             (CDOBJ (IF1 (LOG= (AG 'NEXT
                                   (AG (- N 1) (AG 'NODEARR CDOBJ)))
                               NDEL)
                         (AS 'NODEARR
                             (AS (- N 1)
                                 (AS 'NEXT
                                     (- N 1)
                                     (AG (- N 1) (AG 'NODEARR CDOBJ)))
                                 (AG 'NODEARR CDOBJ))
                             CDOBJ)
                         CDOBJ)))
        (CDLL_DELETE_NODE_REFS_FROM_EDGES-LOOP-0 (- N 1)
                                                 NDEL CDOBJ))
    CDOBJ))

(DEFUND CDLL_DELETE_NODE_REFS_FROM_EDGES (NDEL CDOBJ)
  (CDLL_DELETE_NODE_REFS_FROM_EDGES-LOOP-0 (CDLL_MAX_NODE1)
                                           NDEL CDOBJ))

(DEFUND CDLL_DELETE_NODE (N CDOBJ)
  (LET* ((CDOBJ (IF1 (LOG> (AG 'NODECOUNT CDOBJ) 0)
                     (AS 'NODECOUNT
                         (- (AG 'NODECOUNT CDOBJ) 1)
                         CDOBJ)
                     CDOBJ))
         (LINDEX (AG 'PREV (AG N (AG 'NODEARR CDOBJ))))
         (RINDEX (AG 'NEXT (AG N (AG 'NODEARR CDOBJ))))
         (CDOBJ (AS 'NODEARR
                    (AS N
                        (AS 'ALLOC
                            (BITS 2 1 0)
                            (AG N (AG 'NODEARR CDOBJ)))
                        (AG 'NODEARR CDOBJ))
                    CDOBJ))
         (CDOBJ (IF1 (LOG= (AG 'NEXT
                               (AG LINDEX (AG 'NODEARR CDOBJ)))
                           N)
                     (IF1 (LOG= RINDEX N)
                          (AS 'NODEARR
                              (AS LINDEX
                                  (AS 'NEXT
                                      LINDEX (AG LINDEX (AG 'NODEARR CDOBJ)))
                                  (AG 'NODEARR CDOBJ))
                              CDOBJ)
                          (AS 'NODEARR
                              (AS LINDEX
                                  (AS 'NEXT
                                      RINDEX (AG LINDEX (AG 'NODEARR CDOBJ)))
                                  (AG 'NODEARR CDOBJ))
                              CDOBJ))
                     CDOBJ)))
    (IF1 (LOG= (AG 'PREV
                   (AG RINDEX (AG 'NODEARR CDOBJ)))
               N)
         (IF1 (LOG= LINDEX N)
              (AS 'NODEARR
                  (AS RINDEX
                      (AS 'PREV
                          RINDEX (AG RINDEX (AG 'NODEARR CDOBJ)))
                      (AG 'NODEARR CDOBJ))
                  CDOBJ)
              (AS 'NODEARR
                  (AS RINDEX
                      (AS 'PREV
                          LINDEX (AG RINDEX (AG 'NODEARR CDOBJ)))
                      (AG 'NODEARR CDOBJ))
                  CDOBJ))
         CDOBJ)))

(DEFUND CDLL_DELETE_NODE_EDGE_SCRUB (N CDOBJ)
  (LET* ((CDOBJ (IF1 (LOG> (AG 'NODECOUNT CDOBJ) 0)
                     (AS 'NODECOUNT
                         (- (AG 'NODECOUNT CDOBJ) 1)
                         CDOBJ)
                     CDOBJ))
         (CDOBJ (AS 'NODEARR
                    (AS N
                        (AS 'ALLOC
                            (BITS 2 1 0)
                            (AG N (AG 'NODEARR CDOBJ)))
                        (AG 'NODEARR CDOBJ))
                    CDOBJ)))
    (CDLL_DELETE_NODE_REFS_FROM_EDGES N CDOBJ)))

(DEFUND CDLL_CHANGE_EDGE_TARGET (N EDGENUM NNEW CDOBJ)
  (IF1 (LOG< N (CDLL_MAX_NODE1))
       (IF1 (LOG= EDGENUM 0)
            (AS 'NODEARR
                (AS N
                    (AS 'NEXT
                        NNEW (AG N (AG 'NODEARR CDOBJ)))
                    (AG 'NODEARR CDOBJ))
                CDOBJ)
            (AS 'NODEARR
                (AS N
                    (AS 'PREV
                        NNEW (AG N (AG 'NODEARR CDOBJ)))
                    (AG 'NODEARR CDOBJ))
                CDOBJ))
       CDOBJ))

(DEFUND CDLL_NTHNODEBY-LOOP-0 (I N EDGENUM ARR INDEX)
  (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
  (IF (AND (INTEGERP I)
           (AND (> I 0)
                (< INDEX (CDLL_MAX_NODE1))))
      (LET ((INDEX (IF1 (LOG<> (AG 'ALLOC (AG INDEX ARR)) 3)
                        (CDLL_MAX_NODE1)
                        (IF1 (LOG= EDGENUM 0)
                             (AG 'NEXT (AG INDEX ARR))
                             (AG 'PREV (AG INDEX ARR))))))
        (CDLL_NTHNODEBY-LOOP-0 (- I 1)
                               N EDGENUM ARR INDEX))
    INDEX))

(DEFUND CDLL_NTHNODEBY (N EDGENUM INDEX ARR)
  (LET ((INDEX (CDLL_NTHNODEBY-LOOP-0 N N EDGENUM ARR INDEX)))
    (IF1 (LOGAND1 (LOG< INDEX (CDLL_MAX_NODE1))
                  (LOG= (AG 'ALLOC (AG INDEX ARR)) 3))
         INDEX (CDLL_MAX_NODE1))))

(DEFUND CDLL_FINDNODEBY-LOOP-0 (I DATUM EDGENUM CDOBJ INDEX)
  (DECLARE (XARGS :MEASURE (NFIX (- (CDLL_MAX_NODE1) I))))
  (IF (AND (INTEGERP I)
           (INTEGERP (CDLL_MAX_NODE1))
           (AND (< I (CDLL_MAX_NODE1))
                (NOT (EQL (SI (AG 'VAL (AG INDEX (AG 'NODEARR CDOBJ)))
                              64)
                          (SI DATUM 64)))))
      (LET ((INDEX (IF1 (LOG= EDGENUM 0)
                        (AG 'NEXT
                            (AG INDEX (AG 'NODEARR CDOBJ)))
                        (AG 'PREV
                            (AG INDEX (AG 'NODEARR CDOBJ))))))
        (CDLL_FINDNODEBY-LOOP-0 (+ I 1)
                                DATUM EDGENUM CDOBJ INDEX))
    (MV I INDEX)))

(DEFUND CDLL_FINDNODEBY (EDGENUM DATUM INDEX CDOBJ)
  (IF1 (LOG= (SI DATUM 64)
             (* (* -2 2147483648) 2147483648))
       (CDLL_MAX_NODE1)
       (LET ((I 0))
         (MV-LET (I INDEX)
                 (CDLL_FINDNODEBY-LOOP-0 0 DATUM EDGENUM CDOBJ INDEX)
           (IF1 (LOG= I (CDLL_MAX_NODE1))
                (CDLL_MAX_NODE1)
                INDEX)))))

(DEFUND CDLL_DEPTHOF-LOOP-0 (I DATUM CDOBJ INDEX)
  (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
  (IF (AND (INTEGERP I)
           (AND (> I 0)
                (NOT (EQL (SI (AG 'VAL (AG INDEX (AG 'NODEARR CDOBJ)))
                              64)
                          (SI DATUM 64)))))
      (LET ((INDEX (AG 'NEXT
                       (AG INDEX (AG 'NODEARR CDOBJ)))))
        (CDLL_DEPTHOF-LOOP-0 (- I 1)
                             DATUM CDOBJ INDEX))
    (MV I INDEX)))

(DEFUND CDLL_DEPTHOF-LOOP-1 (I DATUM CDOBJ INDEX)
  (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
  (IF (AND (INTEGERP I)
           (AND (> I 0)
                (NOT (EQL (SI (AG 'VAL (AG INDEX (AG 'NODEARR CDOBJ)))
                              64)
                          (SI DATUM 64)))))
      (LET ((INDEX (AG 'PREV
                       (AG INDEX (AG 'NODEARR CDOBJ)))))
        (CDLL_DEPTHOF-LOOP-1 (- I 1)
                             DATUM CDOBJ INDEX))
    (MV I INDEX)))

(DEFUND CDLL_DEPTHOF (EDGENUM DATUM INDEX CDOBJ)
  (IF1 (LOG= (SI DATUM 64)
             (* (* -2 2147483648) 2147483648))
       (CDLL_MAX_NODE1)
       (LET ((I (+ (AG 'NODECOUNT CDOBJ) 1)))
         (IF1 (LOG= EDGENUM 0)
              (MV-LET (I INDEX)
                      (CDLL_DEPTHOF-LOOP-0 (+ (AG 'NODECOUNT CDOBJ) 1)
                                           DATUM CDOBJ INDEX)
                (- (AG 'NODECOUNT CDOBJ) I))
              (MV-LET (I INDEX)
                      (CDLL_DEPTHOF-LOOP-1 (+ (AG 'NODECOUNT CDOBJ) 1)
                                           DATUM CDOBJ INDEX)
                (- (AG 'NODECOUNT CDOBJ) I))))))

(DEFUND CDLL_HD (CDOBJ)
  (IF1 (LOG= (AG 'NODECOUNT CDOBJ) 0)
       (BITS (* (* -2 2147483648) 2147483648)
             63 0)
       (AG 'VAL
           (AG (AG 'NODEHD CDOBJ)
               (AG 'NODEARR CDOBJ)))))

(DEFUND CDLL_TL (CDOBJ)
  (IF1 (LOG= (AG 'NODECOUNT CDOBJ) 0)
       (BITS (* (* -2 2147483648) 2147483648)
             63 0)
       (AG 'VAL
           (AG (AG 'PREV
                   (AG (AG 'NODEHD CDOBJ)
                       (AG 'NODEARR CDOBJ)))
               (AG 'NODEARR CDOBJ)))))

(DEFUND CDLL_NTH (J CDOBJ)
  (IF1 (LOGIOR1 (LOG= (AG 'NODECOUNT CDOBJ) 0)
                (LOG>= J (AG 'NODECOUNT CDOBJ)))
       (BITS (* (* -2 2147483648) 2147483648)
             63 0)
       (IF1 (LOG= J 0)
            (AG 'VAL
                (AG (AG 'NODEHD CDOBJ)
                    (AG 'NODEARR CDOBJ)))
            (LET ((JTHNODE (CDLL_NTHNODEBY J (BITS 0 0 0)
                                           (AG 'NODEHD CDOBJ)
                                           (AG 'NODEARR CDOBJ))))
              (IF1 (LOG= JTHNODE (CDLL_MAX_NODE1))
                   (BITS (* (* -2 2147483648) 2147483648)
                         63 0)
                   (AG 'VAL
                       (AG JTHNODE (AG 'NODEARR CDOBJ))))))))

(DEFUND CDLL_NTH_PREV (J CDOBJ)
  (IF1 (LOGIOR1 (LOG= (AG 'NODECOUNT CDOBJ) 0)
                (LOG>= J (AG 'NODECOUNT CDOBJ)))
       (BITS (* (* -2 2147483648) 2147483648)
             63 0)
       (IF1 (LOG= J 0)
            (AG 'VAL
                (AG (AG 'NODEHD CDOBJ)
                    (AG 'NODEARR CDOBJ)))
            (LET ((JTHNODE (CDLL_NTHNODEBY J (BITS 1 0 0)
                                           (AG 'NODEHD CDOBJ)
                                           (AG 'NODEARR CDOBJ))))
              (IF1 (LOG= JTHNODE (CDLL_MAX_NODE1))
                   (BITS (* (* -2 2147483648) 2147483648)
                         63 0)
                   (AG 'VAL
                       (AG JTHNODE (AG 'NODEARR CDOBJ))))))))

(DEFUND CDLL_LN (CDOBJ)
  (AG 'NODECOUNT CDOBJ))

(DEFUND CDLL_LN_COUNT-LOOP-0 (I CDOBJ LNC ND)
  (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
  (IF (AND (INTEGERP I)
           (AND (> I 0)
                (NOT (EQL ND (AG 'NODEHD CDOBJ)))))
      (LET ((LNC (BITS (+ (SI LNC 64) 1) 63 0))
            (ND (AG 'NEXT (AG ND (AG 'NODEARR CDOBJ)))))
        (CDLL_LN_COUNT-LOOP-0 (- I 1)
                              CDOBJ LNC ND))
    (MV I LNC ND)))

(DEFUND CDLL_LN_COUNT (CDOBJ)
  (LET ((LNC (BITS 0 63 0))
        (ND (AG 'NODEHD CDOBJ)))
    (IF1 (LOG= ND
               (AG 'NEXT (AG ND (AG 'NODEARR CDOBJ))))
         LNC
         (LET ((LNC (BITS (+ (SI LNC 64) 1) 63 0))
               (ND (AG 'NEXT (AG ND (AG 'NODEARR CDOBJ))))
               (I (CDLL_MAX_NODE1)))
           (MV-LET (I LNC ND)
                   (CDLL_LN_COUNT-LOOP-0 (CDLL_MAX_NODE1)
                                         CDOBJ LNC ND)
             (IF1 (LOG= I 0) (BITS -1 63 0) LNC))))))

(DEFUND CDLL_RST (CDOBJ)
 (LET ((HDINDEX (AG 'NODEHD CDOBJ)))
  (IF1
     (LOG= (AG 'NODECOUNT CDOBJ) 0)
     CDOBJ
     (LET ((CDOBJ (IF1 (LOG= (AG 'NODECOUNT CDOBJ) 1)
                       (AS 'NODEHD 0 CDOBJ)
                       (LET ((CDOBJ (AS 'NODEHD
                                        (AG 'NEXT
                                            (AG HDINDEX (AG 'NODEARR CDOBJ)))
                                        CDOBJ)))
                         (IF1 (LOG= (AG 'NODECOUNT CDOBJ) 2)
                              (LET ((CDOBJ (AS 'NODEARR
                                               (AS (AG 'NODEHD CDOBJ)
                                                   (AS 'PREV
                                                       (AG 'NODEHD CDOBJ)
                                                       (AG (AG 'NODEHD CDOBJ)
                                                           (AG 'NODEARR CDOBJ)))
                                                   (AG 'NODEARR CDOBJ))
                                               CDOBJ)))
                                (AS 'NODEARR
                                    (AS (AG 'NODEHD CDOBJ)
                                        (AS 'NEXT
                                            (AG 'NODEHD CDOBJ)
                                            (AG (AG 'NODEHD CDOBJ)
                                                (AG 'NODEARR CDOBJ)))
                                        (AG 'NODEARR CDOBJ))
                                    CDOBJ))
                              (AS 'NODEARR
                                  (AS (AG 'NODEHD CDOBJ)
                                      (AS 'PREV
                                          (AG 'PREV
                                              (AG HDINDEX (AG 'NODEARR CDOBJ)))
                                          (AG (AG 'NODEHD CDOBJ)
                                              (AG 'NODEARR CDOBJ)))
                                      (AG 'NODEARR CDOBJ))
                                  CDOBJ))))))
       (CDLL_DELETE_NODE HDINDEX CDOBJ)))))

(DEFUND CDLL_TSR (CDOBJ)
 (LET ((TLINDEX (AG 'PREV
                    (AG (AG 'NODEHD CDOBJ)
                        (AG 'NODEARR CDOBJ)))))
  (IF1 (LOG= (AG 'NODECOUNT CDOBJ) 0)
       CDOBJ
       (LET ((CDOBJ (IF1 (LOG= (AG 'NODECOUNT CDOBJ) 1)
                         (AS 'NODEHD 0 CDOBJ)
                         (IF1 (LOG= (AG 'NODECOUNT CDOBJ) 2)
                              (LET ((CDOBJ (AS 'NODEARR
                                               (AS (AG 'NODEHD CDOBJ)
                                                   (AS 'PREV
                                                       (AG 'NODEHD CDOBJ)
                                                       (AG (AG 'NODEHD CDOBJ)
                                                           (AG 'NODEARR CDOBJ)))
                                                   (AG 'NODEARR CDOBJ))
                                               CDOBJ)))
                                (AS 'NODEARR
                                    (AS (AG 'NODEHD CDOBJ)
                                        (AS 'NEXT
                                            (AG 'NODEHD CDOBJ)
                                            (AG (AG 'NODEHD CDOBJ)
                                                (AG 'NODEARR CDOBJ)))
                                        (AG 'NODEARR CDOBJ))
                                    CDOBJ))
                              (AS 'NODEARR
                                  (AS (AG 'NODEHD CDOBJ)
                                      (AS 'PREV
                                          (AG 'PREV
                                              (AG TLINDEX (AG 'NODEARR CDOBJ)))
                                          (AG (AG 'NODEHD CDOBJ)
                                              (AG 'NODEARR CDOBJ)))
                                      (AG 'NODEARR CDOBJ))
                                  CDOBJ)))))
         (CDLL_DELETE_NODE TLINDEX CDOBJ)))))

(DEFUND CDLL_CNS (V CDOBJ)
 (IF1
  (LOGIOR1 (LOG= (AG 'NODECOUNT CDOBJ)
                 (CDLL_MAX_NODE1))
           (LOG= (SI V 64)
                 (* (* -2 2147483648) 2147483648)))
  CDOBJ
  (LET ((INDEX (CDLL_FIND_FREE_NODE (AG 'NODECOUNT CDOBJ)
                                    (AG 'NODEARR CDOBJ))))
   (IF1
    (LOG> INDEX (CDLL_MAX_NODE))
    CDOBJ
    (IF1
      (LOGAND1 (LOG> (AG 'NODECOUNT CDOBJ) 0)
               (LOGIOR1 (LOG> (AG 'NODEHD CDOBJ)
                              (CDLL_MAX_NODE))
                        (LOG<> (AG 'ALLOC
                                   (AG (AG 'NODEHD CDOBJ)
                                       (AG 'NODEARR CDOBJ)))
                               3)))
      CDOBJ
      (LET*
       ((CDOBJ
             (IF1 (LOG> (AG 'NODECOUNT CDOBJ) 0)
                  (LET* ((TL (AG 'PREV
                                 (AG (AG 'NODEHD CDOBJ)
                                     (AG 'NODEARR CDOBJ))))
                         (CDOBJ (AS 'NODEARR
                                    (AS TL
                                        (AS 'NEXT
                                            INDEX (AG TL (AG 'NODEARR CDOBJ)))
                                        (AG 'NODEARR CDOBJ))
                                    CDOBJ))
                         (CDOBJ (AS 'NODEARR
                                    (AS INDEX
                                        (AS 'NEXT
                                            (AG 'NODEHD CDOBJ)
                                            (AG INDEX (AG 'NODEARR CDOBJ)))
                                        (AG 'NODEARR CDOBJ))
                                    CDOBJ))
                         (CDOBJ (AS 'NODEARR
                                    (AS (AG 'NODEHD CDOBJ)
                                        (AS 'PREV
                                            INDEX
                                            (AG (AG 'NODEHD CDOBJ)
                                                (AG 'NODEARR CDOBJ)))
                                        (AG 'NODEARR CDOBJ))
                                    CDOBJ)))
                    (AS 'NODEARR
                        (AS INDEX
                            (AS 'PREV
                                TL (AG INDEX (AG 'NODEARR CDOBJ)))
                            (AG 'NODEARR CDOBJ))
                        CDOBJ))
                  (LET ((CDOBJ (AS 'NODEARR
                                   (AS INDEX
                                       (AS 'PREV
                                           INDEX (AG INDEX (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ)))
                    (AS 'NODEARR
                        (AS INDEX
                            (AS 'NEXT
                                INDEX (AG INDEX (AG 'NODEARR CDOBJ)))
                            (AG 'NODEARR CDOBJ))
                        CDOBJ))))
        (CDOBJ (AS 'NODEHD INDEX CDOBJ))
        (CDOBJ (AS 'NODEARR
                   (AS INDEX
                       (AS 'ALLOC
                           (BITS 3 1 0)
                           (AG INDEX (AG 'NODEARR CDOBJ)))
                       (AG 'NODEARR CDOBJ))
                   CDOBJ))
        (CDOBJ (AS 'NODECOUNT
                   (+ (AG 'NODECOUNT CDOBJ) 1)
                   CDOBJ)))
       (AS 'NODEARR
           (AS INDEX
               (AS 'VAL
                   V (AG INDEX (AG 'NODEARR CDOBJ)))
               (AG 'NODEARR CDOBJ))
           CDOBJ)))))))

(DEFUND CDLL_CNS1 (V CDOBJ)
  (IF1 (LOGIOR1 (LOG= (AG 'NODECOUNT CDOBJ) 0)
                (LOGIOR1 (LOG= (AG 'NODECOUNT CDOBJ)
                               (CDLL_MAX_NODE1))
                         (LOG= (SI V 64)
                               (* (* -2 2147483648) 2147483648))))
       CDOBJ
       (LET ((INDEX (CDLL_FIND_FREE_NODE (AG 'NODECOUNT CDOBJ)
                                         (AG 'NODEARR CDOBJ))))
         (IF1 (LOG> INDEX (CDLL_MAX_NODE))
              CDOBJ
              (IF1 (LOGIOR1 (LOG> (AG 'NODEHD CDOBJ)
                                  (CDLL_MAX_NODE))
                            (LOG<> (AG 'ALLOC
                                       (AG (AG 'NODEHD CDOBJ)
                                           (AG 'NODEARR CDOBJ)))
                                   3))
                   CDOBJ
                   (LET* ((CDOBJ (AS 'NODEARR
                                     (AS INDEX
                                         (AS 'NEXT
                                             (AG 'NEXT
                                                 (AG (AG 'NODEHD CDOBJ)
                                                     (AG 'NODEARR CDOBJ)))
                                             (AG INDEX (AG 'NODEARR CDOBJ)))
                                         (AG 'NODEARR CDOBJ))
                                     CDOBJ))
                          (CDOBJ (AS 'NODEARR
                                     (AS INDEX
                                         (AS 'PREV
                                             (AG 'NODEHD CDOBJ)
                                             (AG INDEX (AG 'NODEARR CDOBJ)))
                                         (AG 'NODEARR CDOBJ))
                                     CDOBJ))
                          (CDOBJ (AS 'NODECOUNT
                                     (+ (AG 'NODECOUNT CDOBJ) 1)
                                     CDOBJ))
                          (CDOBJ (AS 'NODEARR
                                     (AS INDEX
                                         (AS 'VAL
                                             V (AG INDEX (AG 'NODEARR CDOBJ)))
                                         (AG 'NODEARR CDOBJ))
                                     CDOBJ))
                          (CDOBJ (AS 'NODEARR
                                     (AS INDEX
                                         (AS 'ALLOC
                                             (BITS 3 1 0)
                                             (AG INDEX (AG 'NODEARR CDOBJ)))
                                         (AG 'NODEARR CDOBJ))
                                     CDOBJ))
                          (CDOBJ (AS 'NODEARR
                                     (AS (AG 'NEXT
                                             (AG (AG 'NODEHD CDOBJ)
                                                 (AG 'NODEARR CDOBJ)))
                                         (AS 'PREV
                                             INDEX
                                             (AG (AG 'NEXT
                                                     (AG (AG 'NODEHD CDOBJ)
                                                         (AG 'NODEARR CDOBJ)))
                                                 (AG 'NODEARR CDOBJ)))
                                         (AG 'NODEARR CDOBJ))
                                     CDOBJ)))
                     (AS 'NODEARR
                         (AS (AG 'NODEHD CDOBJ)
                             (AS 'NEXT
                                 INDEX
                                 (AG (AG 'NODEHD CDOBJ)
                                     (AG 'NODEARR CDOBJ)))
                             (AG 'NODEARR CDOBJ))
                         CDOBJ)))))))

(DEFUND CDLL_SNC (V CDOBJ)
 (IF1
  (LOGIOR1 (LOG= (AG 'NODECOUNT CDOBJ)
                 (CDLL_MAX_NODE1))
           (LOG= (SI V 64)
                 (* (* -2 2147483648) 2147483648)))
  CDOBJ
  (LET ((INDEX (CDLL_FIND_FREE_NODE (AG 'NODECOUNT CDOBJ)
                                    (AG 'NODEARR CDOBJ))))
   (IF1
    (LOG> INDEX (CDLL_MAX_NODE))
    CDOBJ
    (IF1
     (LOGAND1 (LOG> (AG 'NODECOUNT CDOBJ) 0)
              (LOGIOR1 (LOG> (AG 'NODEHD CDOBJ)
                             (CDLL_MAX_NODE))
                       (LOG<> (AG 'ALLOC
                                  (AG (AG 'NODEHD CDOBJ)
                                      (AG 'NODEARR CDOBJ)))
                              3)))
     CDOBJ
     (LET*
      ((CDOBJ
            (IF1 (LOG> (AG 'NODECOUNT CDOBJ) 0)
                 (LET* ((TL (AG 'PREV
                                (AG (AG 'NODEHD CDOBJ)
                                    (AG 'NODEARR CDOBJ))))
                        (CDOBJ (AS 'NODEARR
                                   (AS TL
                                       (AS 'NEXT
                                           INDEX (AG TL (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ))
                        (CDOBJ (AS 'NODEARR
                                   (AS INDEX
                                       (AS 'PREV
                                           TL (AG INDEX (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ))
                        (CDOBJ (AS 'NODEARR
                                   (AS INDEX
                                       (AS 'NEXT
                                           (AG 'NODEHD CDOBJ)
                                           (AG INDEX (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ)))
                   (AS 'NODEARR
                       (AS (AG 'NODEHD CDOBJ)
                           (AS 'PREV
                               INDEX
                               (AG (AG 'NODEHD CDOBJ)
                                   (AG 'NODEARR CDOBJ)))
                           (AG 'NODEARR CDOBJ))
                       CDOBJ))
                 (LET* ((CDOBJ (AS 'NODEARR
                                   (AS INDEX
                                       (AS 'PREV
                                           INDEX (AG INDEX (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ))
                        (CDOBJ (AS 'NODEARR
                                   (AS INDEX
                                       (AS 'NEXT
                                           INDEX (AG INDEX (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ)))
                   (AS 'NODEHD INDEX CDOBJ))))
       (CDOBJ (AS 'NODEARR
                  (AS INDEX
                      (AS 'ALLOC
                          (BITS 3 1 0)
                          (AG INDEX (AG 'NODEARR CDOBJ)))
                      (AG 'NODEARR CDOBJ))
                  CDOBJ))
       (CDOBJ (AS 'NODECOUNT
                  (+ (AG 'NODECOUNT CDOBJ) 1)
                  CDOBJ)))
      (AS 'NODEARR
          (AS INDEX
              (AS 'VAL
                  V (AG INDEX (AG 'NODEARR CDOBJ)))
              (AG 'NODEARR CDOBJ))
          CDOBJ)))))))

(DEFUND CDLL_INS (J V CDOBJ)
  (IF1 (LOGIOR1 (LOG>= J (AG 'NODECOUNT CDOBJ))
                (LOGIOR1 (LOG= (AG 'NODECOUNT CDOBJ)
                               (CDLL_MAX_NODE1))
                         (LOG= (SI V 64)
                               (* (* -2 2147483648) 2147483648))))
       CDOBJ
       (IF1 (LOG>= J (AG 'NODECOUNT CDOBJ))
            CDOBJ
            (IF1 (LOG= (AG 'NODECOUNT CDOBJ) 0)
                 CDOBJ
                 (LET ((JTHNODE (CDLL_NTHNODEBY J (BITS 0 0 0)
                                                (AG 'NODEHD CDOBJ)
                                                (AG 'NODEARR CDOBJ))))
                   (IF1 (LOG= JTHNODE (CDLL_MAX_NODE1))
                        CDOBJ
                        (LET* ((PREVHD (AG 'NODEHD CDOBJ))
                               (CDOBJ (AS 'NODEHD JTHNODE CDOBJ))
                               (CDOBJ (CDLL_CNS1 V CDOBJ)))
                          (AS 'NODEHD PREVHD CDOBJ))))))))

(DEFUND CDLL_DEL (J CDOBJ)
  (IF1 (LOGIOR1 (LOG> J (AG 'NODECOUNT CDOBJ))
                (LOG= (AG 'NODECOUNT CDOBJ) 0))
       CDOBJ
       (IF1 (LOG= J 0)
            (CDLL_RST CDOBJ)
            (IF1 (LOGAND1 (LOG> J 0)
                          (LOG= J (AG 'NODECOUNT CDOBJ)))
                 (CDLL_TSR CDOBJ)
                 (LET ((JTHNODE (CDLL_NTHNODEBY J (BITS 0 0 0)
                                                (AG 'NODEHD CDOBJ)
                                                (AG 'NODEARR CDOBJ))))
                   (IF1 (LOG= JTHNODE (CDLL_MAX_NODE))
                        CDOBJ
                        (IF1 (LOG<> (AG 'ALLOC
                                        (AG JTHNODE (AG 'NODEARR CDOBJ)))
                                    3)
                             CDOBJ
                             (LET* ((PREVHD (AG 'NODEHD CDOBJ))
                                    (CDOBJ (AS 'NODEHD JTHNODE CDOBJ))
                                    (CDOBJ (CDLL_RST CDOBJ)))
                               (AS 'NODEHD PREVHD CDOBJ)))))))))

(DEFUND CDLL_REMOVE (N CDOBJ)
  (IF1 (LOG> N (CDLL_MAX_NODE))
       CDOBJ
       (IF1 (LOG= N (AG 'NODEHD CDOBJ))
            CDOBJ
            (IF1 (LOG< (AG 'NODECOUNT CDOBJ) 3)
                 CDOBJ
                 (LET* ((NEXTNODE (AG 'NEXT (AG N (AG 'NODEARR CDOBJ))))
                        (PREVNODE (AG 'PREV (AG N (AG 'NODEARR CDOBJ))))
                        (CDOBJ (AS 'NODEARR
                                   (AS PREVNODE
                                       (AS 'NEXT
                                           NEXTNODE
                                           (AG PREVNODE (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ))
                        (CDOBJ (AS 'NODEARR
                                   (AS NEXTNODE
                                       (AS 'PREV
                                           PREVNODE
                                           (AG NEXTNODE (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ)))
                   (AS 'NODECOUNT
                       (- (AG 'NODECOUNT CDOBJ) 1)
                       CDOBJ))))))

(DEFUND CDLL_RESTORE (N CDOBJ)
  (IF1 (LOG> N (CDLL_MAX_NODE))
       CDOBJ
       (IF1 (LOG= N (AG 'NODEHD CDOBJ))
            CDOBJ
            (IF1 (LOGIOR1 (LOG< (AG 'NODECOUNT CDOBJ) 2)
                          (LOG= (AG 'NODECOUNT CDOBJ)
                                (CDLL_MAX_NODE1)))
                 CDOBJ
                 (LET* ((PREVNODE (AG 'PREV (AG N (AG 'NODEARR CDOBJ))))
                        (NEXTNODE (AG 'NEXT (AG N (AG 'NODEARR CDOBJ))))
                        (CDOBJ (AS 'NODEARR
                                   (AS PREVNODE
                                       (AS 'NEXT
                                           N (AG PREVNODE (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ))
                        (CDOBJ (AS 'NODEARR
                                   (AS NEXTNODE
                                       (AS 'PREV
                                           N (AG NEXTNODE (AG 'NODEARR CDOBJ)))
                                       (AG 'NODEARR CDOBJ))
                                   CDOBJ)))
                   (AS 'NODECOUNT
                       (+ (AG 'NODECOUNT CDOBJ) 1)
                       CDOBJ))))))

