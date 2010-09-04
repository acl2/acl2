(IN-PACKAGE "ACL2")

(LOCAL (DEFUN %%SUB1-INDUCTION (N)
              (IF (ZP N)
                  N (%%SUB1-INDUCTION (1- N)))))

(LOCAL (DEFUN %%AND-TREE-FN (ARGS LEN)
              (DECLARE (XARGS :MODE :PROGRAM))
              (IF (< LEN 20)
                  (CONS 'AND ARGS)
                  (LET* ((LEN2 (FLOOR LEN 2)))
                        (LIST 'AND
                              (%%AND-TREE-FN (TAKE LEN2 ARGS) LEN2)
                              (%%AND-TREE-FN (NTHCDR LEN2 ARGS)
                                             (- LEN LEN2)))))))

(LOCAL (DEFMACRO %%AND-TREE (&REST ARGS)
                 (%%AND-TREE-FN ARGS (LENGTH ARGS))))

(LOCAL (DEFTHEORY THEORY-0 (THEORY 'MINIMAL-THEORY)))

(LOCAL (DEFTHM G1-BODY-IS-%G1-BODY_S
               (EQUAL (IF (ZP X) X Y)
                      (COND ((ZP X) X)
                            ((< 0 (F1 X)) Y)
                            (T 23)))
               :HINTS (("Goal" :DO-NOT '(PREPROCESS)))
               :RULE-CLASSES NIL))

(DEFTHM G1-IS-%G1 (EQUAL (G1 X Y) (%G1 X Y))
        :HINTS (("Goal" :EXPAND ((:FREE (X Y) (%G1 X Y))
                                 (:FREE (X Y) (G1 X Y)))
                        :IN-THEORY (THEORY 'THEORY-0)
                        :DO-NOT '(PREPROCESS)
                        :USE G1-BODY-IS-%G1-BODY_S)))

(LOCAL (DEFTHEORY THEORY-1
                  (UNION-THEORIES '(G1-IS-%G1)
                                  (THEORY 'THEORY-0))))

(LOCAL (DEFUN %%G2 (X Y)
              (IF (CONSP X)
                  (%%G2 (CDR X) Y)
                  (%G1 X Y))))

(LOCAL (DEFTHM %%G2-IS-G2 (EQUAL (%%G2 X Y) (G2 X Y))
               :HINTS (("Goal" :IN-THEORY (UNION-THEORIES '((:INDUCTION %%G2))
                                                          (THEORY 'THEORY-1))
                               :DO-NOT '(PREPROCESS)
                               :EXPAND ((%%G2 X Y) (G2 X Y))
                               :INDUCT T))))

(DEFTHM G2-IS-%G2 (EQUAL (G2 X Y) (%G2 X Y))
        :HINTS (("Goal" :BY (:FUNCTIONAL-INSTANCE %%G2-IS-G2 (%%G2 %G2))
                        :DO-NOT '(PREPROCESS)
                        :EXPAND ((%G2 X Y)))))

(LOCAL (DEFTHEORY THEORY-2
                  (UNION-THEORIES '(G2-IS-%G2)
                                  (THEORY 'THEORY-1))))

(LOCAL (DEFUN %%P2 (N)
              (DECLARE (XARGS :NORMALIZE NIL))
              (%%AND-TREE (EQUAL (WIRE2 N) (%WIRE2 N))
                          (EQUAL (WIRE1 N) (%WIRE1 N))
                          (EQUAL (REG2 N) (%REG2 N))
                          (EQUAL (REG1 N) (%REG1 N)))))

(LOCAL
   (DEFTHM
        %%P2-PROPERTY
        (IMPLIES (%%P2 N)
                 (%%AND-TREE (EQUAL (WIRE2 N) (%WIRE2 N))
                             (EQUAL (WIRE1 N) (%WIRE1 N))
                             (EQUAL (REG2 N) (%REG2 N))
                             (EQUAL (REG1 N) (%REG1 N))))
        :HINTS (("Goal" :IN-THEORY (UNION-THEORIES '(%%P2)
                                                   (THEORY 'MINIMAL-THEORY))))))

(LOCAL
     (DEFTHEORY %%P2-IMPLIES-F-IS-%F-THEORY
                (UNION-THEORIES (SET-DIFFERENCE-THEORIES (CURRENT-THEORY :HERE)
                                                         (CURRENT-THEORY '%%P2))
                                (THEORY 'MINIMAL-THEORY))))

(LOCAL
  (ENCAPSULATE NIL
               (LOCAL (IN-THEORY (DISABLE %%P2-PROPERTY)))
               (LOCAL (DEFTHM REG1-IS-%REG1-BASE
                              (IMPLIES (ZP N)
                                       (EQUAL (REG1 N) (%REG1 N)))
                              :HINTS (("Goal" :EXPAND ((REG1 N) (%REG1 N))))))
               (LOCAL (DEFTHM REG2-IS-%REG2-BASE
                              (IMPLIES (ZP N)
                                       (EQUAL (REG2 N) (%REG2 N)))
                              :HINTS (("Goal" :EXPAND ((REG2 N) (%REG2 N))))))
               (LOCAL (DEFTHM WIRE1-IS-%WIRE1-BASE
                              (IMPLIES (ZP N)
                                       (EQUAL (WIRE1 N) (%WIRE1 N)))
                              :HINTS (("Goal" :EXPAND ((WIRE1 N) (%WIRE1 N))))))
               (LOCAL (DEFTHM WIRE2-IS-%WIRE2-BASE
                              (IMPLIES (ZP N)
                                       (EQUAL (WIRE2 N) (%WIRE2 N)))
                              :HINTS (("Goal" :EXPAND ((WIRE2 N) (%WIRE2 N))))))
               (DEFTHM %%P2-BASE (IMPLIES (ZP N) (%%P2 N))
                       :INSTRUCTIONS (:PROMOTE :X-DUMB (:S :NORMALIZE NIL)))))

(LOCAL
     (ENCAPSULATE
          NIL
          (LOCAL (IN-THEORY (DISABLE %%P2 %%P2-BASE)))
          (LOCAL (DEFLABEL %%INDUCTION-START))
          (LOCAL (DEFTHM REG1-IS-%REG1-INDUCTION_STEP
                         (IMPLIES (AND (NOT (ZP N)) (%%P2 (1- N)))
                                  (EQUAL (REG1 N) (%REG1 N)))
                         :INSTRUCTIONS (:PROMOTE (:DV 1)
                                                 :X-DUMB
                                                 :NX :X-DUMB
                                                 :TOP (:S :NORMALIZE NIL
                                                          :BACKCHAIN-LIMIT 1000
                                                          :EXPAND :LAMBDAS
                                                          :REPEAT 4))))
          (LOCAL (DEFTHM REG2-IS-%REG2-INDUCTION_STEP
                         (IMPLIES (AND (NOT (ZP N)) (%%P2 (1- N)))
                                  (EQUAL (REG2 N) (%REG2 N)))
                         :INSTRUCTIONS (:PROMOTE (:DV 1)
                                                 :X-DUMB
                                                 :NX :X-DUMB
                                                 :TOP (:S :NORMALIZE NIL
                                                          :BACKCHAIN-LIMIT 1000
                                                          :EXPAND :LAMBDAS
                                                          :REPEAT 4))))
          (LOCAL (DEFTHM WIRE1-IS-%WIRE1-INDUCTION_STEP
                         (IMPLIES (AND (NOT (ZP N)) (%%P2 (1- N)))
                                  (EQUAL (WIRE1 N) (%WIRE1 N)))
                         :INSTRUCTIONS (:PROMOTE (:DV 1)
                                                 :X-DUMB
                                                 :NX :X-DUMB
                                                 :TOP (:S :NORMALIZE NIL
                                                          :BACKCHAIN-LIMIT 1000
                                                          :EXPAND :LAMBDAS
                                                          :REPEAT 4))))
          (LOCAL (DEFTHM WIRE2-IS-%WIRE2-INDUCTION_STEP
                         (IMPLIES (AND (NOT (ZP N)) (%%P2 (1- N)))
                                  (EQUAL (WIRE2 N) (%WIRE2 N)))
                         :INSTRUCTIONS (:PROMOTE (:DV 1)
                                                 :X-DUMB
                                                 :NX :X-DUMB
                                                 :TOP (:S :NORMALIZE NIL
                                                          :BACKCHAIN-LIMIT 1000
                                                          :EXPAND :LAMBDAS
                                                          :REPEAT 4))))
          (DEFTHM %%P2-INDUCTION_STEP
                  (IMPLIES (AND (NOT (ZP N)) (%%P2 (1- N)))
                           (%%P2 N))
                  :INSTRUCTIONS (:PROMOTE :X-DUMB (:S :NORMALIZE NIL)))))

(LOCAL
 (DEFTHM
  %%P2-HOLDS (%%P2 N)
  :HINTS
  (("Goal" :INDUCT (%%SUB1-INDUCTION N)
           :DO-NOT '(PREPROCESS)
           :IN-THEORY (UNION-THEORIES '(%%P2-BASE %%P2-INDUCTION_STEP
                                                  (:INDUCTION %%SUB1-INDUCTION))
                                      (THEORY 'MINIMAL-THEORY))))))

(ENCAPSULATE
     NIL
     (LOCAL (IN-THEORY (UNION-THEORIES '(%%P2-HOLDS)
                                       (THEORY '%%P2-IMPLIES-F-IS-%F-THEORY))))
     (DEFTHM REG1-IS-%REG1 (EQUAL (REG1 N) (%REG1 N))
             :HINTS (("Goal" :DO-NOT '(PREPROCESS))))
     (DEFTHM REG2-IS-%REG2 (EQUAL (REG2 N) (%REG2 N))
             :HINTS (("Goal" :DO-NOT '(PREPROCESS))))
     (DEFTHM WIRE1-IS-%WIRE1
             (EQUAL (WIRE1 N) (%WIRE1 N))
             :HINTS (("Goal" :DO-NOT '(PREPROCESS))))
     (DEFTHM WIRE2-IS-%WIRE2
             (EQUAL (WIRE2 N) (%WIRE2 N))
             :HINTS (("Goal" :DO-NOT '(PREPROCESS)))))

(DEFTHEORY %-REMOVAL-THEORY
           (UNION-THEORIES '(G1-IS-%G1 G2-IS-%G2
                                       WIRE2-IS-%WIRE2 WIRE1-IS-%WIRE1
                                       REG2-IS-%REG2 REG1-IS-%REG1)
                           (THEORY 'MINIMAL-THEORY)))

