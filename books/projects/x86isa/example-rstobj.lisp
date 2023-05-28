(include-book "centaur/defrstobj2/defrstobj" :dir :system)
(include-book "centaur/bigmem/bigmem" :dir :system)

(skip-proofs (rstobj2::defrstobj example-rstobj
                                 (mem   :type (array (unsigned-byte 8) ((expt 2 52))) ;; 2^52
                                        :initially 0
                                        :fix (acl2::loghead 8 (ifix x))
                                        :child-stobj bigmem::mem
                                        :child-accessor bigmem::read-mem
                                        :child-updater  bigmem::write-mem
                                        :accessor memi-internal
                                        :updater !memi-internal)
                                 :accessor xr
                                 :inline t))

;; (skip-proofs (rstobj2::defrstobj example-rstobj
;;                                  (mem   :type bigmem::mem
;;                                         :accessor mem
;;                                         :updater !mem)
;;                                  :inline t))

(skip-proofs (ENCAPSULATE NIL
                          (LOCAL (DEFLABEL EXAMPLE-RSTOBJ-START))
                          (DEFSTOBJ EXAMPLE-RSTOBJ$C
                                    (MEM$C :TYPE BIGMEM::MEM)
                                    :INLINE T
                                    :NON-MEMOIZABLE NIL)
                          (PROGN (DEFUN EXAMPLE-RSTOBJ-ELEM-P (RSTOBJ2::KEY X)
                                        (DECLARE (XARGS :GUARD T))
                                        (CASE RSTOBJ2::KEY
                                              (:MEM (BIGMEM::MEMP X))
                                              (OTHERWISE T)))
                                 (DEFTHM EXAMPLE-RSTOBJ-ELEM-P-OPENER
                                         (IMPLIES (SYNTAXP (QUOTEP K))
                                                  (EQUAL (EXAMPLE-RSTOBJ-ELEM-P K X)
                                                         (CASE K (:MEM NIL) (OTHERWISE T)))))
                                 (IN-THEORY (DISABLE EXAMPLE-RSTOBJ-ELEM-P))
                                 (DEFUN EXAMPLE-RSTOBJ-ELEM-P-TOP (RSTOBJ2::KEY X)
                                        (DECLARE (XARGS :GUARD T))
                                        (EXAMPLE-RSTOBJ-ELEM-P (EC-CALL (CAR RSTOBJ2::KEY))
                                                               X)))
                          (PROGN (DEFUN EXAMPLE-RSTOBJ-ELEM-FIX (RSTOBJ2::KEY X)
                                        (DECLARE (XARGS :GUARD T))
                                        (CASE RSTOBJ2::KEY
                                              (:MEM X)
                                              (OTHERWISE X)))
                                 (DEFTHM EXAMPLE-RSTOBJ-ELEM-FIX-OPENER
                                         (IMPLIES (SYNTAXP (QUOTEP K))
                                                  (EQUAL (EXAMPLE-RSTOBJ-ELEM-FIX K X)
                                                         (CASE K (:MEM X) (OTHERWISE X)))))
                                 (DEFTHM EXAMPLE-RSTOBJ-ELEM-P-OF-EXAMPLE-RSTOBJ-ELEM-FIX
                                         (EXAMPLE-RSTOBJ-ELEM-P K (EXAMPLE-RSTOBJ-ELEM-FIX K X))
                                         :HINTS ((AND STABLE-UNDER-SIMPLIFICATIONP
                                                      '(:IN-THEORY (ENABLE EXAMPLE-RSTOBJ-ELEM-P)))))
                                 (DEFTHM EXAMPLE-RSTOBJ-ELEM-FIX-WHEN-EXAMPLE-RSTOBJ-ELEM-P
                                         (IMPLIES (EXAMPLE-RSTOBJ-ELEM-P K X)
                                                  (EQUAL (EXAMPLE-RSTOBJ-ELEM-FIX K X) X))
                                         :HINTS ((AND STABLE-UNDER-SIMPLIFICATIONP
                                                      '(:IN-THEORY (ENABLE EXAMPLE-RSTOBJ-ELEM-P)))))
                                 (IN-THEORY (DISABLE EXAMPLE-RSTOBJ-ELEM-FIX))
                                 (DEFUN EXAMPLE-RSTOBJ-ELEM-FIX-TOP (RSTOBJ2::KEY X)
                                        (DECLARE (XARGS :GUARD T))
                                        (EXAMPLE-RSTOBJ-ELEM-FIX (EC-CALL (CAR RSTOBJ2::KEY))
                                                                 X)))
                          (PROGN (DEFUN EXAMPLE-RSTOBJ-ELEM-DEFAULT (RSTOBJ2::KEY)
                                        (DECLARE (XARGS :GUARD T))
                                        (CASE RSTOBJ2::KEY
                                              (:MEM 'NIL)
                                              (OTHERWISE NIL)))
                                 (DEFTHM EXAMPLE-RSTOBJ-ELEM-DEFAULT-OPENER
                                         (IMPLIES (SYNTAXP (QUOTEP K))
                                                  (EQUAL (EXAMPLE-RSTOBJ-ELEM-DEFAULT K)
                                                         (CASE K (:MEM 'NIL) (OTHERWISE NIL)))))
                                 (DEFTHM EXAMPLE-RSTOBJ-ELEM-P-OF-EXAMPLE-RSTOBJ-ELEM-DEFAULT
                                         (EXAMPLE-RSTOBJ-ELEM-P K (EXAMPLE-RSTOBJ-ELEM-DEFAULT K))
                                         :HINTS ((AND STABLE-UNDER-SIMPLIFICATIONP
                                                      '(:IN-THEORY (ENABLE EXAMPLE-RSTOBJ-ELEM-P)))))
                                 (IN-THEORY (DISABLE EXAMPLE-RSTOBJ-ELEM-DEFAULT))
                                 (DEFUN EXAMPLE-RSTOBJ-ELEM-DEFAULT-TOP (RSTOBJ2::KEY)
                                        (DECLARE (XARGS :GUARD T))
                                        (EXAMPLE-RSTOBJ-ELEM-DEFAULT (EC-CALL (CAR RSTOBJ2::KEY)))))
                          (RSTOBJ2::DEF-MULTITYPED-RECORD
                            EXAMPLE-RSTOBJREC
                            :ELEM-P (EXAMPLE-RSTOBJ-ELEM-P-TOP K X)
                            :ELEM-FIX (EXAMPLE-RSTOBJ-ELEM-FIX-TOP K X)
                            :ELEM-DEFAULT (EXAMPLE-RSTOBJ-ELEM-DEFAULT-TOP K)
                            :IN-PACKAGE-OF EXAMPLE-RSTOBJ)
                          (LOCAL
                            (IN-THEORY
                              (UNION-THEORIES
                                NIL
                                (UNION-THEORIES
                                  (UNION-THEORIES (THEORY 'MINIMAL-THEORY)
                                                  '(ACL2::NATP-COMPOUND-RECOGNIZER
                                                     NTH-UPDATE-NTH
                                                     CONS-EQUAL ACL2::NFIX-WHEN-NATP (NFIX)
                                                     (NATP)
                                                     CAR-CONS CDR-CONS (MAKE-LIST-AC)
                                                     (NTH)
                                                     (CONS)
                                                     (LEN)
                                                     UPDATE-NTH-ARRAY))
                                  (SET-DIFFERENCE-THEORIES (CURRENT-THEORY :HERE)
                                                           (CURRENT-THEORY 'EXAMPLE-RSTOBJ-START))))))
                          (DEFUN GET-EXAMPLE-RSTOBJ (RSTOBJ2::FLD RSTOBJ2::INDEX EXAMPLE-RSTOBJ$A)
                                 (DECLARE (XARGS :GUARD T))
                                 (EXAMPLE-RSTOBJREC-GET (CONS RSTOBJ2::FLD RSTOBJ2::INDEX)
                                                        EXAMPLE-RSTOBJ$A))
                          (DEFUN SET-EXAMPLE-RSTOBJ (RSTOBJ2::FLD RSTOBJ2::INDEX
                                                                  RSTOBJ2::VAL EXAMPLE-RSTOBJ$A)
                                 (DECLARE (XARGS :GUARD T))
                                 (EXAMPLE-RSTOBJREC-SET (CONS RSTOBJ2::FLD RSTOBJ2::INDEX)
                                                        RSTOBJ2::VAL EXAMPLE-RSTOBJ$A))
                          (DEFTHM EXAMPLE-RSTOBJ-ELEM-P-OF-GET-EXAMPLE-RSTOBJ
                                  (EXAMPLE-RSTOBJ-ELEM-P
                                    RSTOBJ2::FLD
                                    (GET-EXAMPLE-RSTOBJ RSTOBJ2::FLD I EXAMPLE-RSTOBJ$A))
                                  :HINTS (("goal" :USE ((:INSTANCE ELEM-P-OF-EXAMPLE-RSTOBJREC-GET
                                                                   (A (CONS RSTOBJ2::FLD I))
                                                                   (X EXAMPLE-RSTOBJ$A)))
                                           :IN-THEORY (DISABLE ELEM-P-OF-EXAMPLE-RSTOBJREC-GET))))
                          (MAKE-EVENT
                            '(:OR
                               (DEFTHM ELEM-P-OF-GET-EXAMPLE-RSTOBJ-MEM
                                       NIL
                                       :HINTS
                                       (("goal"
                                         :USE ((:INSTANCE EXAMPLE-RSTOBJ-ELEM-P-OF-GET-EXAMPLE-RSTOBJ
                                                          (RSTOBJ2::FLD :MEM)))
                                         :IN-THEORY (DISABLE EXAMPLE-RSTOBJ-ELEM-P-OF-GET-EXAMPLE-RSTOBJ))))
                               (MAKE-EVENT
                                 (PROG2$
                                   (CW
                                     "*** NOTE: Failed to prove rewrite rule stating that ~x0 satisfies ~x1 for field ~x2.~%"
                                     'GET-EXAMPLE-RSTOBJ
                                     'NIL
                                     ':MEM)
                                   '(VALUE-TRIPLE :SKIPPED)))))
                          (DEFTHM GET-EXAMPLE-RSTOBJ-OF-NIL
                                  (EQUAL (GET-EXAMPLE-RSTOBJ RSTOBJ2::FLD I NIL)
                                         (EXAMPLE-RSTOBJ-ELEM-DEFAULT RSTOBJ2::FLD)))
                          (DEFTHM EXAMPLE-RSTOBJREC-BAD-PART-OF-SET-EXAMPLE-RSTOBJ
                                  (EQUAL (EXAMPLE-RSTOBJREC-BAD-PART
                                           (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD
                                                               I RSTOBJ2::VAL EXAMPLE-RSTOBJ$A))
                                         (EXAMPLE-RSTOBJREC-BAD-PART EXAMPLE-RSTOBJ$A)))
                          (DEFTHM GET-EXAMPLE-RSTOBJ-OF-SET-EXAMPLE-RSTOBJ-INTRA-FIELD
                                  (EQUAL (GET-EXAMPLE-RSTOBJ
                                           RSTOBJ2::FLD I
                                           (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD J V EXAMPLE-RSTOBJ$A))
                                         (IF (EQUAL I J)
                                             (EXAMPLE-RSTOBJ-ELEM-FIX RSTOBJ2::FLD V)
                                             (GET-EXAMPLE-RSTOBJ RSTOBJ2::FLD I EXAMPLE-RSTOBJ$A))))
                          (DEFTHM GET-EXAMPLE-RSTOBJ-OF-SET-EXAMPLE-RSTOBJ-INTER-FIELD
                                  (IMPLIES
                                    (CASE-SPLIT (NOT (EQUAL RSTOBJ2::FLD1 RSTOBJ2::FLD2)))
                                    (EQUAL
                                      (GET-EXAMPLE-RSTOBJ RSTOBJ2::FLD2 RSTOBJ2::I2
                                                          (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD1
                                                                              RSTOBJ2::I1 V EXAMPLE-RSTOBJ$A))
                                      (GET-EXAMPLE-RSTOBJ RSTOBJ2::FLD2
                                                          RSTOBJ2::I2 EXAMPLE-RSTOBJ$A))))
                          (DEFTHM SET-EXAMPLE-RSTOBJ-SET-EXAMPLE-RSTOBJ-SHADOW-WRITES
                                  (EQUAL
                                    (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD I RSTOBJ2::V2
                                                        (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD
                                                                            I RSTOBJ2::V1 EXAMPLE-RSTOBJ$A))
                                    (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD
                                                        I RSTOBJ2::V2 EXAMPLE-RSTOBJ$A)))
                          (DEFTHM SET-EXAMPLE-RSTOBJ-SET-EXAMPLE-RSTOBJ-INTRA-FIELD-ARRANGE-WRITES
                                  (IMPLIES
                                    (NOT (EQUAL RSTOBJ2::I1 RSTOBJ2::I2))
                                    (EQUAL
                                      (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD RSTOBJ2::I2 RSTOBJ2::V2
                                                          (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD RSTOBJ2::I1
                                                                              RSTOBJ2::V1 EXAMPLE-RSTOBJ$A))
                                      (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD RSTOBJ2::I1 RSTOBJ2::V1
                                                          (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD RSTOBJ2::I2
                                                                              RSTOBJ2::V2 EXAMPLE-RSTOBJ$A))))
                                  :RULE-CLASSES ((:REWRITE :LOOP-STOPPER ((RSTOBJ2::I2 RSTOBJ2::I1)))))
                          (DEFTHM SET-EXAMPLE-RSTOBJ-SET-EXAMPLE-RSTOBJ-INTER-FIELD-ARRANGE-WRITES
                                  (IMPLIES
                                    (NOT (EQUAL RSTOBJ2::FLD1 RSTOBJ2::FLD2))
                                    (EQUAL
                                      (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD2 RSTOBJ2::I2 RSTOBJ2::V2
                                                          (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD1 RSTOBJ2::I1
                                                                              RSTOBJ2::V1 EXAMPLE-RSTOBJ$A))
                                      (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD1 RSTOBJ2::I1 RSTOBJ2::V1
                                                          (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD2 RSTOBJ2::I2
                                                                              RSTOBJ2::V2 EXAMPLE-RSTOBJ$A))))
                                  :RULE-CLASSES ((:REWRITE :LOOP-STOPPER ((RSTOBJ2::FLD2 RSTOBJ2::FLD1)))))
                          (DEFTHM SET-EXAMPLE-RSTOBJ-OF-GET-EXAMPLE-RSTOBJ
                                  (EQUAL
                                    (SET-EXAMPLE-RSTOBJ RSTOBJ2::FLD I
                                                        (GET-EXAMPLE-RSTOBJ RSTOBJ2::FLD I EXAMPLE-RSTOBJ$A)
                                                        EXAMPLE-RSTOBJ$A)
                                    EXAMPLE-RSTOBJ$A))
                          (IN-THEORY (DISABLE GET-EXAMPLE-RSTOBJ SET-EXAMPLE-RSTOBJ))
                          (DEFUN MEM$A (EXAMPLE-RSTOBJ$A)
                                 (DECLARE (XARGS :GUARD T))
                                 (GET-EXAMPLE-RSTOBJ :MEM NIL EXAMPLE-RSTOBJ$A))
                          (DEFUN !MEM$A (V EXAMPLE-RSTOBJ$A)
                                 (DECLARE (XARGS :GUARD NIL))
                                 (SET-EXAMPLE-RSTOBJ :MEM NIL V EXAMPLE-RSTOBJ$A))
                          (DEFUN EXAMPLE-RSTOBJ$AP (EXAMPLE-RSTOBJ$A)
                                 (DECLARE (XARGS :GUARD T))
                                 (NOT (EXAMPLE-RSTOBJREC-BAD-PART EXAMPLE-RSTOBJ$A)))
                          (DEFUN CREATE-EXAMPLE-RSTOBJ$A NIL
                                 (DECLARE (XARGS :GUARD T))
                                 NIL)
                          (LOCAL
                            (PROGN
                              (IN-THEORY (DISABLE NTH
                                                  UPDATE-NTH ACL2::NTH-WHEN-ZP NTH-ADD1))
                              (DEFUN-NX EXAMPLE-RSTOBJ-CORR
                                        (EXAMPLE-RSTOBJ$C EXAMPLE-RSTOBJ$A)
                                        (AND (EQUAL (MEM$A EXAMPLE-RSTOBJ$A)
                                                    (MEM$C EXAMPLE-RSTOBJ$C))))
                              (IN-THEORY (DISABLE (EXAMPLE-RSTOBJ-CORR)))
                              (SET-DEFAULT-HINTS '((AND STABLE-UNDER-SIMPLIFICATIONP
                                                        (LET ((RSTOBJ2::LIT (CAR (LAST CLAUSE))))
                                                             (AND (CONSP RSTOBJ2::LIT)
                                                                  (MEMBER-EQ (CAR RSTOBJ2::LIT) 'NIL)
                                                                  (CONS ':EXPAND
                                                                        (CONS (CONS RSTOBJ2::LIT 'NIL)
                                                                              'NIL)))))))
                              (IN-THEORY (E/D (RSTOBJ2::NTH-WHEN-ALL-EQUAL RSTOBJ2::NTH-OF-CONS
                                                                           (RSTOBJ2::ALL-EQUAL)
                                                                           (ZP))))))
                          (ACL2::DEFABSSTOBJ-EVENTS
                            EXAMPLE-RSTOBJ
                            :FOUNDATION EXAMPLE-RSTOBJ$C
                            :CORR-FN EXAMPLE-RSTOBJ-CORR
                            :RECOGNIZER (EXAMPLE-RSTOBJP :LOGIC EXAMPLE-RSTOBJ$AP
                                                         :EXEC EXAMPLE-RSTOBJ$CP)
                            :CREATOR (CREATE-EXAMPLE-RSTOBJ :LOGIC CREATE-EXAMPLE-RSTOBJ$A
                                                            :EXEC CREATE-EXAMPLE-RSTOBJ$C)
                            :EXPORTS ((MEM :LOGIC MEM$A :EXEC MEM$C)
                                      (!MEM :LOGIC !MEM$A
                                            :EXEC UPDATE-MEM$C)))))

(defun mem-function (bigmem::mem)
  (declare (xargs :stobjs (bigmem::mem)))
  (bigmem::read-mem 10 bigmem::mem))
