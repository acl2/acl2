(IN-PACKAGE "ACL2")

(ENCAPSULATE
  ((LONGOP (N) T) (IN (N) T))
  (LOCAL (DEFUN LONGOP (N)
                (DECLARE (IGNORE N))
                0))
  (LOCAL (DEFUN IN (N) (DECLARE (IGNORE N)) 0))
  (DEFTHM BVECP$LONGOP (BVECP (LONGOP N) 1)
          :RULE-CLASSES
          (:REWRITE (:FORWARD-CHAINING :TRIGGER-TERMS ((LONGOP N)))
                    (:TYPE-PRESCRIPTION :COROLLARY
                                        (AND (INTEGERP (LONGOP N))
                                             (>= (LONGOP N) 0))
                                        :HINTS
                                        (("Goal" :IN-THEORY '(IMPLIES BVECP)))))
          :HINTS
          (("Goal" :IN-THEORY (ENABLE LONGOP))))
  (DEFTHM BVECP$IN (BVECP (IN N) 4)
          :RULE-CLASSES
          (:REWRITE (:FORWARD-CHAINING :TRIGGER-TERMS ((IN N)))
                    (:TYPE-PRESCRIPTION :COROLLARY
                                        (AND (INTEGERP (IN N)) (>= (IN N) 0))
                                        :HINTS
                                        (("Goal" :IN-THEORY '(IMPLIES BVECP)))))
          :HINTS
          (("Goal" :IN-THEORY (ENABLE IN)))))

(DEFUN RESET (N) (= N 0))

(DEFUN LONGOP_FLOPPED (N)
       (IF (ZP N)
           (UNKNOWN 'LONGOP_FLOPPED 1 N)
           (LONGOP (1- N))))

(DEFUN S01 (N)
       (LOGAND (BITN (IN N) 0)
               (BITN (IN N) 1)))

(DEFUN S01_MUXED (N)
       (IF (EQL (LONGOP N) 0)
           (COMP1 (S01 N) 1)
           (S01 N)))

(DEFUN S01_MUXED_FLOPPED (N)
       (IF (ZP N)
           (UNKNOWN 'S01_MUXED_FLOPPED 1 N)
           (S01_MUXED (1- N))))

(DEFUN S23 (N)
       (LOGAND (BITN (IN N) 2)
               (BITN (IN N) 3)))

(DEFUN S23_FLOPPED (N)
       (IF (ZP N)
           (UNKNOWN 'S23_FLOPPED 1 N)
           (S23 (1- N))))

(DEFUN S0123 (N)
       (IF (ZP N)
           (UNKNOWN 'S0123 1 N)
           (LOGAND (S01_MUXED_FLOPPED (1- N))
                   (S23_FLOPPED (1- N)))))

(DEFUN OUT (N)
       (IF (EQL (LONGOP_FLOPPED N) 0)
           (S01_MUXED_FLOPPED N)
           (S0123 N)))

(IN-THEORY (DISABLE S01 S01_MUXED S23 OUT LONGOP_FLOPPED
                    S01_MUXED_FLOPPED S23_FLOPPED S0123))

