(IN-PACKAGE "ACL2")

; !! Our original approach was to include the following book in the portcullis.
(include-book "model")
(include-book "constants")
(include-book "inputs")

(DEFUN INPUT-BINDINGS (N)
       (AND (EQUAL (*::LONGOP) (LONGOP N))
            (EQUAL (*::IN) (IN N))))

(DEFUN INPUT-ASSUMPTIONS* (N)
       (AND (INPUT-ASSUMPTIONS N)
            (INPUT-BINDINGS N)))

(DEFTHM INPUT$INPUT*
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (INPUT-ASSUMPTIONS N)))

(DEFTHM INPUT$BINDINGS
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (AND (EQUAL (*::IN) (IN N))
                      (EQUAL (*::LONGOP) (LONGOP N)))))

(IN-THEORY (DISABLE INPUT-ASSUMPTIONS*
                    (INPUT-ASSUMPTIONS*)))

;;*********************************************************************

(DEFTHM SIMP$LONGOP$1
        (IMPLIES (INPUT-ASSUMPTIONS N)
                 (EQUAL (LONGOP (+ 1 N)) 1))
        :HINTS
        (("Goal" :IN-THEORY (ENABLE INPUT-ASSUMPTIONS))))

(DEFTHM SIMP$LONGOP$0
        (IMPLIES (INPUT-ASSUMPTIONS N)
                 (EQUAL (LONGOP N) 1))
        :HINTS
        (("Goal" :IN-THEORY (ENABLE INPUT-ASSUMPTIONS))))

(DEFTHM LONGOP_FLOPPED$PIPE$REWRITE
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (EQUAL (*::LONGOP_FLOPPED) 1))
        :HINTS
        (("Goal" :IN-THEORY
                 (ENABLE LONGOP_FLOPPED *::LONGOP_FLOPPED))))

(DEFTHM SIMP$LONGOP_FLOPPED$1
        (IMPLIES (INPUT-ASSUMPTIONS N)
                 (EQUAL (LONGOP_FLOPPED (+ 1 N)) 1))
        :HINTS
        (("Goal" :IN-THEORY (ENABLE LONGOP_FLOPPED))))

(DEFTHM SIMP$LONGOP_FLOPPED$2
        (IMPLIES (INPUT-ASSUMPTIONS N)
                 (EQUAL (LONGOP_FLOPPED (+ 2 N)) 1))
        :HINTS
        (("Goal" :IN-THEORY (ENABLE LONGOP_FLOPPED))))

;;*********************************************************************

(DEFTHM S01$PIPE$REWRITE
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (EQUAL (*::S01) (S01 N)))
        :HINTS
        (("Goal" :IN-THEORY (ENABLE S01 *::S01))))

(DEFTHM S01_MUXED$PIPE$REWRITE
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (EQUAL (*::S01_MUXED) (S01_MUXED N)))
        :HINTS
        (("Goal" :IN-THEORY
                 (ENABLE S01_MUXED *::S01_MUXED))))

; !! The following is needed for S01_MUXED_FLOPPED$PIPE$REWRITE.

(defthm input-assumptions*-forward
  (implies (input-assumptions* n)
           (and (integerp n)
                (< 0 n)
                (equal (longop n) 1)
                (equal (longop (+ 1 n)) 1)))
  :hints (("Goal" :in-theory (enable input-assumptions*)))
  :rule-classes :forward-chaining)

(DEFTHM S01_MUXED_FLOPPED$PIPE$REWRITE
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (EQUAL (*::S01_MUXED_FLOPPED)
                        (S01_MUXED_FLOPPED (+ 1 N))))
        :HINTS
        (("Goal" :IN-THEORY
                 (ENABLE S01_MUXED_FLOPPED
                         *::S01_MUXED_FLOPPED))))

(DEFTHM S23$PIPE$REWRITE
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (EQUAL (*::S23) (S23 N)))
        :HINTS
        (("Goal" :IN-THEORY (ENABLE S23 *::S23))))

(DEFTHM S23_FLOPPED$PIPE$REWRITE
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (EQUAL (*::S23_FLOPPED)
                        (S23_FLOPPED (+ 1 N))))
        :HINTS
        (("Goal" :IN-THEORY
                 (ENABLE S23_FLOPPED *::S23_FLOPPED))))

(DEFTHM S0123$PIPE$REWRITE
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (EQUAL (*::S0123) (S0123 (+ 2 N))))
        :HINTS
        (("Goal" :IN-THEORY (ENABLE S0123 *::S0123))))

(DEFTHM OUT$PIPE$REWRITE
        (IMPLIES (INPUT-ASSUMPTIONS* N)
                 (EQUAL (*::OUT) (OUT (+ 2 N))))
        :HINTS
        (("Goal" :IN-THEORY (ENABLE OUT *::OUT))))

