(IN-PACKAGE "ACL2")

(LOGIC)

(LOCAL (INCLUDE-BOOK "generic-loop-inv"))

; ------------------------------
; PRELIMINARY DEFINITIONS
; ------------------------------

(DEFUN |_N_33$PROP$INIT| (IN)
       (DECLARE (XARGS :NORMALIZE NIL))
       (|_N_8$LOOP$INIT| IN))

; ------------------------------
; PROOF OF LOOP INVARIANT PRESERVATION, IN ISOLATION
; ------------------------------

(DEFUN |_N_33$HYPS| (IN)
       (AND (NATP (G :LC IN))
            (INTEGERP (G :|_T_3| IN))
            (NATP (G :|_T_5| IN))
            (NATP (G :|_T_6| IN))))

(DEFUN |_N_33$PROP| (N IN)
       (DECLARE (IGNORABLE N))
       (AND (|_N_33$HYPS| IN)
            (EQUAL N (G :|_T_3| IN))
            (G :ASN (ACL2-LOOP-INV IN))))

; Here is the key lemma, which in principle at least requires some work by the
; prover, and may require help from the user.  It corresponds to the inductive
; step.

; USER ASSISTANCE MAY BE REQUIRED:


(DEFTHMDL |_N_33$PROP{_N_8$STEP}|
          (IMPLIES (AND (NATP (G :LC IN))
                        (< (G :LC IN) N)
                        (|_N_33$PROP| N IN))
                   (|_N_33$PROP| N
                                 (S :LC (1+ (G :LC IN))
                                    (|_N_8$STEP| IN)))))

(DEFTHML
  |_N_33$PROP{_N_8}|
  (IMPLIES (AND (NATP N)
                (NATP (G :LC IN))
                (|_N_33$PROP| N IN))
           (|_N_33$PROP| N (|_N_8$LOOP| N IN)))
  :HINTS
  (("Goal" :BY (:FUNCTIONAL-INSTANCE LOOP-GENERIC-THM
                                     (STEP-GENERIC |_N_8$STEP|)
                                     (PROP-GENERIC |_N_33$PROP|)
                                     (LOOP-GENERIC |_N_8$LOOP|))
           :IN-THEORY
           (UNION-THEORIES '(|_N_33$PROP{_N_8$STEP}|)
                           (THEORY 'MINIMAL-THEORY))
           :EXPAND ((|_N_8$LOOP| N IN))))
  :RULE-CLASSES NIL)

(DEFTHML LC$_N_8
         (IMPLIES (AND (NATP N)
                       (NATP (G :LC IN))
                       (<= (G :LC IN) N))
                  (EQUAL (G :LC (|_N_8$LOOP| N IN)) N))
         :HINTS (("Goal" :BY (:FUNCTIONAL-INSTANCE LOOP-GENERIC-LC
                                                   (STEP-GENERIC |_N_8$STEP|)
                                                   (PROP-GENERIC |_N_33$PROP|)
                                                   (LOOP-GENERIC |_N_8$LOOP|))
                         :IN-THEORY (THEORY 'MINIMAL-THEORY)
                         :EXPAND ((|_N_8$LOOP| N IN)))))

; ------------------------------
; CORRECTNESS OF LOOP INVARIANT
; WITH RESPECT TO THE ENVIRONMENT,
; BUT CONDITIONAL ON PRECONDITION
; ------------------------------

; We prove that the outer loop invariant block holds, under assumptions on its
; inputs, namely: type assumptions on the diagram's top-level inputs, as well
; as assumptions coming from the associated loop precondition block.

(DEFUN ACL2-LOOP-INV$INV{PRE} (IN)
       (AND (GAUSS$INPUT-HYPS IN)
            (NATP (INPUT1<_T_0> IN))))

(DEFTHML ACL2-LOOP-INV$INV{NATP-N}
         (IMPLIES (ACL2-LOOP-INV$INV{PRE} IN)
                  (NATP (INPUT1<_T_0> IN)))
         :HINTS (("Goal" :EXPAND ((ACL2-LOOP-INV$INV{PRE} IN))
                         :IN-THEORY (THEORY 'MINIMAL-THEORY)))
         :RULE-CLASSES NIL)

; USER ASSISTANCE MAY BE REQUIRED:
; This is a real proof obligation!  It implements the requirement that the
; invariant hold when initially entering the loop, and is thus probably trivial
; to prove in most cases.

; If a non-trivial precondition block has been specified for the loop
; invariant, then the invariant hypotheses may be enough to prove the property
; without opening up any signals in the actual design.  So you may wish to
; disable the inputs to the loop invariant block, from _N_xx$LOOP$INIT.  While
; that approach may speed up the proof of this lemma, it could make the proof
; fail.

(DEFTHML ACL2-LOOP-INV$INV{INIT}
         (IMPLIES (ACL2-LOOP-INV$INV{PRE} IN)
                  (|_N_33$PROP| (INPUT1<_T_0> IN)
                                (|_N_33$PROP$INIT| IN)))
         :RULE-CLASSES NIL)

(DEFTHMDL
    ACL2-LOOP-INV$INV{NATP-LOOP-INIT}
    (EQUAL (G :LC (|_N_33$PROP$INIT| IN)) 0)
    :HINTS (("Goal" :EXPAND ((|_N_33$PROP$INIT| IN)
                             (|_N_8$LOOP$INIT| IN))
                    :IN-THEORY (UNION-THEORIES '(S-ALIST)
                                               (CURRENT-THEORY 'START-GAUSS)))))

(DEFUN ACL2-LOOP-INV$INV+ (IN)
       (DECLARE (XARGS :NORMALIZE NIL))
       (|_N_33$PROP| (INPUT1<_T_0> IN)
                     (|_N_8$LOOP| (INPUT1<_T_0> IN)
                                  (|_N_8$LOOP$INIT| IN))))

(DEFTHML ACL2-LOOP-INV$INV$CONDITIONAL
         (IMPLIES (ACL2-LOOP-INV$INV{PRE} IN)
                  (ACL2-LOOP-INV$INV+ IN))
         :HINTS (("Goal" :USE ((:INSTANCE |_N_33$PROP{_N_8}|
                                          (IN (|_N_33$PROP$INIT| IN))
                                          (N (INPUT1<_T_0> IN)))
                               ACL2-LOOP-INV$INV{NATP-N}
                               ACL2-LOOP-INV$INV{INIT}
                               ACL2-LOOP-INV$INV{NATP-LOOP-INIT}
                               ACL2-LOOP-INV$INV+)
                         :IN-THEORY (UNION-THEORIES '((NATP) |_N_33$PROP$INIT|)
                                                    (THEORY 'MINIMAL-THEORY))))
         :RULE-CLASSES NIL)

; ------------------------------
; CORRECTNESS OF LOOP INVARIANT
; WITH RESPECT TO THE ENVIRONMENT
; ------------------------------

; First we prove the precondition.  In general, this could take some work.

; USER ASSISTANCE MAY BE REQUIRED:

(DEFTHML ACL2-LOOP-INV$INV{PRE}{HOLDS}
         (IMPLIES (GAUSS$INPUT-HYPS IN)
                  (AND (NATP (INPUT1<_T_0> IN))))
         :RULE-CLASSES NIL)

; Now we use the conditional invariant result to prove the desired assertion.

(DEFTHML
   ACL2-LOOP-INV$INV
   (IMPLIES (GAUSS$INPUT-HYPS IN)
            (ACL2-LOOP-INV$INV+ IN))
   :HINTS
   (("Goal" :IN-THEORY (UNION-THEORIES '(ACL2-LOOP-INV$INV{PRE})
                                       (THEORY 'MINIMAL-THEORY))
            :USE (ACL2-LOOP-INV$INV$CONDITIONAL ACL2-LOOP-INV$INV{PRE}{HOLDS})))
   :RULE-CLASSES NIL)

; ------------------------------
; CORRECTNESS OF MAIN ASSERTION BLOCK
; ------------------------------

; Our goal is to derive the main assertion as a corollary of the loop
; invariant.  Thus, we do not want to open up the self-reference (inner) node
; of the loop block.  The following lemmas extract what we
; need from that loop block.

(DEFTHML
    LEMMA-1-ACL2-LOOP
    (IMPLIES (NOT (MEMBER-EQ KEY (CONS :LC '(:|_T_5| :|_T_6|))))
             (EQUAL (G KEY (|_N_8$LOOP| N IN))
                    (G KEY IN)))
    :HINTS (("Goal" :IN-THEORY (UNION-THEORIES '(|_N_8$LOOP| |_N_8$STEP|)
                                               (CURRENT-THEORY 'START-GAUSS)))))

(DEFTHML LEMMA-2-ACL2-LOOP
         (IMPLIES (GAUSS$INPUT-HYPS IN)
                  (NATP (INPUT1<_T_0> IN)))
         :HINTS (("Goal" :IN-THEORY (ENABLE INPUT1<_T_0>)))
         :RULE-CLASSES NIL)

; USER ASSISTANCE MAY BE REQUIRED:

(DEFTHM ACL2-TOP-INV$INV
        (IMPLIES (GAUSS$INPUT-HYPS IN)
                 (G :ASN (ACL2-TOP-INV IN)))
        :HINTS (("Goal" :IN-THEORY (DISABLE |_N_8$LOOP|)
                        :USE (ACL2-LOOP-INV$INV LEMMA-2-ACL2-LOOP))))

