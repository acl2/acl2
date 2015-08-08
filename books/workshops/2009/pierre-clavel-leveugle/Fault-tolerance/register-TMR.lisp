; -----------------------------------------------------------------------------
; |                                                                           |
; | Description : This book define a TMR FSM, that has:                       |
; |               o Two inputs :                                              |
; |                   - in_value   : new input value                          |
; |                   - ld_flag    : load flag                                |
; |               o Two outputs :                                             |
; |                   - out_value  : current value of the register            |
; |                   - e_detect   : error detection flag                     |
; |                                                                           |
; -----------------------------------------------------------------------------

(IN-PACKAGE "ACL2")
(include-book "error-model")

; definition of the TMR FSM
; -------------------------

(defspec TMR
; - Signatures
  (((TMR-Sp          *) => *) ; State predicate
   ((TMR-next      * *) => *) ; transition function
   ((TMR-out_value * *) => *) ; out_value output function
   ((TMR-e_detect  * *) => *) ; e_detect output function
   ((TMR-reach_state *) => *) ; reachable states
   ((TMR-error       *) => *)); error in a TMR

; - Constants
  (local (defconst *TMR/mem1* 0))
  (local (defconst *TMR/mem2* 1))
  (local (defconst *TMR/mem3* 2))
  (defconst *TMR/in_value*       0)
  (defconst *TMR/ld_flag*       1)
  (local (defconst *TMR/def_val*  0))

; - Witnesses (not "toy" witnesses, actual definitions for a register)
;    + Definition of the state predicate
  (local (defun TMR-Sp (x)
           (and (true-listp x)
		(natp (nth *TMR/mem1* x)) ; first memory
		(natp (nth *TMR/mem2* x)) ; second memory
		(natp (nth *TMR/mem3* x)) ; third memory
		(equal (len x) 3))))
;    + Definition of the transition function
  (local (defun TMR-next (current_input current_state)
           (if (and (TMR-Sp current_state)
                    (true-listp current_input)
                    (natp     (nth *TMR/in_value* current_input))
                    (booleanp (nth *TMR/ld_flag* current_input))
                    (equal (len current_input) 2))
               (list
                ; TMR/current_memory1
                (cond ((nth *TMR/ld_flag* current_input)
                       (nth *TMR/in_value* current_input))
                      ((or (equal (nth *TMR/mem1* current_state)
                                  (nth *TMR/mem2* current_state))
                           (equal (nth *TMR/mem1* current_state)
                                  (nth *TMR/mem3* current_state)))
                       (nth *TMR/mem1* current_state))
                      ((equal (nth *TMR/mem2* current_state)
                              (nth *TMR/mem3* current_state))
                       (nth *TMR/mem2* current_state))
                      (T
                       *TMR/def_val*))
                ; TMR/current_memory2
                (cond ((nth *TMR/ld_flag* current_input)
                       (nth *TMR/in_value* current_input))
                      ((or (equal (nth *TMR/mem1* current_state)
                                  (nth *TMR/mem2* current_state))
                           (equal (nth *TMR/mem1* current_state)
                                  (nth *TMR/mem3* current_state)))
                       (nth *TMR/mem1* current_state))
                      ((equal (nth *TMR/mem2* current_state)
                              (nth *TMR/mem3* current_state))
                       (nth *TMR/mem2* current_state))
                      (T
                       *TMR/def_val*))
                ; TMR/current_memory3
                (cond ((nth *TMR/ld_flag* current_input)
                       (nth *TMR/in_value* current_input))
                      ((or (equal (nth *TMR/mem1* current_state)
                                  (nth *TMR/mem2* current_state))
                           (equal (nth *TMR/mem1* current_state)
                                  (nth *TMR/mem3* current_state)))
                       (nth *TMR/mem1* current_state))
                      ((equal (nth *TMR/mem2* current_state)
                              (nth *TMR/mem3* current_state))
                       (nth *TMR/mem2* current_state))
                      (T
                       *TMR/def_val*))
                )
             "error")))
;    + Definition of the function that gives the out_value output signal
  (local (defun TMR-out_value (current_input current_state)
           (if (and (TMR-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (cond ((or (equal (nth *TMR/mem1* current_state)
                                 (nth *TMR/mem2* current_state))
                          (equal (nth *TMR/mem1* current_state)
                                 (nth *TMR/mem3* current_state)))
                      (nth *TMR/mem1* current_state))
                     ((equal (nth *TMR/mem2* current_state)
                             (nth *TMR/mem3* current_state))
                      (nth *TMR/mem2* current_state))
                     (T
                      *TMR/def_val*)
                )
             "error")))
;    + Definition of the function that gives the e_detect output signal
  (local (defun TMR-e_detect (current_input current_state)
           (if (and (TMR-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (and (not (equal (nth *TMR/mem1* current_state)
                                (nth *TMR/mem2* current_state)))
                    (not (equal (nth *TMR/mem1* current_state)
                                (nth *TMR/mem3* current_state)))
                    (not (equal (nth *TMR/mem2* current_state)
                                (nth *TMR/mem3* current_state))))
               "error")))
;    + Definition of TMR reachable states
  (local (defun TMR-reach_state (S)
           (and (TMR-Sp S)
                (equal (nth *TMR/mem1* S)
                       (nth *TMR/mem2* S))
                (equal (nth *TMR/mem1* S)
                       (nth *TMR/mem3* S)))))
;    + Definition of an error in a TMR FSM
;      * The error is located in the first memory
  (local (defun TMR-inject1 (x)
           (if (TMR-Sp x)
               (list (STD-natp-error (nth *TMR/mem1* x))
                     (nth *TMR/mem2* x)
                     (nth *TMR/mem3* x))
               "error")))
;      * Or the error is located in the second memory
  (local (defun TMR-inject2 (x)
           (if (TMR-Sp x)
               (list (nth *TMR/mem1* x)
                     (STD-natp-error (nth *TMR/mem2* x))
                     (nth *TMR/mem3* x))
               "error")))
;      * Or the error is located in the third memory
  (local (defun TMR-inject3 (x)
           (if (TMR-Sp x)
               (list (nth *TMR/mem1* x)
                     (nth *TMR/mem2* x)
                     (STD-natp-error (nth *TMR/mem3* x)))
               "error")))
;      * Definition of the error model
  (local (encapsulate
          (((TMR-error *) => *))
          (local (defun TMR-error (x) (TMR-inject1 x)))
          (defthm TMR-error-type1
            (equal (TMR-Sp (TMR-error x))
                   (TMR-Sp x)))
          (defthm TMR-error-type2
            (implies (not (TMR-Sp x))
                     (equal (TMR-error x) "error")))
          (defthm TMR-error-def1
            (implies (TMR-Sp x)
                     (not (equal (TMR-error x) x))))
          (defthm TMR-error-def2    ; the error can be located in any of the 3 registers
            (or (equal (TMR-error x)
                       (TMR-inject1 x))
                (equal (TMR-error x)
                       (TMR-inject2 x))
                (equal (TMR-error x)
                       (TMR-inject3 x)))
            :hints (("Goal" :in-theory (disable TMR-Sp)))
            :rule-classes nil)))

; - Typing properties
; -------------------

;    + Sp is a predicate
  (defthm TMR-thm-Sp-type
    (booleanp (TMR-Sp S))
    :rule-classes ((:type-prescription :typed-term (TMR-Sp S))))

;    + "error" is not a Sp (speeds up proofs)
  (defthm TMR-thm-Sp-error
    (not (TMR-Sp "error"))
    :rule-classes :rewrite)

;    + Output of the transition function
  (defthm TMR-thm-next-type1
    (implies (TMR-Sp S)
             (equal (TMR-Sp (TMR-next I S))
                    (and (true-listp I)
                         (natp     (nth *TMR/in_value* I))
                         (booleanp (nth *TMR/ld_flag* I))
                         (equal (len I) 2))))
    :rule-classes :rewrite)

;    + Input of the transition function
  (defthm TMR-thm-next-type2
    (implies (or (not (TMR-Sp S))
                 (not (true-listp I))
                 (not (natp     (nth *TMR/in_value*      I)))
                 (not (booleanp (nth *TMR/ld_flag*      I)))
                 (not (equal (len I) 2)))
             (equal (TMR-next I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the out_value output signal
  (defthm TMR-thm-out_value-type1
    (implies (TMR-Sp S)
             (equal (natp (TMR-out_value I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the out_value output signal
  (defthm TMR-thm-out_value-type2
    (implies (or (not (TMR-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (TMR-out_value I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the e_detect output signal
  (defthm TMR-thm-e_detect-type1
    (implies (TMR-Sp S)
             (equal (booleanp (TMR-e_detect I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the e_detect output signal
  (defthm TMR-thm-e_detect-type2
    (implies (or (not (TMR-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (TMR-e_detect I S)
                    "error"))
    :rule-classes :rewrite)

;    + reach_state is a predicate
  (defthm TMR-thm-reach_state-type
    (booleanp (TMR-reach_state S))
    :rule-classes ((:type-prescription :typed-term (TMR-reach_state S))))

;    + Output of error is a Sp
  (defthm TMR-thm-error-type1
    (equal (TMR-Sp (TMR-error S))
           (TMR-Sp S))
    :hints (("Goal" :in-theory (disable TMR-Sp)))
    :rule-classes :rewrite)

;    + input of error is a Sp
  (defthm TMR-thm-error-type2
    (implies (not (TMR-Sp S))
             (equal (TMR-error S)
                    "error"))
    :rule-classes :rewrite)

;    + the transition function returns a reachable state
  (defthm TMR-thm-reach_state
    (implies (and (TMR-Sp S)
                  (TMR-reach_state S))
             (equal (TMR-reach_state (TMR-next I S))
                    (and (true-listp I)
                         (natp     (nth *TMR/in_value* I))
                         (booleanp (nth *TMR/ld_flag* I))
                         (equal (len I) 2))))
    :rule-classes :rewrite)

; - Robustness-related properties
; -------------------------------

;    + fault-injection is actual
  (defthm TMR-thm-error
    (implies (TMR-Sp S)
             (not (equal (TMR-error S) S)))
    :rule-classes ((:forward-chaining :match-free :all
                                      :trigger-terms ((TMR-Sp S)))))

;    + an error is corrected after one clock tick
  (defthm TMR-thm-hardened-1
    (implies (and (TMR-Sp S)
                  (TMR-reach_state S)
                  (true-listp I)
                  (natp     (nth *TMR/in_value* I))
                  (booleanp (nth *TMR/ld_flag* I))
                  (equal (len I) 2))
             (equal (TMR-next I (TMR-error S))
                    (TMR-next I S)))
    :hints (("Goal" :use (:instance TMR-error-def2 (x S))))
    :rule-classes :rewrite)

;    + the output_value output signal does not change when an error occurs
  (defthm TMR-thm-hardened-2
    (implies (and (TMR-Sp S)
                  (TMR-reach_state S))
             (equal (TMR-out_value nil (TMR-error S))
                    (TMR-out_value nil S)))
    :hints (("Goal" :use (:instance TMR-error-def2 (x S))))
    :rule-classes ((:forward-chaining :match-free :all
                                      :trigger-terms ((TMR-Sp S)))))

;    + no error is detected when no error occurs
  (defthm TMR-thm-hardened-3
    (implies (and (TMR-Sp S)
                  (TMR-reach_state S))
             (not (TMR-e_detect nil S)))
    :hints (("Goal" :in-theory (disable TMR-Sp)))
    :rule-classes :rewrite)

;    + no error is detected when an error occurs
;     (two errors are needed for detection)
  (defthm TMR-thm-hardened-4
    (implies (and (TMR-Sp S)
                  (TMR-reach_state S))
             (not (TMR-e_detect nil (TMR-error S))))
    :hints (("Goal" :use (:instance TMR-error-def2 (x S))))
    :rule-classes :rewrite)
)
