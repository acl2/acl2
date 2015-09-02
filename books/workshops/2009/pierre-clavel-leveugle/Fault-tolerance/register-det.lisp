; -----------------------------------------------------------------------------
; |                                                                           |
; | Description : This book defines a register with a error detection system, |
; |               that has :                                                  |
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

; definition of the REG-det FSM
; -----------------------------

(defspec REG-det
; - Signatures
  (((REG-det-Sp          *) => *) ; State predicate
   ((REG-det-next      * *) => *) ; transition function
   ((REG-det-out_value * *) => *) ; out_value output function
   ((REG-det-e_detect  * *) => *) ; e_detect output function
   ((REG-det-reach_state *) => *) ; reachable states
   ((REG-det-error       *) => *)); error in a REG-det

; - Constants
  (local (defconst *REG-det/mem1* 0))
  (local (defconst *REG-det/mem2* 1))
  (defconst *REG-det/in_value*      0)
  (defconst *REG-det/ld_flag*       1)
  (local (defconst *REG-det/def_val*  0))

; - Witnesses (not "toy" witnesses, actual definitions for a register-det)
;    + Definition of the state predicate
  (local (defun REG-det-Sp (x)     ; two state elements
           (and (true-listp x)
		(natp (nth *REG-det/mem1* x))
		(natp (nth *REG-det/mem2* x))
		(equal (len x) 2))))
;    + Definition of the transition function
  (local (defun REG-det-next (current_input current_state)
           (if (and (REG-det-Sp current_state)
                    (true-listp current_input)
                    (natp     (nth *REG-det/in_value* current_input))
                    (booleanp (nth *REG-det/ld_flag* current_input))
                    (equal (len current_input) 2))
               (list ; REG-det/mem1
                     (if (nth *REG-det/ld_flag* current_input)
			 (nth *REG-det/in_value* current_input)
		         (if (equal (nth *REG-det/mem1* current_state)
				    (nth *REG-det/mem2* current_state))
			     (nth *REG-det/mem1* current_state)
			     *REG-det/def_val*))
		     ; REG-det/mem2
                     (if (nth *REG-det/ld_flag* current_input)
			 (nth *REG-det/in_value* current_input)
		         (if (equal (nth *REG-det/mem1* current_state)
				    (nth *REG-det/mem2* current_state))
			     (nth *REG-det/mem1* current_state)
			     *REG-det/def_val*)))
	       "error")))
;    + Definition of the function that gives the out_value output signal
  (local (defun REG-det-out_value (current_input current_state)
           (if (and (REG-det-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (if (equal (nth *REG-det/mem1* current_state)
                          (nth *REG-det/mem2* current_state))
                   (nth *REG-det/mem1* current_state)
                   *REG-det/def_val*)
               "error")))
;    + Definition of the function that gives the e_detect output signal
  (local (defun REG-det-e_detect (current_input current_state)
           (if (and (REG-det-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (not (equal (nth *REG-det/mem1* current_state)
                           (nth *REG-det/mem2* current_state)))
               "error")))
;    + Definition of REG-det reachable states (nominal case)
  (local (defun REG-det-reach_state (S)   ; the 2 registers have the same value
           (and (REG-det-Sp S)
                (equal (nth *REG-det/mem1* S)
                       (nth *REG-det/mem2* S)))))
;    + Definition of an error in a REG-det FSM
;      * The error is located in the first memory
  (local (defun REG-det-inject1 (x)
           (if (REG-det-Sp x)
               (list (STD-natp-error (nth *REG-det/mem1* x))
                     (nth *REG-det/mem2* x))
               "error")))
;      * Or the error is located in the second memory
  (local (defun REG-det-inject2 (x)
           (if (REG-det-Sp x)
               (list (nth *REG-det/mem1* x)
                     (STD-natp-error (nth *REG-det/mem2* x)))
               "error")))
;      * Definition of the error model
  (local (encapsulate
          (((REG-det-error *) => *))
          (local (defun REG-det-error (x) (REG-det-inject1 x)))
          (defthm REG-det-error-type1
            (equal (REG-det-Sp (REG-det-error x))
                   (REG-det-Sp x)))
          (defthm REG-det-error-type2
            (implies (not (REG-det-Sp x))
                     (equal (REG-det-error x) "error")))
          (defthm REG-det-error-def1
            (implies (REG-det-Sp x)
                     (not (equal (REG-det-error x) x))))
          (defthm REG-det-error-def2         ; the error can be located in the first
            (or (equal (REG-det-error x)     ; or in the second register
                       (REG-det-inject1 x))
                (equal (REG-det-error x)
                       (REG-det-inject2 x)))
            :hints (("Goal" :in-theory (disable REG-det-Sp)))
            :rule-classes nil)))

; - Typing properties
; -------------------

;    + Sp is a predicate
  (defthm REG-det-thm-Sp-type
    (booleanp (REG-det-Sp S))
    :rule-classes ((:type-prescription :typed-term (REG-det-Sp S))))

;    + "error" is not a Sp (speeds up proofs)
  (defthm REG-det-thm-Sp-error
    (not (REG-det-Sp "error"))
    :rule-classes :rewrite)

;    + Output of the transition function
  (defthm REG-det-thm-next-type1
    (implies (REG-det-Sp S)
             (equal (REG-det-Sp (REG-det-next I S))
                    (and (true-listp I)
                         (natp     (nth *REG-det/in_value* I))
                         (booleanp (nth *REG-det/ld_flag* I))
                         (equal (len I) 2))))
    :rule-classes :rewrite)

;    + Input of the transition function
  (defthm REG-det-thm-next-type2
    (implies (or (not (REG-det-Sp S))
                 (not (true-listp I))
                 (not (natp     (nth *REG-det/in_value*      I)))
                 (not (booleanp (nth *REG-det/ld_flag*      I)))
                 (not (equal (len I) 2)))
             (equal (REG-det-next I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the out_value output signal
  (defthm REG-det-thm-out_value-type1
    (implies (REG-det-Sp S)
             (equal (natp (REG-det-out_value I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the out_value output signal
  (defthm REG-det-thm-out_value-type2
    (implies (or (not (REG-det-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (REG-det-out_value I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the e_detect output signal
  (defthm REG-det-thm-e_detect-type1
    (implies (REG-det-Sp S)
             (equal (booleanp (REG-det-e_detect I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the e_detect output signal
  (defthm REG-det-thm-e_detect-type2
    (implies (or (not (REG-det-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (REG-det-e_detect I S)
                    "error"))
    :rule-classes :rewrite)

;    + reach_state is a predicate
  (defthm REG-det-thm-reach_state-type
    (booleanp (REG-det-reach_state S))
    :rule-classes ((:type-prescription :typed-term (REG-det-reach_state S))))

;    + Output of error is a Sp
  (defthm REG-det-thm-error-type1
    (equal (REG-det-Sp (REG-det-error S))
           (REG-det-Sp S))
    :hints (("Goal" :in-theory (disable REG-det-Sp)))
    :rule-classes :rewrite)

;    + input of error is a Sp
  (defthm REG-det-thm-error-type2
    (implies (not (REG-det-Sp S))
             (equal (REG-det-error S)
                    "error"))
    :rule-classes :rewrite)

;    + the transition function returns a reachable state
  (defthm REG-det-thm-reach_state
    (implies (and (REG-det-Sp S)
                  (REG-det-reach_state S))
             (equal (REG-det-reach_state (REG-det-next I S))
                    (and (true-listp I)
                         (natp     (nth *REG-det/in_value* I))
                         (booleanp (nth *REG-det/ld_flag* I))
                         (equal (len I) 2))))
    :rule-classes :rewrite)

; - Robustness-related properties
; -------------------------------

;    + fault-injection is actual
  (defthm REG-det-thm-error
    (implies (REG-det-Sp S)
             (not (equal (REG-det-error S) S)))
    :rule-classes ((:forward-chaining :match-free :all
                                      :trigger-terms ((REG-det-Sp S)))))

;    + an error is corrected after one clock tick if ld_flag = '1'
  (defthm REG-det-thm-hardened-1
    (implies (and (REG-det-Sp S)
                  (REG-det-reach_state S)
                  (true-listp I)
                  (natp     (nth *REG-det/in_value* I))
                  (booleanp (nth *REG-det/ld_flag* I))
                  (equal (len I) 2)
                  (nth *REG-det/ld_flag* I)) ; loading a new input
             (equal (REG-det-next I (REG-det-error S))
                    (REG-det-next I S)))
    :hints (("Goal" :use (:instance REG-det-error-def2 (x S))))
    :rule-classes :rewrite)

;    + no error is detected when no error occurs
  (defthm REG-det-thm-hardened-2
    (implies (and (REG-det-Sp S)
                  (REG-det-reach_state S))
             (not (REG-det-e_detect nil S)))
    :hints (("Goal" :in-theory (disable REG-det-Sp)))
    :rule-classes :rewrite)

;    + an error is detected when an error occurs
  (defthm REG-det-thm-hardened-3
    (implies (and (REG-det-Sp S)
                  (REG-det-reach_state S))
             (REG-det-e_detect nil (REG-det-error S)))
    :hints (("Goal" :use (:instance REG-det-error-def2 (x S))))
    :rule-classes :rewrite)
)
