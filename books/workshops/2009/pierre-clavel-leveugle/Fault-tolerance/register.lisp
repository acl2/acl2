; -----------------------------------------------------------------------------
; |                                                                           |
; | Description : This book defines a REG FSM.                                |
; |               A REG FSM is a simple register with :                       |
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

; definition of the REG FSM
; -------------------------

(defspec REG
; - Signatures
  (((REG-Sp          *) => *) ; State predicate
   ((REG-next      * *) => *) ; transition function
   ((REG-out_value * *) => *) ; out_value output function
   ((REG-e_detect  * *) => *) ; e_detect output function
   ((REG-reach_state *) => *) ; reachable states
   ((REG-error       *) => *)); error in a REG

; - Constants
  (local (defconst *REG/current_memory* 0))
  (defconst *REG/in_value*      0)
  (defconst *REG/ld_flag*       1)
  (local (defconst *REG/default_value*  0))

; - Witnesses (not "toy" witnesses, actual definitions for a register)
;    + Definition of the state predicate
  (local (defun REG-Sp (x)      ; one state element
            (and (true-listp x)
                 (natp (nth *REG/current_memory* x))
                 (equal (len x) 1))))
;    + Definition of the transition function
  (local (defun REG-next (current_input current_state)
           (if (and (REG-Sp current_state)
                    (true-listp current_input)
                    (natp     (nth *REG/in_value* current_input))
                    (booleanp (nth *REG/ld_flag* current_input))
                    (equal (len current_input) 2))
               (list (if (nth *REG/ld_flag* current_input)
                         (nth *REG/in_value* current_input)
		         (nth *REG/current_memory* current_state)))
               "error")))
;    + Definition of the function that gives the out_value output signal
  (local (defun REG-out_value (current_input current_state)
           (if (and (REG-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (nth *REG/current_memory* current_state)
               "error")))
;    + Definition of the function that gives the e_detect output signal
  (local (defun REG-e_detect (current_input current_state)
           (if (and (REG-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               nil
               "error")))
;    + Definition of REG reachable states
  (local (defun REG-reach_state (S)
           (REG-Sp S)))
;    + Definition of an error in a REG FSM
;      * The error is located in the first memory
  (local (defun REG-inject1 (x)
           (if (REG-Sp x)
               (list (STD-natp-error (nth *REG/current_memory* x)))
               "error")))
;      * Definition of the error model
  (local (encapsulate
          (((REG-error *) => *))
          (local (defun REG-error (x) (REG-inject1 x)))
          (defthm REG-error-type1
            (equal (REG-Sp (REG-error x))
                   (REG-Sp x))
            :rule-classes :rewrite)
          (defthm REG-error-type2
            (implies (not (REG-Sp x))
                     (equal (REG-error x) "error"))
            :rule-classes :rewrite)
          (defthm REG-error-def1
            (implies (REG-Sp x)
                     (not (equal (REG-error x) x)))
            :rule-classes :rewrite)
          (defthm REG-error-def2  ; the error can only be located in the first register
            (or (equal (REG-error x)
                       (REG-inject1 x)))
            :hints (("Goal" :in-theory (disable REG-Sp)))
            :rule-classes nil)))

; - Typing properties
; -------------------

;    + Sp is a predicate
  (defthm REG-thm-Sp-type
    (booleanp (REG-Sp S))
    :rule-classes ((:type-prescription :typed-term (REG-Sp S))))

;    + "error" is not a Sp (speeds up proofs)
  (defthm REG-thm-Sp-error
    (not (REG-Sp "error"))
    :rule-classes :rewrite)

;    + Output of the transition function
  (defthm REG-thm-next-type1
    (implies (REG-Sp S)
             (equal (REG-Sp (REG-next I S))
                    (and (true-listp I)
                         (natp     (nth *REG/in_value* I))
                         (booleanp (nth *REG/ld_flag* I))
                         (equal (len I) 2))))
    :rule-classes :rewrite)

;    + Input of the transition function
  (defthm REG-thm-next-type2
    (implies (or (not (REG-Sp S))
                 (not (true-listp I))
                 (not (natp     (nth *REG/in_value*      I)))
                 (not (booleanp (nth *REG/ld_flag*      I)))
                 (not (equal (len I) 2)))
             (equal (REG-next I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the out_value output signal
  (defthm REG-thm-out_value-type1
    (implies (REG-Sp S)
             (equal (natp (REG-out_value I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the out_value output signal
  (defthm REG-thm-out_value-type2
    (implies (or (not (REG-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (REG-out_value I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the e_detect output signal
  (defthm REG-thm-e_detect-type1
    (implies (REG-Sp S)
             (equal (booleanp (REG-e_detect I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the e_detect output signal
  (defthm REG-thm-e_detect-type2
    (implies (or (not (REG-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (REG-e_detect I S)
                    "error"))
    :rule-classes :rewrite)

;    + reach_state is a predicate
  (defthm REG-thm-reach_state-type
    (booleanp (REG-reach_state S))
    :rule-classes ((:type-prescription :typed-term (REG-reach_state S))))

;    + Output of error is a Sp
  (defthm REG-thm-error-type1
    (equal (REG-Sp (REG-error S))
           (REG-Sp S))
    :hints (("Goal" :in-theory (disable REG-Sp)))
    :rule-classes :rewrite)

;    + input of error is a Sp
  (defthm REG-thm-error-type2
    (implies (not (REG-Sp S))
             (equal (REG-error S)
                    "error"))
    :rule-classes :rewrite)

;    + the transition function returns a reachable state
  (defthm REG-thm-reach_state
    (implies (and (REG-Sp S)
                  (REG-reach_state S))
             (equal (REG-reach_state (REG-next I S))
                    (and (true-listp I)
                         (natp     (nth *REG/in_value* I))
                         (booleanp (nth *REG/ld_flag* I))
                         (equal (len I) 2))))
    :rule-classes :rewrite)

; - Robustness-related properties
; -------------------------------

;    + fault-injection is actual
  (defthm REG-thm-error
    (implies (REG-Sp S)
             (not (equal (REG-error S) S)))
    :rule-classes ((:forward-chaining :match-free :all
                                      :trigger-terms ((REG-Sp S)))))

;    + an error is corrected after one clock tick if ld_flag = '1'
  (defthm REG-thm-hardened-1
    (implies (and (REG-Sp S)
                  (REG-reach_state S)
                  (true-listp I)
                  (natp     (nth *REG/in_value* I))
                  (booleanp (nth *REG/ld_flag* I))
                  (equal (len I) 2)
                  (nth *REG/ld_flag* I)) ; loading a new input
             (equal (REG-next I (REG-error S))
                    (REG-next I S)))
    :hints (("Goal" :use (:instance REG-error-def2 (x S))))
    :rule-classes :rewrite)

;    + no error is detected when no error occurs
  (defthm REG-thm-hardened-2
    (implies (and (REG-Sp S)
                  (REG-reach_state S))
             (not (REG-e_detect nil S)))
    :rule-classes :rewrite)

;    + no error is detected when an error occurs
  (defthm REG-thm-hardened-3
    (implies (and (REG-Sp S)
                  (REG-reach_state S))
             (not (REG-e_detect nil (REG-error S))))
    :hints (("Goal" :use (:instance REG-error-def2 (x S))))
    :rule-classes :rewrite)
)
