; -----------------------------------------------------------------------------
; |                                                                           |
; | Description : ATM-TMR defines an Automatic Teller Machine control         |
; |               system that uses a TMR FSM for each register, and has:      |
; |               o Seven inputs :                                            |
; |                   - inc        : a card has been inserted                 |
; |                   - reset      : cancel button                            |
; |                   - val        : validation (after entering the code)     |
; |                   - done_op    : banking operations completed             |
; |                   - take       : card taken                               |
; |                   - cc         : card code reader output                  |
; |                   - codin      : user code reader output                  |
; |               o Four outputs :                                            |
; |                   - outc       : eject the card                           |
; |                   - keep       : don't eject the card                     |
; |                   - start_op   : banking operations can start             |
; |                   - e_detect   : error detection flag                     |
; |                                                                           |
; | The transition and output functions are automatically computed thanks     |
; | to our VSYML tool.                                                        |
; -----------------------------------------------------------------------------

(IN-PACKAGE "ACL2")
(include-book "register-TMR")

; -------------------------
; definition of the ATM FSM
; -------------------------

(defspec ATM-TMR
; - Signatures
  (((ATMv2-Sp          *) => *) ; State predicate
   ((ATMv2-next      * *) => *) ; transition function
   ((ATMv2-start_op  * *) => *) ; start_op output function
   ((ATMv2-keep      * *) => *) ; keep output function
   ((ATMv2-outc      * *) => *) ; outc output function
   ((ATMv2-e_detect  * *) => *) ; e_detect output function
   ((ATMv2-reach_state *) => *) ; reachable states
   ((ATMv2-error       *) => *)); error in a ATM

; - Definition of type work.local_type.FSM_state
(local (defun ATMv2-FSM_statep (x)
         (or (equal x "init")
	     (equal x "card_in")
	     (equal x "test_code")
	     (equal x "code_error")
	     (equal x "code_ok")
	     (equal x "card_out"))))

; - Constants
  (local (defconst *ATMv2/n_register*    0))
  (local (defconst *ATMv2/ok_register*   1))
  (local (defconst *ATMv2/code_register* 2))
  (local (defconst *ATMv2/c_state* 3))
  (defconst *ATMv2/reset* 0)
  (defconst *ATMv2/inc* 1)
  (defconst *ATMv2/cc* 2)
  (defconst *ATMv2/codin* 3)
  (defconst *ATMv2/val* 4)
  (defconst *ATMv2/done_op* 5)
  (defconst *ATMv2/take* 6)
  (local (defconst *ATMv2/max_try*  3))

; -Instances
  (local (encapsulate          ; for register n
          (((ATMv2-n_reg-error *) => *))
          (defun ATMv2-n_reg-Sp (S) (TMR-Sp S))
          (defun ATMv2-n_reg-next (I S) (TMR-next I S))
          (defun ATMv2-n_reg-out_value (I S) (TMR-out_value I S))
          (defun ATMv2-n_reg-e_detect (I S) (TMR-e_detect I S))
          (defun ATMv2-n_reg-reach_state (S) (TMR-reach_state S))
          (local (defun ATMv2-n_reg-error (S) (TMR-error S)))
          (definstance TMR n_register
            :functional-substitution ((TMR-error ATMv2-n_reg-error))
            :rule-classes :rewrite)))

  (local (encapsulate           ; for register ok
          (((ATMv2-ok_reg-error *) => *))
          (defun ATMv2-ok_reg-Sp (S) (TMR-Sp S))
          (defun ATMv2-ok_reg-next (I S) (TMR-next I S))
          (defun ATMv2-ok_reg-out_value (I S) (TMR-out_value I S))
          (defun ATMv2-ok_reg-e_detect (I S) (TMR-e_detect I S))
          (defun ATMv2-ok_reg-reach_state (S) (TMR-reach_state S))
          (local (defun ATMv2-ok_reg-error (x) (TMR-error x)))
          (definstance TMR ok_register
            :functional-substitution ((TMR-error ATMv2-ok_reg-error))
            :rule-classes :rewrite)))

  (local (encapsulate            ; for register code
          (((ATMv2-code_reg-error *) => *))
          (defun ATMv2-code_reg-Sp (S) (TMR-Sp S))
          (defun ATMv2-code_reg-next (I S) (TMR-next I S))
          (defun ATMv2-code_reg-out_value (I S) (TMR-out_value I S))
          (defun ATMv2-code_reg-e_detect (I S) (TMR-e_detect I S))
          (defun ATMv2-code_reg-reach_state (S) (TMR-reach_state S))
          (local (defun ATMv2-code_reg-error (x) (TMR-error x)))
          (definstance TMR code_register
            :functional-substitution ((TMR-error ATMv2-code_reg-error))
            :rule-classes :rewrite)))

; - Witnesses (not "toy" witnesses, actual definitions for this ATM)
;    + Definition of ATM States
  (local (defun ATMv2-Sp (x)
           (and (true-listp x)
		(ATMv2-n_reg-Sp    (nth *ATMv2/n_register*    x))
		(ATMv2-ok_reg-Sp   (nth *ATMv2/ok_register*   x))
		(ATMv2-code_reg-Sp (nth *ATMv2/code_register* x))
		(ATMv2-FSM_statep  (nth *ATMv2/c_state* x))
		(equal (len x) 4))))

;    + Definition of the transition function
  (local (defun ATMv2-next (current_input current_state)
           (if (and (ATMv2-Sp current_state)
                    (true-listp current_input)
                    (booleanp (nth *ATMv2/reset*   current_input))
                    (booleanp (nth *ATMv2/inc*     current_input))
                    (natp     (nth *ATMv2/cc*      current_input))
                    (natp     (nth *ATMv2/codin*   current_input))
                    (booleanp (nth *ATMv2/val*     current_input))
                    (booleanp (nth *ATMv2/done_op* current_input))
                    (booleanp (nth *ATMv2/take*    current_input))
                    (equal (len current_input) 7))
               (list
                ; ATM/n_register
                (ATMv2-n_reg-next
                 (list
                  ; in_value
                  (cond ((and (equal (nth *ATMv2/c_state* current_state)
                                     "init")
                              (nth *ATMv2/inc* current_input))
                         1)
                        ((and (equal (nth *ATMv2/c_state* current_state)
                                     "test_code")
                              (not (equal
                               (ATMv2-code_reg-out_value nil
                                (nth *ATMv2/code_register* current_state))
                               (ATMv2-ok_reg-out_value nil
                                (nth *ATMv2/ok_register* current_state))))
                              (< (ATMv2-n_reg-out_value nil
                                  (nth *ATMv2/n_register* current_state))
                                 *ATMv2/max_try*))
                         (1+ (ATMv2-n_reg-out_value nil
                              (nth *ATMv2/n_register* current_state))))
                        (T
                         (ATMv2-n_reg-out_value nil
                          (nth *ATMv2/n_register* current_state))))
                  ; ld_flag
                  (or (and (equal (nth *ATMv2/c_state* current_state)
                                  "init")
                           (nth *ATMv2/inc* current_input))
                      (and (equal (nth *ATMv2/c_state* current_state)
                                  "test_code")
                           (not (equal
                                 (ATMv2-code_reg-out_value nil
                                  (nth *ATMv2/code_register* current_state))
                                 (ATMv2-ok_reg-out_value nil
                                  (nth *ATMv2/ok_register* current_state))))
                           (< (ATMv2-n_reg-out_value nil
                               (nth *ATMv2/n_register* current_state))
                              *ATMv2/max_try*))))
                 (nth *ATMv2/n_register* current_state))
                ; ATM/ok_register
                (ATMv2-ok_reg-next
                 (list
                  ; in_value
                  (cond ((and (equal (nth *ATMv2/c_state* current_state)
                                     "init")
                              (nth *ATMv2/inc* current_input))
                         (nth *ATMv2/cc* current_input))
                        ((equal (nth *ATMv2/c_state* current_state)
                                "code_error")
                         0)
                        ((and (equal (nth *ATMv2/c_state* current_state)
                                     "card_out")
                              (nth *ATMv2/take* current_input))
                         0)
                        (T
                         (ATMv2-ok_reg-out_value nil
                          (nth *ATMv2/ok_register* current_state))))
                  ; ld_flag
                  (or (and (equal (nth *ATMv2/c_state* current_state)
                                  "init")
                           (nth *ATMv2/inc* current_input))
                      (equal (nth *ATMv2/c_state* current_state)
                             "code_error")
                      (and (equal (nth *ATMv2/c_state* current_state)
                                  "card_out")
                           (nth *ATMv2/take* current_input))))
                 (nth *ATMv2/ok_register* current_state))
                ; ATM/code_register
                (ATMv2-code_reg-next
                 (list
                  ; in_value
                  (cond ((and (equal (nth *ATMv2/c_state* current_state)
                                     "card_in")
                              (nth *ATMv2/val* current_input)
                              (not (nth *ATMv2/reset* current_input)))
                         (nth *ATMv2/codin* current_input))
                        ((equal (nth *ATMv2/c_state* current_state)
                                "code_error")
                         0)
                        ((and (equal (nth *ATMv2/c_state* current_state)
                                     "card_out")
                              (nth *ATMv2/take* current_input))
                         0)
                        (T
                         (ATMv2-code_reg-out_value nil
                          (nth *ATMv2/code_register* current_state))))
                  ; ld_flag
                  (or (and (equal (nth *ATMv2/c_state* current_state)
                                  "card_in")
                           (nth *ATMv2/val* current_input)
                           (not (nth *ATMv2/reset* current_input)))
                      (equal (nth *ATMv2/c_state* current_state)
                             "code_error")
                      (and (equal (nth *ATMv2/c_state* current_state)
                                  "card_out")
                           (nth *ATMv2/take* current_input))))
                 (nth *ATMv2/code_register* current_state))
                ; ATM/c_state
                (cond ((equal (nth *ATMv2/c_state* current_state)
                              "init") ; case c_state = init
                       (if (nth *ATMv2/inc* current_input)
                           "card_in"
                           "init"))
                      ((equal (nth *ATMv2/c_state* current_state)
                              "card_in") ; case c_state = card_in
                       (cond ((or (nth *ATMv2/reset* current_input)
                                  (or (ATMv2-n_reg-e_detect nil
                                       (nth *ATMv2/n_register* current_state))
                                      (ATMv2-ok_reg-e_detect nil
                                       (nth *ATMv2/ok_register* current_state))
                                      (ATMv2-code_reg-e_detect nil
                                       (nth *ATMv2/code_register* current_state))))
                              "card_out")
                             ((nth *ATMv2/val* current_input)
                              "test_code")
                             (T
                              "card_in")))
                      ((equal (nth *ATMv2/c_state* current_state)
                              "test_code") ; case c_state = test_code
                       (cond ((or (ATMv2-n_reg-e_detect nil
                                   (nth *ATMv2/n_register* current_state))
                                  (ATMv2-ok_reg-e_detect nil
                                   (nth *ATMv2/ok_register* current_state))
                                  (ATMv2-code_reg-e_detect nil
                                   (nth *ATMv2/code_register* current_state)))
                              "card_out")
                             ((equal (ATMv2-code_reg-out_value nil
                                      (nth *ATMv2/code_register* current_state))
                                     (ATMv2-ok_reg-out_value nil
                                      (nth *ATMv2/ok_register* current_state)))
                              "code_ok")
                             ((< (ATMv2-n_reg-out_value nil
                                   (nth *ATMv2/n_register* current_state))
                                  *ATMv2/max_try*)
                              "card_in")
                             (T
                              "code_error")))
                      ((equal (nth *ATMv2/c_state* current_state)
                              "code_error") ; case c_state = code_error
                       "init")
                      ((equal (nth *ATMv2/c_state* current_state)
                              "code_ok") ; case c_state = code_ok
                       (if (or (nth *ATMv2/reset* current_input)
                               (nth *ATMv2/done_op* current_input)
                               (or (ATMv2-n_reg-e_detect nil
                                    (nth *ATMv2/n_register* current_state))
                                   (ATMv2-ok_reg-e_detect nil
                                    (nth *ATMv2/ok_register* current_state))
                                   (ATMv2-code_reg-e_detect nil
                                    (nth *ATMv2/code_register* current_state))))
                           "card_out"
                           "code_ok"))
                      (T ; case others (card_out)
                       (if (nth *ATMv2/take* current_input)
                           "init"
                           "card_out")))
                )
               "error")))

;    + Definition of the function that gives the start_op output signal
  (local (defun ATMv2-start_op (current_input current_state)
           (if (and (ATMv2-Sp current_state)
                    (true-listp current_input)
                    (booleanp (nth 0 current_input)) ; reset
                    (booleanp (nth 1 current_input)) ; done_op
                    (equal (len current_input) 2))
               (or (and (equal (nth *ATMv2/c_state* current_state)
                               "test_code")
                        (equal (ATMv2-code_reg-out_value nil
                                (nth *ATMv2/code_register* current_state))
                               (ATMv2-ok_reg-out_value nil
                                (nth *ATMv2/ok_register* current_state)))
                        (not (or (ATMv2-n_reg-e_detect nil
                                  (nth *ATMv2/n_register* current_state))
                                 (ATMv2-ok_reg-e_detect nil
                                  (nth *ATMv2/ok_register* current_state))
                                 (ATMv2-code_reg-e_detect nil
                                  (nth *ATMv2/code_register* current_state)))))
                   (and (equal (nth *ATMv2/c_state* current_state)
                               "code_ok")
                        (not (nth 0 current_input))
                        (not (nth 1 current_input))
                        (not (or (ATMv2-n_reg-e_detect nil
                                  (nth *ATMv2/n_register* current_state))
                                 (ATMv2-ok_reg-e_detect nil
                                  (nth *ATMv2/ok_register* current_state))
                                 (ATMv2-code_reg-e_detect nil
                                  (nth *ATMv2/code_register* current_state))))))
               "error")))

;    + Definition of the function that gives the keep output signal
  (local (defun ATMv2-keep (current_input current_state)
           (if (and (ATMv2-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (and (equal (nth *ATMv2/c_state* current_state)
                           "test_code")
                    (not (equal (ATMv2-code_reg-out_value nil
                                 (nth *ATMv2/code_register* current_state))
                                (ATMv2-ok_reg-out_value nil
                                 (nth *ATMv2/ok_register* current_state))))
                    (>= (ATMv2-n_reg-out_value nil
                         (nth *ATMv2/n_register* current_state))
                        *ATMv2/max_try*)
                    (not (or (ATMv2-n_reg-e_detect nil
                              (nth *ATMv2/n_register* current_state))
                             (ATMv2-ok_reg-e_detect nil
                              (nth *ATMv2/ok_register* current_state))
                             (ATMv2-code_reg-e_detect nil
                              (nth *ATMv2/code_register* current_state)))))
               "error")))

;    + Definition of the function that gives the outc output signal
  (local (defun ATMv2-outc (current_input current_state)
           (if (and (ATMv2-Sp current_state)
                    (true-listp current_input)
                    (booleanp (nth 0 current_input)) ; reset
                    (booleanp (nth 1 current_input)) ; done_op
                    (equal (len current_input) 2))
               (or (and (equal (nth *ATMv2/c_state* current_state)
                               "code_ok")
                        (or (nth 0 current_input)
                            (nth 1 current_input)
                            (or (ATMv2-n_reg-e_detect nil
                                 (nth *ATMv2/n_register* current_state))
                                (ATMv2-ok_reg-e_detect nil
                                 (nth *ATMv2/ok_register* current_state))
                                (ATMv2-code_reg-e_detect nil
                                 (nth *ATMv2/code_register* current_state)))))
                   (and (equal (nth *ATMv2/c_state* current_state)
                               "card_in")
                        (or (nth 0 current_input)
                            (or (ATMv2-n_reg-e_detect nil
                                 (nth *ATMv2/n_register* current_state))
                                (ATMv2-ok_reg-e_detect nil
                                 (nth *ATMv2/ok_register* current_state))
                                (ATMv2-code_reg-e_detect nil
                                 (nth *ATMv2/code_register* current_state)))))
                   (and (equal (nth *ATMv2/c_state* current_state)
                               "test_code")
                        (or (ATMv2-n_reg-e_detect nil
                             (nth *ATMv2/n_register* current_state))
                            (ATMv2-ok_reg-e_detect nil
                             (nth *ATMv2/ok_register* current_state))
                            (ATMv2-code_reg-e_detect nil
                             (nth *ATMv2/code_register* current_state)))))
               "error")))

;    + Definition of the function that gives the e_detect output signal
  (local (defun ATMv2-e_detect (current_input current_state)
           (if (and (ATMv2-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (or (ATMv2-n_reg-e_detect nil
                    (nth *ATMv2/n_register* current_state))
                   (ATMv2-ok_reg-e_detect nil
                    (nth *ATMv2/ok_register* current_state))
                   (ATMv2-code_reg-e_detect nil
                    (nth *ATMv2/code_register* current_state)))
               "error")))

;    + Definition of ATM reachable states
  (local (defun ATMv2-reach_state (S)
           (and (ATMv2-Sp S)
                (ATMv2-n_reg-reach_state (nth *ATMv2/n_register* S))
                (ATMv2-ok_reg-reach_state (nth *ATMv2/ok_register* S))
                (ATMv2-code_reg-reach_state (nth *ATMv2/code_register* S)))))

;    + Definition of an error in a ATM FSM
;      * The error is located in register n
  (local (defun ATMv2-inject1 (x)
           (if (ATMv2-Sp x)
               (list (ATMv2-n_reg-error (nth *ATMv2/n_register* x))
                     (nth *ATMv2/ok_register*   x)
                     (nth *ATMv2/code_register* x)
                     (nth *ATMv2/c_state* x)
                     )
               "error")))

;      * Or the error is located in register ok
  (local (defun ATMv2-inject2 (x)
           (if (ATMv2-Sp x)
               (list (nth *ATMv2/n_register* x)
                     (ATMv2-ok_reg-error (nth *ATMv2/ok_register* x))
                     (nth *ATMv2/code_register* x)
                     (nth *ATMv2/c_state* x)
                     )
               "error")))

;      * Or the error is located in register code
  (local (defun ATMv2-inject3 (x)
           (if (ATMv2-Sp x)
               (list (nth *ATMv2/n_register* x)
                     (nth *ATMv2/ok_register* x)
                     (ATMv2-code_reg-error (nth *ATMv2/code_register* x))
                     (nth *ATMv2/c_state* x)
                     )
               "error")))

;      * Definition of the error model
  (local (encapsulate
          (((ATMv2-error *) => *))
          (local (defun ATMv2-error (x) (ATMv2-inject1 x)))
          (defthm ATMv2-error-type1
            (equal (ATMv2-Sp (ATMv2-error x))
                   (ATMv2-Sp x)))
          (defthm ATMv2-error-type2
            (implies (not (ATMv2-Sp x))
                     (equal (ATMv2-error x) "error")))
          (defthm ATMv2-error-def1
            (implies (ATMv2-Sp x)
                     (not (equal (ATMv2-error x) x))))
          (defthm ATMv2-error-def2   ; the error can be located in any of the 3 registers
            (or (equal (ATMv2-error x)
                       (ATMv2-inject1 x))
                (equal (ATMv2-error x)
                       (ATMv2-inject2 x))
                (equal (ATMv2-error x)
                       (ATMv2-inject3 x)))
            :hints (("Goal" :in-theory (disable ATMv2-Sp)))
            :rule-classes nil)))

; - Typing properties
; -------------------

;    + Sp is a predicate
  (defthm ATMv2-thm-Sp-type
    (booleanp (ATMv2-Sp S))
    :rule-classes ((:type-prescription :typed-term (ATMv2-Sp S))))

;    + "error" is not a Sp (speeds up proofs)
  (defthm ATMv2-thm-Sp-error
    (not (ATMv2-Sp "error"))
    :rule-classes :rewrite)

;    + Output of the transition function
  (defthm ATMv2-thm-next-type1
    (implies (ATMv2-Sp S)
             (equal (ATMv2-Sp (ATMv2-next I S))
                    (and (true-listp I)
                         (booleanp (nth *ATMv2/reset*   I))
                         (booleanp (nth *ATMv2/inc*     I))
                         (natp     (nth *ATMv2/cc*      I))
                         (natp     (nth *ATMv2/codin*   I))
                         (booleanp (nth *ATMv2/val*     I))
                         (booleanp (nth *ATMv2/done_op* I))
                         (booleanp (nth *ATMv2/take*    I))
                         (equal (len I) 7))))
    :rule-classes :rewrite)

;    + Input of the transition function
  (defthm ATMv2-thm-next-type2
    (implies (or (not (ATMv2-Sp S))
                 (not (true-listp I))
                 (not (booleanp (nth *ATMv2/reset*   I)))
                 (not (booleanp (nth *ATMv2/inc*     I)))
                 (not (natp     (nth *ATMv2/cc*      I)))
                 (not (natp     (nth *ATMv2/codin*   I)))
                 (not (booleanp (nth *ATMv2/val*     I)))
                 (not (booleanp (nth *ATMv2/done_op* I)))
                 (not (booleanp (nth *ATMv2/take*    I)))
                 (not (equal (len I) 7)))
             (equal (ATMv2-next I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the start_op output signal
  (defthm ATMv2-thm-start_op-type1
    (implies (ATMv2-Sp S)
             (equal (booleanp (ATMv2-start_op I S))
                    (and (true-listp I)
                         (booleanp (nth 0 I)) ; reset
                         (booleanp (nth 1 I)) ; done_op
                         (equal (len I) 2))))
    :rule-classes :rewrite)

;    + Input of the function that gives the start_op output signal
  (defthm ATMv2-thm-start_op-type2
    (implies (or (not (ATMv2-Sp S))
                 (not (true-listp I))
                 (not (booleanp (nth 0 I)))
                 (not (booleanp (nth 1 I)))
                 (not (equal (len I) 2)))
             (equal (ATMv2-start_op I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the keep output signal
  (defthm ATMv2-thm-keep-type1
    (implies (ATMv2-Sp S)
             (equal (booleanp (ATMv2-keep I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the keep output signal
  (defthm ATMv2-thm-keep-type2
    (implies (or (not (ATMv2-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (ATMv2-keep I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the outc output signal
  (defthm ATMv2-thm-outc-type1
    (implies (ATMv2-Sp S)
             (equal (booleanp (ATMv2-outc I S))
                    (and (true-listp I)
                         (booleanp (nth 0 I)) ; reset
                         (booleanp (nth 1 I)) ; done_op
                         (equal (len I) 2))))
    :rule-classes :rewrite)

;    + Input of the function that gives the outc output signal
  (defthm ATMv2-thm-outc-type2
    (implies (or (not (ATMv2-Sp S))
                 (not (true-listp I))
                 (not (booleanp (nth 0 I)))
                 (not (booleanp (nth 1 I)))
                 (not (equal (len I) 2)))
             (equal (ATMv2-outc I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the e_detect output signal
  (defthm ATMv2-thm-e_detect-type1
    (implies (ATMv2-Sp S)
             (equal (booleanp (ATMv2-e_detect I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the e_detect output signal
  (defthm ATMv2-thm-e_detect-type2
    (implies (or (not (ATMv2-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (ATMv2-e_detect I S)
                    "error"))
    :rule-classes :rewrite)

;    + reach_state is a predicate
  (defthm ATMv2-thm-reach_state-type
    (booleanp (ATMv2-reach_state S))
    :rule-classes ((:type-prescription :typed-term (ATMv2-reach_state S))))

;    + Output of error is a Sp
  (defthm ATMv2-thm-error-type1
    (equal (ATMv2-Sp (ATMv2-error S))
           (ATMv2-Sp S))
    :rule-classes :rewrite)

;    + Input of error is a Sp
  (defthm ATMv2-thm-error-type2
    (implies (not (ATMv2-Sp S))
             (equal (ATMv2-error S)
                    "error"))
    :rule-classes :rewrite)

;    + the transition function returns a reachable state
  (defthm ATMv2-thm-reach_state
    (implies (and (ATMv2-Sp S)
                  (ATMv2-reach_state S))
             (equal (ATMv2-reach_state (ATMv2-next I S))
                    (and (true-listp I)
                         (booleanp (nth *ATMv2/reset*   I))
                         (booleanp (nth *ATMv2/inc*     I))
                         (natp     (nth *ATMv2/cc*      I))
                         (natp     (nth *ATMv2/codin*   I))
                         (booleanp (nth *ATMv2/val*     I))
                         (booleanp (nth *ATMv2/done_op* I))
                         (booleanp (nth *ATMv2/take*    I))
                         (equal (len I) 7))))
    :rule-classes :rewrite)

; - Robustness-related properties
; -------------------------------

;    + fault-injection is actual
  (defthm ATMv2-thm-error
    (implies (ATMv2-Sp S)
             (not (equal (ATMv2-error S) S)))
    :rule-classes ((:forward-chaining :match-free :all
                                      :trigger-terms ((ATMv2-Sp S)))))

;    + an error does not change the symbolic state
  (local (defthm ATMv2-thm-symbolicstate-unchanged
    (implies (ATMv2-Sp S)
             (equal (nth *ATMv2/c_state* (ATMv2-error S))
                    (nth *ATMv2/c_state* S)))
    :hints (("Goal" :use (:instance ATMv2-error-def2 (x S))))
    :rule-classes :rewrite))

;    + an error is corrected after one clock tick
  (defthm ATMv2-thm-hardened-1
    (implies (and (ATMv2-Sp S)
                  (ATMv2-reach_state S)
                  (true-listp I)
                  (booleanp (nth *ATMv2/reset*   I))
                  (booleanp (nth *ATMv2/inc*     I))
                  (natp     (nth *ATMv2/cc*      I))
                  (natp     (nth *ATMv2/codin*   I))
                  (booleanp (nth *ATMv2/val*     I))
                  (booleanp (nth *ATMv2/done_op* I))
                  (booleanp (nth *ATMv2/take*    I))
                  (equal (len I) 7))
             (equal (ATMv2-next I (ATMv2-error S))
                    (ATMv2-next I S)))
    :hints (("Goal" :use (:instance ATMv2-error-def2 (x S))
                    :in-theory (disable booleanp)))
    :rule-classes :rewrite)

;    + the start_op output signal is unchanged when an error occurs
  (defthm ATMv2-thm-hardened-2
    (implies (and (ATMv2-Sp S)
                  (true-listp I)
                  (booleanp (nth 0 I))
                  (booleanp (nth 1 I))
                  (equal (len I) 2)
                  (ATMv2-reach_state S))
             (equal (ATMv2-start_op I (ATMv2-error S))
		    (ATMv2-start_op I S)))
    :hints (("Goal" :use (:instance ATMv2-error-def2 (x S))))
    :rule-classes :rewrite)

;    + the keep output signal is unchanged when an error occurs
  (defthm ATMv2-thm-hardened-3
    (implies (and (ATMv2-Sp S)
                  (ATMv2-reach_state S))
             (equal (ATMv2-keep nil (ATMv2-error S))
                    (ATMv2-keep nil S)))
    :hints (("Goal" :use (:instance ATMv2-error-def2 (x S))))
    :rule-classes :rewrite)

;    + the outc output signal is unchanged when an error occurs
  (defthm ATMv2-thm-hardened-4
    (implies (and (ATMv2-Sp S)
                  (true-listp I)
                  (booleanp (nth 0 I))
                  (booleanp (nth 1 I))
                  (equal (len I) 2)
                  (ATMv2-reach_state S))
             (equal (ATMv2-outc I (ATMv2-error S))
                    (ATMv2-outc I S)))
    :hints (("Goal" :use (:instance ATMv2-error-def2 (x S))))
    :rule-classes :rewrite)
)

; -------------------------------------------------
; Then, robustness-related properties over n cycles
; -------------------------------------------------

; Definition of a well-formed trace
(defun SPEC-ATMv2-Ip (x)
  (and (true-listp x)
       (booleanp (nth *ATMv2/reset*   x))
       (booleanp (nth *ATMv2/inc*     x))
       (natp     (nth *ATMv2/cc*      x))
       (natp     (nth *ATMv2/codin*   x))
       (booleanp (nth *ATMv2/val*     x))
       (booleanp (nth *ATMv2/done_op* x))
       (booleanp (nth *ATMv2/take*    x))
       (equal (len x) 7)))
; - An input trace is a list of inputs
(defun SPEC-ATMv2-Trace-Ip (x)
  (and (true-listp x)
       (or (null x)
           (and (SPEC-ATMv2-Ip (car x))
                (SPEC-ATMv2-Trace-Ip (cdr x))))))

; - Definition of the recursive application of the transition function
(defun SPEC-ATMv2-rec-next (input_trace initial_state)
  (if (and (ATMv2-Sp initial_state)
           (SPEC-ATMv2-Trace-Ip input_trace))
      (if (null input_trace)
          initial_state
          (ATMv2-next (car input_trace)
                      (SPEC-ATMv2-rec-next (cdr input_trace)
                                           initial_state)))
      "error"))

; Typing properties
; -----------------

; - Output of SPEC-ATMv2-rec-next is a Sp
(defthm SPEC-ATMv2-thm-rec-next-type1
  (implies (ATMv2-Sp initial_state)
           (equal (ATMv2-Sp (SPEC-ATMv2-rec-next input_trace initial_state))
                  (SPEC-ATMv2-Trace-Ip input_trace)))
  :rule-classes :rewrite)

; Output of SPEC-ATMv2-rec-next is a reach_state
(defthm SPEC-ATMv2-thm-rec-next-reach_state
  (implies (and (ATMv2-Sp initial_state) ; for all state
                (ATMv2-reach_state initial_state) ; being a reachable state
                (SPEC-ATMv2-Trace-Ip input_trace)) ; and all input trace
           (ATMv2-reach_state (SPEC-ATMv2-rec-next input_trace initial_state)))
  :rule-classes :rewrite)

; Input of SPEC-ATMv2-rec-next
(defthm SPEC-ATMv2-thm-rec-next-type2
  (implies (or (not (ATMv2-Sp S))
               (not (SPEC-ATMv2-Trace-Ip I)))
           (equal (SPEC-ATMv2-rec-next I S)
                  "error"))
  :rule-classes :rewrite)

; Robustness-related props
; ------------------------

; - If an error is injected in a ATMv2 FSM after n clock ticks,
;   it will be corrected one clock cycle later
(defthm SPEC-ATMv2-test1
  (implies
   (and (ATMv2-Sp initial_state) ; for all state
        (ATMv2-reach_state initial_state) ; being a reachable state
        (SPEC-ATMv2-Trace-Ip input_trace) ; and all input trace
        (SPEC-ATMv2-Ip last_input)) ; and all last input
   (equal (ATMv2-next last_input
                      (ATMv2-error (SPEC-ATMv2-rec-next input_trace
                                                        initial_state)))
          (ATMv2-next last_input
                                   (SPEC-ATMv2-rec-next input_trace
                                                        initial_state))))
  :rule-classes nil)

; - If an error is injected in a ATMv2 FSM after n clock ticks,
; the start_op output signal keeps its value on the next clock tick
(defthm SPEC-ATMv2-test2
  (implies
   (and (ATMv2-Sp initial_state) ; for all state
        (ATMv2-reach_state initial_state) ; being a reachable state
        (SPEC-ATMv2-Trace-Ip input_trace) ; and all input trace
        (true-listp last_input) ; and all last start_op input
        (booleanp (nth 0 last_input))
        (booleanp (nth 1 last_input))
        (equal (len last_input) 2))
   (equal (ATMv2-start_op last_input
                          (ATMv2-error (SPEC-ATMv2-rec-next input_trace
                                                            initial_state)))
          (ATMv2-start_op last_input
                                       (SPEC-ATMv2-rec-next input_trace
                                                            initial_state))))
  :rule-classes nil)

; - If an error is injected in a ATMv2 FSM after n clock ticks,
; the keep output signal keeps its value on the next clock tick
(defthm SPEC-ATMv2-test3
  (implies
   (and (ATMv2-Sp initial_state) ; for all state
        (ATMv2-reach_state initial_state) ; being a reachable state
        (SPEC-ATMv2-Trace-Ip input_trace)) ; and all input trace
   (equal (ATMv2-keep nil
                      (ATMv2-error (SPEC-ATMv2-rec-next input_trace
                                                        initial_state)))
          (ATMv2-keep nil
                                   (SPEC-ATMv2-rec-next input_trace
                                                        initial_state))))
  :rule-classes nil)

; - If an error is injected in a ATMv2 FSM after n clock ticks,
; the outc output signal keeps its value on the next clock tick
(defthm SPEC-ATMv2-test4
  (implies
   (and (ATMv2-Sp initial_state) ; for all state
        (ATMv2-reach_state initial_state) ; being a reachable state
        (SPEC-ATMv2-Trace-Ip input_trace) ; and all input trace
        (true-listp last_input) ; and all last input
        (booleanp (nth 0 last_input))
        (booleanp (nth 1 last_input))
        (equal (len last_input) 2))
   (equal (ATMv2-outc last_input
                      (ATMv2-error (SPEC-ATMv2-rec-next input_trace
                                                        initial_state)))
          (ATMv2-outc last_input
                                   (SPEC-ATMv2-rec-next input_trace
                                                        initial_state))))
  :rule-classes nil)
