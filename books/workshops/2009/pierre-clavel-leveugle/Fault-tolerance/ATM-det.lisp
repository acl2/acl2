; -----------------------------------------------------------------------------
; |                                                                           |
; | Description : ATM-det defines an Automatic Teller Machine control         |
; |               system that uses a REG-det FSM for each register, and has:  |
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
(include-book "register-det")

; -------------------------
; definition of the ATM FSM
; -------------------------

(defspec ATM-det
; - Signatures
  (((ATMv1-Sp          *) => *) ; State predicate
   ((ATMv1-next      * *) => *) ; transition function
   ((ATMv1-start_op  * *) => *) ; start_op output function
   ((ATMv1-keep      * *) => *) ; keep output function
   ((ATMv1-outc      * *) => *) ; outc output function
   ((ATMv1-e_detect  * *) => *) ; e_detect output function
   ((ATMv1-reach_state *) => *) ; reachable states
   ((ATMv1-error       *) => *)); error in a ATM

; - Definition of type work.local_type.FSM_state
(local (defun ATMv1-FSM_statep (x)
         (or (equal x "init")
	     (equal x "card_in")
	     (equal x "test_code")
	     (equal x "code_error")
	     (equal x "code_ok")
	     (equal x "card_out"))))

; - Constants
  (local (defconst *ATMv1/n_register*    0))
  (local (defconst *ATMv1/ok_register*   1))
  (local (defconst *ATMv1/code_register* 2))
  (local (defconst *ATMv1/c_state* 3))
  (defconst *ATMv1/reset* 0)
  (defconst *ATMv1/inc* 1)
  (defconst *ATMv1/cc* 2)
  (defconst *ATMv1/codin* 3)
  (defconst *ATMv1/val* 4)
  (defconst *ATMv1/done_op* 5)
  (defconst *ATMv1/take* 6)
  (local (defconst *ATMv1/max_try*  3))

; -Instances
  (local (encapsulate            ; for register n
          (((ATMv1-n_reg-error *) => *))
          (defun ATMv1-n_reg-Sp (S) (REG-det-Sp S))
          (defun ATMv1-n_reg-next (I S) (REG-det-next I S))
          (defun ATMv1-n_reg-out_value (I S) (REG-det-out_value I S))
          (defun ATMv1-n_reg-e_detect (I S) (REG-det-e_detect I S))
          (defun ATMv1-n_reg-reach_state (S) (REG-det-reach_state S))
          (local (defun ATMv1-n_reg-error (S) (REG-det-error S)))
          (definstance REG-det n_register
            :functional-substitution ((REG-det-error ATMv1-n_reg-error))
            :rule-classes :rewrite)))

  (local (encapsulate            ; for register ok
          (((ATMv1-ok_reg-error *) => *))
          (defun ATMv1-ok_reg-Sp (S) (REG-det-Sp S))
          (defun ATMv1-ok_reg-next (I S) (REG-det-next I S))
          (defun ATMv1-ok_reg-out_value (I S) (REG-det-out_value I S))
          (defun ATMv1-ok_reg-e_detect (I S) (REG-det-e_detect I S))
          (defun ATMv1-ok_reg-reach_state (S) (REG-det-reach_state S))
          (local (defun ATMv1-ok_reg-error (x) (REG-det-error x)))
          (definstance REG-det ok_register
            :functional-substitution ((REG-det-error ATMv1-ok_reg-error))
            :rule-classes :rewrite)))

  (local (encapsulate            ; for register code
          (((ATMv1-code_reg-error *) => *))
          (defun ATMv1-code_reg-Sp (S) (REG-det-Sp S))
          (defun ATMv1-code_reg-next (I S) (REG-det-next I S))
          (defun ATMv1-code_reg-out_value (I S) (REG-det-out_value I S))
          (defun ATMv1-code_reg-e_detect (I S) (REG-det-e_detect I S))
          (defun ATMv1-code_reg-reach_state (S) (REG-det-reach_state S))
          (local (defun ATMv1-code_reg-error (x) (REG-det-error x)))
          (definstance REG-det code_register
            :functional-substitution ((REG-det-error ATMv1-code_reg-error))
            :rule-classes :rewrite)))

; - Witnesses (not "toy" witnesses, actual definitions for this ATM)
;    + Definition of ATM states
  (local (defun ATMv1-Sp (x)
           (and
            (true-listp x)
            (ATMv1-n_reg-Sp    (nth *ATMv1/n_register*    x))
            (ATMv1-ok_reg-Sp   (nth *ATMv1/ok_register*   x))
            (ATMv1-code_reg-Sp (nth *ATMv1/code_register* x))
            (ATMv1-FSM_statep  (nth *ATMv1/c_state* x))
            (equal (len x) 4))))

;    + Definition of the transition function
  (local (defun ATMv1-next (current_input current_state)
           (if (and (ATMv1-Sp current_state)
                    (true-listp current_input)
                    (booleanp (nth *ATMv1/reset*   current_input))
                    (booleanp (nth *ATMv1/inc*     current_input))
                    (natp     (nth *ATMv1/cc*      current_input))
                    (natp     (nth *ATMv1/codin*   current_input))
                    (booleanp (nth *ATMv1/val*     current_input))
                    (booleanp (nth *ATMv1/done_op* current_input))
                    (booleanp (nth *ATMv1/take*    current_input))
                    (equal (len current_input) 7))
               (list
                ; ATM/n_register
                (ATMv1-n_reg-next
                 (list
                  ; in_value
                  (cond ((and (equal (nth *ATMv1/c_state* current_state)
                                     "init")
                              (nth *ATMv1/inc* current_input))
                         1)
                        ((and (equal (nth *ATMv1/c_state* current_state)
                                     "test_code")
                              (not (equal
                               (ATMv1-code_reg-out_value nil
                                (nth *ATMv1/code_register* current_state))
                               (ATMv1-ok_reg-out_value nil
                                (nth *ATMv1/ok_register* current_state))))
                              (< (ATMv1-n_reg-out_value nil
                                  (nth *ATMv1/n_register* current_state))
                                 *ATMv1/max_try*))
                         (1+ (ATMv1-n_reg-out_value nil
                              (nth *ATMv1/n_register* current_state))))
                        (T
                         (ATMv1-n_reg-out_value nil
                          (nth *ATMv1/n_register* current_state))))
                  ; ld_flag
                  (or (and (equal (nth *ATMv1/c_state* current_state)
                                  "init")
                           (nth *ATMv1/inc* current_input))
                      (and (equal (nth *ATMv1/c_state* current_state)
                                  "test_code")
                           (not (equal
                                 (ATMv1-code_reg-out_value nil
                                  (nth *ATMv1/code_register* current_state))
                                 (ATMv1-ok_reg-out_value nil
                                  (nth *ATMv1/ok_register* current_state))))
                           (< (ATMv1-n_reg-out_value nil
                               (nth *ATMv1/n_register* current_state))
                              *ATMv1/max_try*))))
                 (nth *ATMv1/n_register* current_state))
                ; ATM/ok_register
                (ATMv1-ok_reg-next
                 (list
                  ; in_value
                  (cond ((and (equal (nth *ATMv1/c_state* current_state)
                                     "init")
                              (nth *ATMv1/inc* current_input))
                         (nth *ATMv1/cc* current_input))
                        ((equal (nth *ATMv1/c_state* current_state)
                                "code_error")
                         0)
                        ((and (equal (nth *ATMv1/c_state* current_state)
                                     "card_out")
                              (nth *ATMv1/take* current_input))
                         0)
                        (T
                         (ATMv1-ok_reg-out_value nil
                          (nth *ATMv1/ok_register* current_state))))
                  ; ld_flag
                  (or (and (equal (nth *ATMv1/c_state* current_state)
                                  "init")
                           (nth *ATMv1/inc* current_input))
                      (equal (nth *ATMv1/c_state* current_state)
                             "code_error")
                      (and (equal (nth *ATMv1/c_state* current_state)
                                  "card_out")
                           (nth *ATMv1/take* current_input))))
                 (nth *ATMv1/ok_register* current_state))
                ; ATM/code_register
                (ATMv1-code_reg-next
                 (list
                  ; in_value
                  (cond ((and (equal (nth *ATMv1/c_state* current_state)
                                     "card_in")
                              (nth *ATMv1/val* current_input)
                              (not (nth *ATMv1/reset* current_input)))
                         (nth *ATMv1/codin* current_input))
                        ((equal (nth *ATMv1/c_state* current_state)
                                "code_error")
                         0)
                        ((and (equal (nth *ATMv1/c_state* current_state)
                                     "card_out")
                              (nth *ATMv1/take* current_input))
                         0)
                        (T
                         (ATMv1-code_reg-out_value nil
                          (nth *ATMv1/code_register* current_state))))
                  ; ld_flag
                  (or (and (equal (nth *ATMv1/c_state* current_state)
                                  "card_in")
                           (nth *ATMv1/val* current_input)
                           (not (nth *ATMv1/reset* current_input)))
                      (equal (nth *ATMv1/c_state* current_state)
                             "code_error")
                      (and (equal (nth *ATMv1/c_state* current_state)
                                  "card_out")
                           (nth *ATMv1/take* current_input))))
                 (nth *ATMv1/code_register* current_state))
                ; ATM/c_state
                (cond ((equal (nth *ATMv1/c_state* current_state)
                              "init") ; case c_state = init
                       (if (nth *ATMv1/inc* current_input)
                           "card_in"
                           "init"))
                      ((equal (nth *ATMv1/c_state* current_state)
                              "card_in") ; case c_state = card_in
                       (cond ((or (nth *ATMv1/reset* current_input)
                                  (or (ATMv1-n_reg-e_detect nil
                                       (nth *ATMv1/n_register* current_state))
                                      (ATMv1-ok_reg-e_detect nil
                                       (nth *ATMv1/ok_register* current_state))
                                      (ATMv1-code_reg-e_detect nil
                                       (nth *ATMv1/code_register* current_state))))
                              "card_out")
                             ((nth *ATMv1/val* current_input)
                              "test_code")
                             (T
                              "card_in")))
                      ((equal (nth *ATMv1/c_state* current_state)
                              "test_code") ; case c_state = test_code
                       (cond ((or (ATMv1-n_reg-e_detect nil
                                   (nth *ATMv1/n_register* current_state))
                                  (ATMv1-ok_reg-e_detect nil
                                   (nth *ATMv1/ok_register* current_state))
                                  (ATMv1-code_reg-e_detect nil
                                   (nth *ATMv1/code_register* current_state)))
                              "card_out")
                             ((equal (ATMv1-code_reg-out_value nil
                                      (nth *ATMv1/code_register* current_state))
                                     (ATMv1-ok_reg-out_value nil
                                      (nth *ATMv1/ok_register* current_state)))
                              "code_ok")
                             ((< (ATMv1-n_reg-out_value nil
                                   (nth *ATMv1/n_register* current_state))
                                  *ATMv1/max_try*)
                              "card_in")
                             (T
                              "code_error")))
                      ((equal (nth *ATMv1/c_state* current_state)
                              "code_error") ; case c_state = code_error
                       "init")
                      ((equal (nth *ATMv1/c_state* current_state)
                              "code_ok") ; case c_state = code_ok
                       (if (or (nth *ATMv1/reset* current_input)
                               (nth *ATMv1/done_op* current_input)
                               (or (ATMv1-n_reg-e_detect nil
                                    (nth *ATMv1/n_register* current_state))
                                   (ATMv1-ok_reg-e_detect nil
                                    (nth *ATMv1/ok_register* current_state))
                                   (ATMv1-code_reg-e_detect nil
                                    (nth *ATMv1/code_register* current_state))))
                           "card_out"
                           "code_ok"))
                      (T ; case others (card_out)
                       (if (nth *ATMv1/take* current_input)
                           "init"
                           "card_out")))
                )
               "error")))

;    + Definition of the function that gives the start_op output signal
  (local (defun ATMv1-start_op (current_input current_state)
           (if (and (ATMv1-Sp current_state)
                    (true-listp current_input)
                    (booleanp (nth 0 current_input)) ; reset
                    (booleanp (nth 1 current_input)) ; done_op
                    (equal (len current_input) 2))
               (or (and (equal (nth *ATMv1/c_state* current_state)
                               "test_code")
                        (equal (ATMv1-code_reg-out_value nil
                                (nth *ATMv1/code_register* current_state))
                               (ATMv1-ok_reg-out_value nil
                                (nth *ATMv1/ok_register* current_state)))
                        (not (or (ATMv1-n_reg-e_detect nil
                                  (nth *ATMv1/n_register* current_state))
                                 (ATMv1-ok_reg-e_detect nil
                                  (nth *ATMv1/ok_register* current_state))
                                 (ATMv1-code_reg-e_detect nil
                                  (nth *ATMv1/code_register* current_state)))))
                   (and (equal (nth *ATMv1/c_state* current_state)
                               "code_ok")
                        (not (nth 0 current_input))
                        (not (nth 1 current_input))
                        (not (or (ATMv1-n_reg-e_detect nil
                                  (nth *ATMv1/n_register* current_state))
                                 (ATMv1-ok_reg-e_detect nil
                                  (nth *ATMv1/ok_register* current_state))
                                 (ATMv1-code_reg-e_detect nil
                                  (nth *ATMv1/code_register* current_state))))))
               "error")))

;    + Definition of the function that gives the keep output signal
  (local (defun ATMv1-keep (current_input current_state)
           (if (and (ATMv1-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (and (equal (nth *ATMv1/c_state* current_state)
                           "test_code")
                    (not (equal (ATMv1-code_reg-out_value nil
                                 (nth *ATMv1/code_register* current_state))
                                (ATMv1-ok_reg-out_value nil
                                 (nth *ATMv1/ok_register* current_state))))
                    (>= (ATMv1-n_reg-out_value nil
                         (nth *ATMv1/n_register* current_state))
                        *ATMv1/max_try*)
                    (not (or (ATMv1-n_reg-e_detect nil
                              (nth *ATMv1/n_register* current_state))
                             (ATMv1-ok_reg-e_detect nil
                              (nth *ATMv1/ok_register* current_state))
                             (ATMv1-code_reg-e_detect nil
                              (nth *ATMv1/code_register* current_state)))))
               "error")))

;    + Definition of the function that gives the outc output signal
  (local (defun ATMv1-outc (current_input current_state)
           (if (and (ATMv1-Sp current_state)
                    (true-listp current_input)
                    (booleanp (nth 0 current_input)) ; reset
                    (booleanp (nth 1 current_input)) ; done_op
                    (equal (len current_input) 2))
               (or (and (equal (nth *ATMv1/c_state* current_state)
                               "code_ok")
                        (or (nth 0 current_input)
                            (nth 1 current_input)
                            (or (ATMv1-n_reg-e_detect nil
                                 (nth *ATMv1/n_register* current_state))
                                (ATMv1-ok_reg-e_detect nil
                                 (nth *ATMv1/ok_register* current_state))
                                (ATMv1-code_reg-e_detect nil
                                 (nth *ATMv1/code_register* current_state)))))
                   (and (equal (nth *ATMv1/c_state* current_state)
                               "card_in")
                        (or (nth 0 current_input)
                            (or (ATMv1-n_reg-e_detect nil
                                 (nth *ATMv1/n_register* current_state))
                                (ATMv1-ok_reg-e_detect nil
                                 (nth *ATMv1/ok_register* current_state))
                                (ATMv1-code_reg-e_detect nil
                                 (nth *ATMv1/code_register* current_state)))))
                   (and (equal (nth *ATMv1/c_state* current_state)
                               "test_code")
                        (or (ATMv1-n_reg-e_detect nil
                             (nth *ATMv1/n_register* current_state))
                            (ATMv1-ok_reg-e_detect nil
                             (nth *ATMv1/ok_register* current_state))
                            (ATMv1-code_reg-e_detect nil
                             (nth *ATMv1/code_register* current_state)))))
               "error")))

;    + Definition of the function that gives the e_detect output signal
  (local (defun ATMv1-e_detect (current_input current_state)
           (if (and (ATMv1-Sp current_state)
                    (true-listp current_input)
                    (equal (len current_input) 0))
               (or (ATMv1-n_reg-e_detect nil
                    (nth *ATMv1/n_register* current_state))
                   (ATMv1-ok_reg-e_detect nil
                    (nth *ATMv1/ok_register* current_state))
                   (ATMv1-code_reg-e_detect nil
                    (nth *ATMv1/code_register* current_state)))
               "error")))

;    + Definition of ATM reachable states
  (local (defun ATMv1-reach_state (S)
           (and (ATMv1-Sp S)
                (ATMv1-n_reg-reach_state (nth *ATMv1/n_register* S))
                (ATMv1-ok_reg-reach_state (nth *ATMv1/ok_register* S))
                (ATMv1-code_reg-reach_state (nth *ATMv1/code_register* S)))))

;    + Definition of an error in a ATM FSM
;      * The error is located in register n
  (local (defun ATMv1-inject1 (x)
           (if (ATMv1-Sp x)
               (list (ATMv1-n_reg-error (nth *ATMv1/n_register* x))
                     (nth *ATMv1/ok_register*   x)
                     (nth *ATMv1/code_register* x)
                     (nth *ATMv1/c_state* x)
                     )
               "error")))
;      * Or the error is located in register ok
  (local (defun ATMv1-inject2 (x)
           (if (ATMv1-Sp x)
               (list (nth *ATMv1/n_register* x)
                     (ATMv1-ok_reg-error (nth *ATMv1/ok_register* x))
                     (nth *ATMv1/code_register* x)
                     (nth *ATMv1/c_state* x)
                     )
               "error")))
;      * Or the error is located in register code
  (local (defun ATMv1-inject3 (x)
           (if (ATMv1-Sp x)
               (list (nth *ATMv1/n_register* x)
                     (nth *ATMv1/ok_register* x)
                     (ATMv1-code_reg-error (nth *ATMv1/code_register* x))
                     (nth *ATMv1/c_state* x)
                     )
               "error")))

;      * Definition of the error model
  (local (encapsulate
          (((ATMv1-error *) => *))
          (local (defun ATMv1-error (x) (ATMv1-inject1 x)))
          (defthm ATMv1-error-type1
            (equal (ATMv1-Sp (ATMv1-error x))
                   (ATMv1-Sp x)))
          (defthm ATMv1-error-type2
            (implies (not (ATMv1-Sp x))
                     (equal (ATMv1-error x) "error")))
          (defthm ATMv1-error-def1
            (implies (ATMv1-Sp x)
                     (not (equal (ATMv1-error x) x))))
          (defthm ATMv1-error-def2    ; the error can be located in any of the 3 registers
            (or (equal (ATMv1-error x)
                       (ATMv1-inject1 x))
                (equal (ATMv1-error x)
                       (ATMv1-inject2 x))
                (equal (ATMv1-error x)
                       (ATMv1-inject3 x)))
            :hints (("Goal" :in-theory (disable ATMv1-Sp)))
            :rule-classes nil)))

; - Typing properties
; -------------------

;    + Sp is a predicate
  (defthm ATMv1-thm-Sp-type
    (booleanp (ATMv1-Sp S))
    :rule-classes ((:type-prescription :typed-term (ATMv1-Sp S))))

;    + "error" is not a Sp (speeds up proofs)
  (defthm ATMv1-thm-Sp-error
    (not (ATMv1-Sp "error"))
    :rule-classes :rewrite)

;    + Output of the transition function
  (defthm ATMv1-thm-next-type1
    (implies (ATMv1-Sp S)
             (equal (ATMv1-Sp (ATMv1-next I S))
                    (and (true-listp I)
                         (booleanp (nth *ATMv1/reset*   I))
                         (booleanp (nth *ATMv1/inc*     I))
                         (natp     (nth *ATMv1/cc*      I))
                         (natp     (nth *ATMv1/codin*   I))
                         (booleanp (nth *ATMv1/val*     I))
                         (booleanp (nth *ATMv1/done_op* I))
                         (booleanp (nth *ATMv1/take*    I))
                         (equal (len I) 7))))
    :rule-classes :rewrite)

;    + Input of the transition function
  (defthm ATMv1-thm-next-type2
    (implies (or (not (ATMv1-Sp S))
                 (not (true-listp I))
                 (not (booleanp (nth *ATMv1/reset*   I)))
                 (not (booleanp (nth *ATMv1/inc*     I)))
                 (not (natp     (nth *ATMv1/cc*      I)))
                 (not (natp     (nth *ATMv1/codin*   I)))
                 (not (booleanp (nth *ATMv1/val*     I)))
                 (not (booleanp (nth *ATMv1/done_op* I)))
                 (not (booleanp (nth *ATMv1/take*    I)))
                 (not (equal (len I) 7)))
             (equal (ATMv1-next I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the start_op output signal
  (defthm ATMv1-thm-start_op-type1
    (implies (ATMv1-Sp S)
             (equal (booleanp (ATMv1-start_op I S))
                    (and (true-listp I)
                         (booleanp (nth 0 I)) ; reset
                         (booleanp (nth 1 I)) ; done_op
                         (equal (len I) 2))))
    :rule-classes :rewrite)

;    + Input of the function that gives the start_op output signal
  (defthm ATMv1-thm-start_op-type2
    (implies (or (not (ATMv1-Sp S))
                 (not (true-listp I))
                 (not (booleanp (nth 0 I)))
                 (not (booleanp (nth 1 I)))
                 (not (equal (len I) 2)))
             (equal (ATMv1-start_op I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the keep output signal
  (defthm ATMv1-thm-keep-type1
    (implies (ATMv1-Sp S)
             (equal (booleanp (ATMv1-keep I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the keep output signal
  (defthm ATMv1-thm-keep-type2
    (implies (or (not (ATMv1-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (ATMv1-keep I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the outc output signal
  (defthm ATMv1-thm-outc-type1
    (implies (ATMv1-Sp S)
             (equal (booleanp (ATMv1-outc I S))
                    (and (true-listp I)
                         (booleanp (nth 0 I)) ; reset
                         (booleanp (nth 1 I)) ; done_op
                         (equal (len I) 2))))
    :rule-classes :rewrite)

;    + Input of the function that gives the outc output signal
  (defthm ATMv1-thm-outc-type2
    (implies (or (not (ATMv1-Sp S))
                 (not (true-listp I))
                 (not (booleanp (nth 0 I)))
                 (not (booleanp (nth 1 I)))
                 (not (equal (len I) 2)))
             (equal (ATMv1-outc I S)
                    "error"))
    :rule-classes :rewrite)

;    + Output of the function that gives the e_detect output signal
  (defthm ATMv1-thm-e_detect-type1
    (implies (ATMv1-Sp S)
             (equal (booleanp (ATMv1-e_detect I S))
                    (and (true-listp I)
                         (equal (len I) 0))))
    :rule-classes :rewrite)

;    + Input of the function that gives the e_detect output signal
  (defthm ATMv1-thm-e_detect-type2
    (implies (or (not (ATMv1-Sp S))
                 (not (true-listp I))
                 (not (equal (len I) 0)))
             (equal (ATMv1-e_detect I S)
                    "error"))
    :rule-classes :rewrite)

;    + reach_state is a predicate
  (defthm ATMv1-thm-reach_state-type
    (booleanp (ATMv1-reach_state S))
    :rule-classes ((:type-prescription :typed-term (ATMv1-reach_state S))))

;    + Output of error is a Sp
  (defthm ATMv1-thm-error-type1
    (equal (ATMv1-Sp (ATMv1-error S))
           (ATMv1-Sp S))
    :rule-classes :rewrite)

;    + Input of error is a Sp
  (defthm ATMv1-thm-error-type2
    (implies (not (ATMv1-Sp S))
             (equal (ATMv1-error S)
                    "error"))
    :rule-classes :rewrite)

;    + the transition function returns a reachable state
  (defthm ATMv1-thm-reach_state
    (implies (and (ATMv1-Sp S)
                  (ATMv1-reach_state S))
             (equal (ATMv1-reach_state (ATMv1-next I S))
                    (and (true-listp I)
                         (booleanp (nth *ATMv1/reset*   I))
                         (booleanp (nth *ATMv1/inc*     I))
                         (natp     (nth *ATMv1/cc*      I))
                         (natp     (nth *ATMv1/codin*   I))
                         (booleanp (nth *ATMv1/val*     I))
                         (booleanp (nth *ATMv1/done_op* I))
                         (booleanp (nth *ATMv1/take*    I))
                         (equal (len I) 7))))
    :rule-classes :rewrite)

; - Robustness-related properties
; -------------------------------

;    + fault-injection is actual
  (defthm ATMv1-thm-error
    (implies (ATMv1-Sp S)
             (not (equal (ATMv1-error S) S)))
    :rule-classes ((:forward-chaining :match-free :all
                                      :trigger-terms ((ATMv1-Sp S)))))

;    + an error does not change the symbolic state
  (local (defthm ATMv1-thm-symbolicstate-unchanged
    (implies (ATMv1-Sp S)
             (equal (nth *ATMv1/c_state* (ATMv1-error S))
                    (nth *ATMv1/c_state* S)))
    :hints (("Goal" :use (:instance ATMv1-error-def2 (x S))))
    :rule-classes :rewrite))

;    + the start_op output signal never holds after an error
  (defthm ATMv1-thm-hardened-1
    (implies (and (ATMv1-Sp S)
                  (true-listp I)
                  (booleanp (nth 0 I))
                  (booleanp (nth 1 I))
                  (equal (len I) 2)
                  (ATMv1-reach_state S))
             (not (ATMv1-start_op I (ATMv1-error S))))
    :hints (("Goal" :use (:instance ATMv1-error-def2 (x S))))
    :rule-classes :rewrite)

;    + no error is detected when no error occurs
  (defthm ATMv1-thm-hardened-2
    (implies (and (ATMv1-Sp S)
                  (ATMv1-reach_state S)
                  (true-listp I)
                  (equal (len I) 0))
             (not (ATMv1-e_detect I S)))
    :rule-classes :rewrite)

;    + an error is detected when an error occurs
  (defthm ATMv1-thm-hardened-3
    (implies (and (ATMv1-Sp S)
                  (ATMv1-reach_state S)
                  (true-listp I)
                  (equal (len I) 0))
             (ATMv1-e_detect I (ATMv1-error S)))
    :hints (("Goal" :use (:instance ATMv1-error-def2 (x S))))
    :rule-classes :rewrite)
)

; -------------------------------------------------
; Then, robustness-related properties over n cycles
; -------------------------------------------------

; Definition of a well-formed trace

; - An input is defined by this seven inputs
(defun SPEC-ATMv1-Ip (x)
  (and (true-listp x)
       (booleanp (nth *ATMv1/reset*   x))
       (booleanp (nth *ATMv1/inc*     x))
       (natp     (nth *ATMv1/cc*      x))
       (natp     (nth *ATMv1/codin*   x))
       (booleanp (nth *ATMv1/val*     x))
       (booleanp (nth *ATMv1/done_op* x))
       (booleanp (nth *ATMv1/take*    x))
       (equal (len x) 7)))
; - An input trace is a list of inputs
(defun SPEC-ATMv1-Trace-Ip (x)
  (and (true-listp x)
       (or (null x)
           (and (SPEC-ATMv1-Ip (car x))
                (SPEC-ATMv1-Trace-Ip (cdr x))))))


; Definition of the recursive application of the transition function
(defun SPEC-ATMv1-rec-next (input_trace initial_state)
  (if (and (ATMv1-Sp initial_state)
           (SPEC-ATMv1-Trace-Ip input_trace))
      (if (null input_trace)
          initial_state
          (ATMv1-next (car input_trace)
                      (SPEC-ATMv1-rec-next (cdr input_trace)
                                           initial_state)))
      "error"))

; Typing properties
; -----------------

; - Output of SPEC-ATMv1-rec-next is a Sp
(defthm SPEC-ATMv1-thm-rec-next-type1
  (implies (ATMv1-Sp initial_state)
           (equal (ATMv1-Sp (SPEC-ATMv1-rec-next input_trace initial_state))
                  (SPEC-ATMv1-Trace-Ip input_trace)))
  :rule-classes ((:rewrite)))

; Output of SPEC-ATMv1-rec-next is a reach_state
(defthm SPEC-ATMv1-thm-rec-next-reach_state
  (implies (and (ATMv1-Sp initial_state) ; for all state
                (ATMv1-reach_state initial_state) ; being a reachable state
                (SPEC-ATMv1-Trace-Ip input_trace)) ; and all input trace
           (ATMv1-reach_state (SPEC-ATMv1-rec-next input_trace initial_state)))
  :rule-classes ((:rewrite)))

; Input of SPEC-ATMv1-rec-next
(defthm SPEC-ATMv1-thm-rec-next-type2
  (implies (or (not (ATMv1-Sp S))
               (not (SPEC-ATMv1-Trace-Ip I)))
           (equal (SPEC-ATMv1-rec-next I S)
                  "error"))
  :rule-classes ((:rewrite)))

; Robustness-related props
; ------------------------

; - If an error is injected in a ATMv1 FSM after n clock ticks,
; access to the bank account will not been granted on the next clock tick
(defthm SPEC-ATMv1-test1
  (implies
   (and (ATMv1-Sp initial_state) ; for all state
        (ATMv1-reach_state initial_state) ; being a reachable state
        (SPEC-ATMv1-Trace-Ip input_trace) ; and all input trace
        (true-listp last_input) ; and all last start_op input
        (booleanp (nth 0 last_input))
        (booleanp (nth 1 last_input))
        (equal (len last_input) 2))
   (not (ATMv1-start_op last_input
                        (ATMv1-error (SPEC-ATMv1-rec-next input_trace
                                                          initial_state)))))
  :rule-classes nil)

; - If no error is injected in a ATMv1 FSM after n clock ticks,
; no error is detected
(defthm SPEC-ATMv1-test2
  (implies
   (and (ATMv1-Sp initial_state) ; for all state
        (ATMv1-reach_state initial_state) ; being a reachable state
        (SPEC-ATMv1-Trace-Ip input_trace)) ; and all input trace
   (not (ATMv1-e_detect nil (SPEC-ATMv1-rec-next input_trace
                                                 initial_state))))
   :rule-classes nil)

; - If an error is injected in a ATMv1 FSM after n clock ticks,
; an error is detected
(defthm SPEC-ATMv1-test3
  (implies
   (and (ATMv1-Sp initial_state) ; for all state
        (ATMv1-reach_state initial_state) ; being a reachable state
        (SPEC-ATMv1-Trace-Ip input_trace)) ; and all input trace
   (ATMv1-e_detect nil (ATMv1-error (SPEC-ATMv1-rec-next input_trace
                                                         initial_state))))
   :rule-classes nil)

