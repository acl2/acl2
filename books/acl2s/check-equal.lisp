#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")


;***** CHECK and CHECK= macros for Peter Dillinger & Pete Manolios & Northeastern CSU290 *****

#|

(defmacro check (form)
  `(with-output
    :stack :push
    :off :all
    (make-event
     (with-output
      :stack :pop
     ; (state-global-let*
     ; ((guard-checking-on :none))
      (er-let*
        ((eval-result (acl2::trans-eval
                       '(if ,form
                          (value nil)
                          (er soft 'check "Check failed (returned NIL)."))
                       'check
                       state t)))
        (if (second eval-result)
          (mv t nil state)
          (value '(value-triple :passed)))))
     :check-expansion t)))

(defmacro check= (form1 form2)
  `(with-output
    :stack :push
    :off :all
    (make-event
     (with-output
      :stack :pop
      ;(state-global-let*
      ;((guard-checking-on :none))
      (er-let*
        ((eval-result1 (acl2::trans-eval ',form1 'check= state t))
         (eval-result2 (acl2::trans-eval ',form2 'check= state t)))
        (cond ((not (equal (car eval-result1)
                           (car eval-result2)))
               (er soft 'check=
                   "Forms return different number or stobj types of ~
                    results; thus, they should not be considered equal."))
              ((not (equal (cdr eval-result1)
                           (cdr eval-result2)))
               (er soft 'check=
                   "Check failed (values not equal).~%First value:  ~x0~%~
                    Second value: ~x1" (cdr eval-result1) (cdr eval-result2)))
              (t
               (value '(value-triple :passed))))))
     :check-expansion t)))

|#

(defmacro check (form)
  `(make-event
    (with-output
     :off :all
; (state-global-let*
; ((guard-checking-on :none))
     (er-let*
      ((eval-result (acl2::trans-eval
                     '(if ,form
                          (value nil)
                        (er soft 'check "Check failed (returned NIL)."))
                     'check
                     state t)))
      (if (second eval-result)
          (mv t nil state)
        (value '(value-triple :passed)))))
    :check-expansion t))

(defmacro check= (form1 form2)
  `(make-event
    (with-output
     :off :all
     (er-let*
      ((eval-result1 (acl2::trans-eval ',form1 'check= state t))
       (eval-result2 (acl2::trans-eval ',form2 'check= state t)))
      (cond ((not (equal (car eval-result1)
                         (car eval-result2)))
             (er soft 'check=
                 "Forms return different number or stobj types of ~
                    results; thus, they should not be considered equal."))
            ((not (equal (cdr eval-result1)
                         (cdr eval-result2)))
             (er soft 'check=
                 "Check failed (values not equal).~%First value:  ~x0~%~
                    Second value: ~x1" (cdr eval-result1) (cdr eval-result2)))
            (t (value '(value-triple :passed))))))
    :check-expansion t))
