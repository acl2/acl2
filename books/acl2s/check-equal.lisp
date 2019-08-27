#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "std/util/bstar" :dir :system)

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
|#

(defun fcheck (form state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((er res) (with-output! :on error (trans-eval form 'check state t)))
       ((when (not (equal (cdr res) t)))
        (prog2$
         (cw "~%ACL2s Error in CHECK: The form evaluates to: ~x0, not T!~%"
             (cdr res))
         (mv t nil state))))
    (value '(value-triple :passed))))

(defun fcheck= (form1 form2 state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((er res1) (with-output! :on error (trans-eval form1 'check= state t)))
       ((er res2) (with-output! :on error (trans-eval form2 'check= state t)))
       ((when (not (equal (car res1) (car res2))))
        (prog2$
         (cw "~%ACL2s Error in CHECK=: The forms return a different number or stobj types.~%")
         (mv t nil state)))
       ((when (not (equal (cdr res1) (cdr res2))))
        (prog2$
         (cw "~%ACL2s Error in CHECK=: Check failed (values not equal).~
               ~%First value:  ~x0~
               ~%Second value: ~x1~%" (cdr res1) (cdr res2))
         (mv t nil state))))
    (value '(value-triple :passed))))

#|

(fcheck 1 state)
(fcheck (equal 1 1) state)

(fcheck= 1 2 state)
(fcheck= 1 1 state)

|#

(defmacro check (form)
  `(with-output
    :off :all
    (make-event (fcheck ',form state) :check-expansion t)))

(defmacro check= (form1 form2)
  `(with-output
    :off :all
    (make-event (fcheck= ',form1 ',form2 state) :check-expansion t)))


#|

(check 1)
(check t)
(check (equal 1 1))

(check= (+ 0 1) 1)
(check= 1 2)

(check= (head nil) t)

|#
