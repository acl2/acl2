; vwsim-tests-input.lsp                           Vivek & Warren

; This file contains the tests to run when the VWSIM source is updated
; in the ACL2 books.

(with-output
  :off :all
  :gag-mode nil
  (ld "../driver.lsp"
      :ld-prompt nil
      :ld-verbose nil
      :ld-pre-eval-print nil
      :ld-post-eval-print nil))

; Routines to convert double-float numbers, first to single-float
; numbers, and then to rational numbers.  This, we hope, makes the
; ACL2 comparison-check machinery satisified.

(defun coerce-list-to-sf (l)
  (if (atom l)
      nil
    (let* ((el (car l))
           (new-el (if (nump el)
                       (rationalize (coerce el 'single-float))
                     el)))
      (cons new-el (coerce-list-to-sf (cdr l))))))

(defun coerce-list-of-list-to-sf (l)
  (if (atom l)
      nil
    (let ((el (car l)))
      (cons (coerce-list-to-sf el)
            (coerce-list-of-list-to-sf (cdr l))))))

(defmacro vw-output-test ()
; This macro produces the voltage and phase for every node, and the
; voltage across, current through, and phase across every device.
  `(mv-let
     (result state)
     (vw-output-all)
     (mv (coerce-list-of-list-to-sf result)
         state)))

(setq *read-default-float-format* 'single-float)

; Test 1: RC Circuit

(vwsim "../Testing/test-circuits/cirs/rc-circuit.cir")

(vw-output-test)

; Test 2: Four-stage Josephson Transmission Line (JTL)

(vwsim "../Testing/test-circuits/cirs/four-stage-jtl.cir"
       :time-step (* 1/10 *pico*)
       :time-stop (* 100 *pico*))

(vw-output-test)

(set-raw-mode nil)
