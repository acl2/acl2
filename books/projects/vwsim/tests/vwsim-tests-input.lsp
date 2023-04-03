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

; Test 1: RC Circuit

(vwsim "../Testing/test-circuits/cirs/rc-circuit.cir")

(time-list rtime)

; Test 2: Four-stage Josephson Transmission Line (JTL)

(vwsim "../Testing/test-circuits/cirs/four-stage-jtl.cir"
       :time-step (* 1/10 *pico*)
       :time-stop (* 100 *pico*))

(time-list rtime)

(set-raw-mode nil)
