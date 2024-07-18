(in-package "X86ISA")

(defparameter *console-stream* nil)

(let* ((socket (ccl::make-socket :connect :passive ;; Listen
                                 :local-host "localhost"
                                 :local-port 6444))
       (stream (ccl::accept-connection socket)))
  (setf *console-stream* stream))

(defun write-tty (c x86)
  (write-char (code-char c) *console-stream*)
  (force-output *console-stream*)
  x86)

(defun read-tty (x86)
  (b* ((c (read-char-no-hang *console-stream*)))
      (mv (if (null c)
            nil
            (char-code c))
          x86)))


#|
; To use Yahya's version of the ACL2 x86 model, do:

;  (ld "resume-linux.lisp")

; > Type :? for other options.
; 1 > :q
;  (:STOP-LD 1)

; TTAG NOTE: Printing of ttag notes has been deferred for the following
; list of ttags:
;   (:UNDEF-FLG :OTHER-NON-DET
;               :INSTRUMENT :INCLUDE-RAW).
; To print the deferred ttag notes:  (ACL2::SHOW-TTAG-NOTES).


; ACL2 Error in ACL2::CHK-ABSSTOBJ-INVARIANTS:  Possible invariance violation
; for an abstract stobj!
; **PROCEED AT YOUR OWN RISK.**
; To proceed, evaluate the following form.
; :CONTINUE-FROM-ILLEGAL-STATE
; See :DOC set-absstobj-debug.
|#
