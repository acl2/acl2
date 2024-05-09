; ensure in raw lisp
(acl2::value :q)
(acl2::in-package "ACL2")

; turn off GC and Load messages in GCL
#+akcl (setq si::*notify-gbc* nil)
#+akcl (setq si::*load-verbose* nil)

; check for GCC in GCL
#+gcl (unless (zp (progn (sys-call "gcc" '("-v")) (sys-call-status *the-live-state*)))
              (acl2::or (acl2::cw
                         "${NoMoReSnIp}$~%~@0~%Aborting...~%${SnIpMeHeRe}$~%~@0~%Aborting...~%"
                         "Using this GCL image of ACL2 requires an installation of GCC to be ~
                          available in your PATH as \"gcc\".  Refer to the ACL2s documentation ~
                          page for help (search for `gcc').")
                        (acl2::good-bye)))


; Disable debugger entry in GCL, since ACL2 method doesn't work for
; non-ANSI
#+gcl (in-package 'system)
#+gcl (progn (setq lisp:*break-enable* nil)
(defun break (&optional format-string &rest args &aux message)
  (let ((*print-pretty* nil)
        (*print-level* 4)
        (*print-length* 4)
        (*print-case* :upcase))
       (terpri *error-output*)
    (cond (format-string
           (format *error-output* "~&Break: ")
           (let ((*indent-formatted-output* t))
             (apply 'format *error-output* format-string args))
           (terpri *error-output*)
           (setq message (apply 'format nil format-string args)))
          (t (format *error-output* "~&Break.~%")
             (setq message ""))))
  (break-level message)
  nil)
(defun terminal-interrupt (correctablep)
  (if correctablep
      (cerror "Type :r to resume execution, or :q to quit to top level."
              "Console interrupt.")
      (error "Console interrupt -- cannot continue."))))
#+gcl (in-package "ACL2")

; Disable debugger entry , ACL2 method
(set-debugger-enable :bt) ;harshrc: First it was :bt, then I changed it to :never, then I changed it back to :bt.

; and disable changing the setting (harshrc: Something changed in 6.5??)
;; (ld '((push-untouchable set-debugger-enable-fn t)
;;       (push-untouchable debugger-enable nil)))


; get rid of good-bye comments
; do it here because ld-verbose is untouchable
(f-put-global 'ld-verbose "~sv.  Level ~Fl.  Cbd ~xc.~|Distributed books directory ~xb.~|Type :help for help.~|~%" *the-live-state*)



; fix compilation issue with tracing in windows build of ACL 3.4
#+(and gcl mswindows)
(when (equal (@ acl2-version) "ACL2 Version 3.4")
(defun custom-trace-ppr (direction x &optional evisc-tuple msgp)

; NOTE: The caller for direction :in should first increment state global
; 'trace-level.  This function, however, takes care of decrementing that state
; global if direction is not :in.

; We need to provide all the output that one expects when using a trace
; facility.  Hence the cond clause and the first argument.

; We will keep state global 'trace-level appropriate for printing in both
; directions (:in and :out).

; Warning: Keep this in sync with first-trace-printing-column.

  (when (eq evisc-tuple :no-print)
    (return-from custom-trace-ppr nil))
  (when (eq direction :in)
    (increment-trace-level))
  (let ((trace-level (f-get-global 'trace-level *the-live-state*)))
    (cond ((eq direction :in)

; Originally we incremented the trace level here.  But instead we wait until
; calling trace-ppr, in order to get the spacing to work out.

           (case trace-level
             (1 (princ "1> " *trace-output*))
             (2 (princ "  2> " *trace-output*))
             (3 (princ "    3> " *trace-output*))
             (4 (princ "      4> " *trace-output*))
             (5 (princ "        5> " *trace-output*))
             (6 (princ "          6> " *trace-output*))
             (7 (princ "            7> " *trace-output*))
             (8 (princ "              8> " *trace-output*))
             (9 (princ "                9> " *trace-output*))
             (t (princ (format nil "                  ~s> " trace-level)
                       *trace-output*))))
          (t
           (case trace-level
             (1 (princ "<1 " *trace-output*))
             (2 (princ "  <2 " *trace-output*))
             (3 (princ "    <3 " *trace-output*))
             (4 (princ "      <4 " *trace-output*))
             (5 (princ "        <5 " *trace-output*))
             (6 (princ "          <6 " *trace-output*))
             (7 (princ "            <7 " *trace-output*))
             (8 (princ "              <8 " *trace-output*))
             (9 (princ "                <9 " *trace-output*))
             (t (princ (format nil "                  <~s " trace-level)
                       *trace-output*)))))
    (cond ((eq evisc-tuple :print)
           (format *trace-output* "~s~%" x))
          (t (trace-ppr x evisc-tuple msgp *the-live-state*)))
    (when (not (eq direction :in))
      (f-put-global 'trace-level
                    (1-f trace-level)
                    *the-live-state*))
    (finish-output *trace-output*))))
