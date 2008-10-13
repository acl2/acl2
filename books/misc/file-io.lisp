; Utilities read-list and write-list:

; (Read-list fname ctx state) returns (mv nil lst state) where lst is the list
; of top-level forms in the file named fname.  Except, if there is an error
; then (mv t nil state) is returned.

; (Write-list list fname ctx state) pretty-prints the given list of forms to
; file fname, except that strings are printed without any formatting.

; In each of the above, ctx is generally a symbol used in error messages that
; indicates the caller, e.g., 'top-level.

(in-package "ACL2")

(program)

(set-state-ok t)

(defun collect-objects (list channel state)
  (mv-let (eofp obj state)
	  (read-object channel state)
	  (if eofp
	      (mv (reverse list) state)
	    (collect-objects (cons obj list) channel state))))

; Return (value result) where result is the list of top-level forms in file
; fname:
(defun read-list (fname ctx state)
  (mv-let (channel state)
	  (open-input-channel fname :object state)
          (if channel
              (mv-let (result state)
                      (collect-objects () channel state)
                      (let ((state (close-input-channel channel state)))
                        (value result)))
            (er soft ctx
                "Unable to open file ~s0 for :object input."
                fname))))

(defun pprint-object-or-string (obj channel state)
  (if (stringp obj)
      (princ$ obj channel state)
    (mv-let (erp val state)
            (state-global-let*
             ((write-for-read t))
             (pprogn (ppr2 (ppr1 obj (acl2-print-base) 80 0 state t)
                           0 channel state t)
                     (value nil)))
            (declare (ignore erp val))
            state)))

(defun write-objects (list channel state)
  (if (consp list)
      (pprogn (pprint-object-or-string (car list) channel state)
              (newline channel state)
              (newline channel state)
              (write-objects (cdr list) channel state)
              state)
    state))

(defun write-list-body-fn (bangp)
  `(mv-let (channel state)
           ,(if bangp
                '(open-output-channel! fname :character state)
              '(open-output-channel fname :character state))
           (if channel
               (mv-let
                (col state)
                (fmt1 "Writing file ~x0~%" (list (cons #\0 fname))
                      0 (standard-co state) state nil)
                (declare (ignore col))
                (let ((state (write-objects list channel state)))
                  (pprogn (close-output-channel channel state)
                          (value :invisible))))
             (er soft ctx
                 "Unable to open file ~s0 for :character output."
                 fname))))

(defmacro write-list-body (bangp)
  (write-list-body-fn bangp))

; Pretty-print the given list of forms to file fname, except that strings are
; printed without any formatting.
(defun write-list (list fname ctx state)
  (write-list-body nil))

(defmacro write-list! (list fname ctx &optional ttag)

; A non-nil ttag must be supplied, of course, unless there is already an active
; ttag at the point where write-list! is called.

  (let ((trans-eval-form `(trans-eval '(let ((list ,list)
                                             (fname ,fname)
                                             (ctx ,ctx))
                                         ,(write-list-body-fn t))
                                      ,ctx
                                      state)))

    `(er-progn ,(if ttag
                    `(progn (defttag ,ttag) (progn! ,trans-eval-form))
                  trans-eval-form)
               (value :invisible))))

; (Downcase form) causes the execution of form but where printing is in
; :downcase mode.  Form must return an error triple.
(defmacro downcase (form)
  `(state-global-let*
    ((print-case :downcase set-print-case))
    ,form))

; Same as write-list above, but where printing is down in downcase mode:
(defun write-list-downcase (list fname ctx state)
  (downcase (write-list list fname ctx state)))
