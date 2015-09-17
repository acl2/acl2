;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;;SMT-interpreter formats the results

(in-package "ACL2")
(include-book "SMT-run")
(include-book "config")
(defttag :tshell)

;; ;; parse-counter-example
;; (defun parse-counter-example (ce-str)
;;   "parse-counter-example: parse a counter example string returned by Z3"
;;   ())

;; ;; fire-session
;; (defun fire-session (lines)
;;   ()
;;   )

;; SMT-interpreter
;; If failed, one needs to fire off a raw lisp session
;; and bind all variables with values.
;; Need to tell user informations on how to leave the
;; session.
(defun SMT-interpreter (filename smt-config)
  "SMT-intepreter: get the result returned from calling SMT procedure"
  (mv-let (exit-status lines)
          (SMT-run filename smt-config)
	  (cond 
		((not (equal exit-status 0))
		 (cw "Z3 failure: ~q0" lines))
		(t (if (equal (car lines) "proved")
           (let ((cmd (concatenate 'string "rm -f " filename)))
             (mv-let (exit-status-rm lines-rm)
                     (time$ (tshell-call cmd
                                         :print t
                                         :save t)
                            :msg "; rm -f: `~s0`: ~st sec, ~sa bytes~%"
                            :args (list cmd))
                     (if (equal exit-status-rm 0)
                         t
                       (er hard? 'top-level "Error(SMT-interpreter): Remove file error.~% ~q0~%" lines-rm))))
         ;;(fire-session lines)
         (cw "~q0" lines)
         ))))
  )
