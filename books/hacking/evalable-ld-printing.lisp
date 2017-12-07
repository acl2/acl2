; evalable-ld-printing.lisp - Print LD results in "evalable" way, as provided
; by "evalable-printing" book.
;
; To activate, include this book and assign a non-nil value to the state
; global EVALABLE-LD-PRINTINGP, as in
;   (assign evalable-ld-printingp t)
;
; If ld-post-eval-print is :command-conventions, we do not make error
; triple output evalable.  To make error triple output looks especially
; unique, I recommend making it look like a comment:
;   (assign triple-print-prefix "; ")
;
; Requires a trust tag :evalable-ld-printing
;
; Peter C. Dillinger, Northeastern University, 2008

(in-package "ACL2")

(program)
(set-state-ok t)

(defun evalable-ld-printingp (state)
  (and (f-boundp-global 'evalable-ld-printingp state)
       (f-get-global 'evalable-ld-printingp state)))

(include-book "misc/evalable-printing" :dir :system)


(defttag :evalable-ld-printing)

(include-book "hacker")
(progn+all-ttags-allowed
 (include-book "defcode" :ttags ((defcode)))
 (include-book "subsumption")
 (include-book "raw")
 )
(subsume-ttags-since-defttag)

(modify-raw-defun acl2::ld-print-results original-ld-print-results (trans-ans state)
  (if (or (not (acl2::live-state-p state))
 ; Matt K. mod: make acl2::output-in-infixp call conditional on #+acl2infix, to
 ; match ACL2 sources.
          #+acl2-infix
          (acl2::output-in-infixp state)
          (not (evalable-ld-printingp state)))
    (original-ld-print-results trans-ans state)
    (let* ((output-channel (standard-co state))
           (flg (ld-post-eval-print state))
           (stobjs-out (car trans-ans))
           (valx (cdr trans-ans)))
      #-(or gcl cmu sbcl lispworks)
      (when (acl2::raw-mode-p state)
            (acl2::format (acl2::get-output-stream-from-channel output-channel) "~&"))
      (cond
       ((null flg) state)
       ((and (eq flg :command-conventions)
             (equal (length stobjs-out) 3)
             (eq (car stobjs-out) nil)
             (eq (caddr stobjs-out) 'state))
        (cond
         ((eq (cadr valx) :invisible)
          state)
         (t
          (pprogn
           (acl2::princ$ (if (stringp (f-get-global 'acl2::triple-print-prefix state))
                     (f-get-global 'acl2::triple-print-prefix state)
                     "")
                   output-channel state)
           (let ((col (if (stringp (f-get-global 'acl2::triple-print-prefix state))
                        (length (f-get-global 'acl2::triple-print-prefix state))
                        0)))
             (acl2::ppr (cadr valx) col output-channel state nil))
           (acl2::newline output-channel state)))))
     ((equal (length stobjs-out) 1)
      (pprogn
       (acl2::ppr (car (make-evalable-with-stobjs (list valx) stobjs-out)) 0 output-channel state nil)
       (acl2::newline output-channel state)))
     (t
      (pprogn
       (acl2::ppr (cons 'mv (make-evalable-with-stobjs valx stobjs-out)) 0 output-channel state nil)
       (acl2::newline output-channel state)))))))
