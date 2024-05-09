
; vw-eval-raw.lsp                         Matt, Vivek, Warren

; This file provides a mode for evaluating expressions involving
; floating point numbers (actually double-precision floats) in
; raw-mode (or raw Lisp).  One can switch into and out of this mode.

; Evaluate (load "vw-eval-raw.lsp") _after_ evaluating the forms in
; vw-eval.lisp, for example by LDing or including that book.  This
; process should change our evaluation mechanism to use floating-point
; operations instead of rational operations.

; Possible enhancements to make:

; - Improve how VW-EVAL finds functions defined in "vw-eval.lisp":
;   - Traverse PROGN and ENCAPSULATE.
;   - Expand macros.
;   - Deal with MAKE-EVENT.

; - Add helpful output.

; - Add interrupt protection.

; - Load compiled file instead of "vw-eval.lisp".  Not needed for "ccl" and "sbcl".

; - Allow the use of raw-mode (by redefining more than LP).

(in-package "ACL2")

(defparameter *vw-eval-book*
  (file-namestring
   (merge-pathnames "vw-eval.lisp" *load-truename* nil)))

(defvar *vw-eval-raw-p* nil) ; Boolean-valued

(defun install-vw-eval (raw-p)
  (cond ((eq raw-p *vw-eval-raw-p*) ; No change
         nil)
        (t
         (if raw-p
             ;; Note the nasty dynamic binding to *features* which is
             ;; in force at the time of the LOAD.
             (let ((*features* (cons :raw *features*)))
               (load *vw-eval-book*))
           ;; Here, no extension to *features*, so normal operation
           (load *vw-eval-book*))
         ;; Record the value of RAW-P
         (setq *vw-eval-raw-p* raw-p))))

(defvar *old-lp* (symbol-function 'lp))

(defun lp ()
  (when *vw-eval-raw-p*
    (format t "Executing ~s.~%" '(install-vw-eval nil))
    (install-vw-eval nil))
  (funcall *old-lp*))
