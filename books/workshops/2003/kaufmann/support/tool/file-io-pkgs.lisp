(in-package "ACL2")

; There are two ways in which we want to print forms respecting packages.  When
; generating definitions originally, we may prefer to view the symbols as
; package-less (although they will actually be ACL2 or built-in symbols) and
; simply port the entire form to a new package, which might not even exist.  In
; the other case we have a form that is considered to have real symbols in it,
; and we want to print out an equal form that however has a package prefix.  So
; we have write-list-into-pkgs, which prints pkg-name::form when presented with
; (:pkg pkg-name . form), and write-list-using-pkgs, which prints form as an
; equal form using pkg-name::form'.

(include-book "misc/file-io" :dir :system)

(set-state-ok t)
(program)

(defun change-pkg-for-form (form state)
  (if (and (consp form)
           (member-eq (car form) '(defun defthm))
           (consp (cdr form))
           (symbolp (cadr form)))
      (let ((package-name (symbol-package-name (cadr form))))
        (if (equal package-name "ACL2")
            (value nil)
          (in-package-fn package-name state)))
    (value nil)))

(mutual-recursion

(defun pprint-object-or-string-using-pkg (obj indent channel state)
  (cond
   ((stringp obj)
    (princ$ obj channel state))
   ((and (consp obj)
         (eq (car obj) 'encapsulate)
         (consp (cdr obj)))
    (pprogn (princ$ "(ENCAPSULATE" channel state)
            (newline channel state)
            (princ$ " (" channel state)
            (newline channel state)
            (write-objects-using-pkgs (cadr obj) (+ indent 2) channel state)
            (princ$ " )" channel state)
            (newline channel state)
            (newline channel state)
            (write-objects-using-pkgs (cddr obj) (+ indent 1) channel state)
            (princ$ ")" channel state)))
   ((and (consp obj)
         (eq (car obj) 'mutual-recursion))
    (pprogn (princ$ "(MUTUAL-RECURSION" channel state)
            (newline channel state)
            (newline channel state)
            (write-objects-using-pkgs (cdr obj) indent channel state)
            (princ$ ")" channel state)))
   (t
    (mv-let (erp val state)
            (state-global-let*
             ((write-for-read t))
             (er-let*
              ((new-pkg (change-pkg-for-form obj state)))
              (pprogn
               (if new-pkg
                   (pprogn (spaces indent 0 channel state)
                           (princ$ new-pkg channel state)
                           (princ$ "::" channel state)
                           (newline channel state))
                 state)
               (if (int= indent 0) ; optimization
                   state
                 (spaces indent 0 channel state))
               (ppr2 (ppr1 obj (print-base) (print-radix) (- 80 indent) 0 state t)
                     indent channel state t)
               (if new-pkg
                   (in-package-fn "ACL2" state)
                 (value nil)))))
            (declare (ignore erp val))
            state))))

(defun write-objects-using-pkgs (list indent channel state)
  (if (consp list)
      (pprogn (pprint-object-or-string-using-pkg (car list) indent channel
                                                 state)
              (newline channel state)
              (newline channel state)
              (write-objects-using-pkgs (cdr list) indent channel state)
              state)
    state))

)

(defun write-list-using-pkgs (list fname ctx state)
  (mv-let (channel state)
	  (open-output-channel fname :character state)
          (if channel
              (mv-let
               (col state)
               (fmt1 "Writing file ~x0~%" (list (cons #\0 fname))
                     0 (standard-co state) state nil)
               (declare (ignore col))
               (let ((state (write-objects-using-pkgs list 0 channel state)))
                 (pprogn (close-output-channel channel state)
                         (value :invisible))))
            (er soft ctx
                "Unable to open file ~s0 for :character output."
                fname))))

; Now for write-list-into-pkgs.

(mutual-recursion

(defun pprint-object-or-string-into-pkg (obj indent channel state)
  (cond
   ((stringp obj)
    (princ$ obj channel state))
   ((and (consp obj)
         (eq (car obj) 'encapsulate)
         (consp (cdr obj)))
    (pprogn (princ$ "(ENCAPSULATE" channel state)
            (newline channel state)
            (princ$ " (" channel state)
            (newline channel state)
            (write-objects-into-pkgs (cadr obj) (+ indent 2) channel state)
            (princ$ " )" channel state)
            (newline channel state)
            (newline channel state)
            (write-objects-into-pkgs (cddr obj) (+ indent 1) channel state)
            (princ$ ")" channel state)))
   ((and (consp obj)
         (eq (car obj) 'mutual-recursion))
    (pprogn (princ$ "(MUTUAL-RECURSION" channel state)
            (newline channel state)
            (newline channel state)
            (write-objects-into-pkgs (cdr obj) indent channel state)
            (princ$ ")" channel state)))
   (t
    (mv-let (erp val state)
            (state-global-let*
             ((write-for-read t))
             (let* ((new-pkg (and (consp obj)
                                  (eq (car obj) :pkg)
                                  (consp (cdr obj))
                                  (stringp (cadr obj))
                                  (cadr obj)))
                    (form (if new-pkg (cddr obj) obj)))
               (pprogn
                (if new-pkg
                    (pprogn (spaces indent 0 channel state)
                            (princ$ new-pkg channel state)
                            (princ$ "::" channel state)
                            (newline channel state))
                  state)
                (if (int= indent 0) ; optimization
                    state
                  (spaces indent 0 channel state))
                (ppr2 (ppr1 form (print-base) (print-radix) (- 80 indent) 0
                            state t)
                      indent channel state t)
                (value nil))))
            (declare (ignore erp val))
            state))))

(defun write-objects-into-pkgs (list indent channel state)
  (if (consp list)
      (pprogn (pprint-object-or-string-into-pkg (car list) indent channel
                                                state)
              (newline channel state)
              (newline channel state)
              (write-objects-into-pkgs (cdr list) indent channel state)
              state)
    state))

)

(defun write-list-into-pkgs (list fname ctx state)
  (mv-let (channel state)
	  (open-output-channel fname :character state)
          (if channel
              (mv-let
               (col state)
               (fmt1 "Writing file ~x0~%" (list (cons #\0 fname))
                     0 (standard-co state) state nil)
               (declare (ignore col))
               (let ((state (write-objects-into-pkgs list 0 channel state)))
                 (pprogn (close-output-channel channel state)
                         (value :invisible))))
            (er soft ctx
                "Unable to open file ~s0 for :character output."
                fname))))
