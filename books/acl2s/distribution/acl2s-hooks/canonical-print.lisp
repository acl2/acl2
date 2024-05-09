(in-package "ACL2S-HOOKS")

(program)
(set-state-ok t)


;; see with-print-controls in axioms.lisp

;; PRINTING STUFF

(defun put-current-package (pkg state)
  (mv-let (erp v state)
          (acl2::set-current-package pkg state)
          (declare (ignore erp v))
          state))

(defmacro with-upcase-base10 (form)
  `(state-global-let*
    ((print-case :upcase)
     (print-base 10))
    ,form))

(defmacro with-canonical-printing (form)
  `(state-global-let*
    ((print-case :upcase)
     (print-base 10)
     (current-package "COMMON-LISP" put-current-package))
    ,form))

(defmacro fmx-to-comment-window (format &rest args)
  `(fmt-to-comment-window
    ,format
    ,(make-fmt-bindings
      '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
      args)
    0 nil 10))

(defmacro fmx-canonical (formal &rest args)
  `(with-canonical-printing
    (mv (fmx-to-comment-window ,formal . ,args)
        :invisible
        state)))

(defmacro pfmx-canonical (format &rest args)
  `(mv-let (erp val state)
           (fmx-canonical ,format . ,args)
           (declare (ignore erp val))
           state))

(defmacro print-canonical (form) ; form is evaluated
  `(fmx-canonical "~y0~%" ,form))



;; PACKAGE STUFF

(defun package-imports-fn (pack wrld)
  (declare (xargs :guard (and (stringp pack)
                              (plist-worldp wrld))))
  (let* ((known (getprop 'known-package-alist 'global-value
                         nil 'current-acl2-world
                         wrld))
         (known (if (alistp known) known nil))
         (entry (acl2::find-package-entry pack known))
         (entry (if (and (consp entry) (consp (cdr entry))) entry nil)))
    (if (null entry)
      :no-such-package
      (acl2::package-entry-imports entry))))

(defmacro package-imports (pack-expr)
  `(package-imports-fn ,pack-expr (w state)))

(defmacro print-package-imports (pack-expr)
  `(print-canonical (package-imports-fn ,pack-expr (w state))))

(defun non-hidden-known-package-alist0 (known)
  (if (not (consp known))
    ()
    (let ((entry (car known))
          (rst (non-hidden-known-package-alist0 (cdr known))))
      (if (and (consp entry)
               (consp (cdr entry))
               (consp (cddr entry))
               (acl2::package-entry-hidden-p entry))
        rst
        (cons entry rst)))))

(defun non-hidden-known-package-alist (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (non-hidden-known-package-alist0
   (getprop 'known-package-alist 'global-value
            nil 'current-acl2-world
            wrld)))

(defmacro non-hidden-package-list ()
  '(strip-cars (non-hidden-known-package-alist (w state))))
