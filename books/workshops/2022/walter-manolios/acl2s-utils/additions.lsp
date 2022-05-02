(in-package "ACL2S-INTERFACE-INTERNAL")

(define-var *saved-verbosity-level* (acl2s::acl2s-defaults :get acl2s::verbosity-level))
(define-var *saved-defunc-print-summary* (get-table-value 'acl2s::defunc-defaults-table :print-summary))

(add-quiet-mode-on-hook :acl2s-verbosity-level
                        (lambda ()
                          (setf *saved-verbosity-level* (acl2s::acl2s-defaults :get acl2s::verbosity-level))
                          '((acl2s::acl2s-defaults :set acl2s::verbosity-level 0))))
(add-quiet-mode-off-hook :acl2s-verbosity-level
                         (lambda ()
                           `((acl2s::acl2s-defaults :set acl2s::verbosity-level ,*saved-verbosity-level*))))

(add-quiet-mode-on-hook :defunc-defaults-table
                        (lambda ()
                          (setf *saved-defunc-print-summary* (get-table-value 'acl2s::defunc-defaults-table :print-summary))
                          ;; Set defunc to not print out summaries by default
                          '((acl2s::table acl2s::defunc-defaults-table :print-summary nil))))
(add-quiet-mode-off-hook :defunc-defaults-table
                         (lambda ()
                           `((acl2::table acl2s::defunc-defaults-table :print-summary ,*saved-defunc-print-summary*))))
