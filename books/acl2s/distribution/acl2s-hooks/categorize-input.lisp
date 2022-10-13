(in-package "ACL2S-HOOKS")
(include-book "canonical-print")

(defconst *query-fns*
  '(
    pbt pc pcb pcb! pcs pe pe! pf pl pr pr!
    trans trans1 trans! thm props acl2::test? 
    help docs doc doc! 
    acl2::xdoc 
    args acl2::more acl2::more! nqthm-to-acl2 
    pso pso! pstack verbose-pstack
    value value-triple ttags-seen

    print-package-imports
    print-keyword-info
    categorize-input
    print-input-categorization))

(defconst *undoable-fns*
  '(
    in-package in-package-fn defpkg defpkg-fn
    set-ld-skip-proofsp set-ld-redefinition-action set-ld-prompt
    set-ld-pre-eval-filter set-ld-error-triples ;set-ld-keyword-aliases
    set-ld-error-action set-ld-query-control-alist set-cbd set-cbd-fn
    set-guard-checking set-raw-mode set-raw-mode-fn set-tainted-okp
    
    trace$ trace* trace! trace$-lst trace$-fn
    untrace$ untrace$-fn maybe-untrace$ maybe-untrace$-fn
    reset-prehistory reset-prehistory-fn
    
    ;; mine \/
    acl2::set-ccg-verbose))


; TODO: check for updates in ACL2 v3.5

(defconst *critical-settings-globals*
  '(;;standard-oi
    current-package
    ld-skip-proofsp
    ld-redefinition-action
;    ld-keyword-aliases (removed in 6.3 as state global)
    ld-pre-eval-filter
    ld-error-triples
    ld-error-action
    ld-query-control-alist
    connected-book-directory
    guard-checking-on
    acl2-raw-mode-p
    raw-mode-restore-lst
    saved-output-token-lst
    tainted-okp
    skipped-proofsp
    temp-touchable-vars
    temp-touchable-fns
    ttags-allowed
    ))

(defconst *monitor-settings-globals*
  '(acl2::trace-specs
    acl2::gstackp ; for brr
    acl2::brr-monitored-runes
    acl2::make-event-debug
    ;acl2::dmrp ; requires activation/deactivation. dmr writes to a file.  also emacs-specific it seems.
  ))

(defconst *presentation-settings-globals*
  '(acl2::ld-prompt
    acl2::ld-pre-eval-print
    acl2::ld-post-eval-print
    acl2::ld-evisc-tuple
    acl2::ld-verbose
    acl2::prompt-function
    ;acl2::prompt-memo  ; do not include!
    acl2::triple-print-prefix
    acl2::print-base
    acl2::print-case
    acl2::proofs-co
    acl2::inhibit-output-lst
    acl2::print-clause-ids
    acl2::ccg-verbose
    acl2::gag-mode
    acl2::checkpoint-forced-goals
    acl2::checkpoint-processors
    acl2::checkpoint-summary-limit
    acl2::saved-output-p
    acl2::saved-output-token-lst
    
    acl2::evalable-ld-printingp
    acl2::evalable-printing-abstractions
    ))

(defconst *settings-globals*
  (append *critical-settings-globals*
          *monitor-settings-globals*
          *presentation-settings-globals*))

(defconst *restorable-transient-globals*
  '(acl2::gag-state
    acl2::gag-state-saved
    acl2::saved-output-reversed))

(program)
(set-state-ok t)

;; CATEGORIZATION STUFF

(defmacro er-or (form &rest forms)
  `(mv-let
    (er-or-erp er-or-val state)
    ,form
    (if er-or-erp
      ,(if (consp forms)
         (cons 'er-or forms)
         '(mv t er-or-val state))
      (mv nil er-or-val state))))

(defun nil-listp (lst)
  (or (null lst)
      (and (consp lst)
           (null (car lst))
           (nil-listp (cdr lst)))))

(defun er-trans-stobjs-out-fn (form state)
  (mv-let (flg val bindings state)
      (acl2::translate1 form
              :stobjs-out '((:stobjs-out . :stobjs-out)) t
              'acl2::check-input (w state) state)
      (declare (ignore val))
      (mv flg (acl2::translate-deref :stobjs-out bindings) state)))



(defun chk-in-package-fn (form state)
  (cond ((and (consp form)
              (eq (car form) 'in-package)
              (consp (cdr form))
              (member-equal (cadr form) (non-hidden-package-list))
              (null (cddr form)))
         (value :invisible))
        (t
         (mv t nil state))))

(defun chk-begin-book-fn (form state)
  (cond ((and (consp form)
              (eq (car form) 'begin-book)
              (true-listp (cdr form)))
         (er-progn
           (er-trans-stobjs-out-fn form state) ; ACL2's syntax check
           (value :invisible)))
        (t
         (mv t nil state))))


;; define (primitive-event-macros) if needed (3.3 or older)
(make-event
 (if (getprop 'primitive-event-macros 'symbol-class nil 'current-acl2-world (w state))
   (value '(value-triple 'primitive-event-macros))
   (value '(defun primitive-event-macros ()
             (declare (xargs :guard t :mode :logic))
             *primitive-event-macros*))))

(defun chk-top-level-event-fn (form state)
  (chk-embedded-event-form form form (w state) 'top-level state
                           (primitive-event-macros) () () ()))

(defun chk-value-triple-fn (form state)
  (cond ((and (consp form)
              (true-listp (cdr form))
              (symbolp (car form))
              (eq (car form) 'value-triple))
         (value :invisible))
        ((and (consp form)
              (true-listp (cdr form))
              (member (car form) '(progn er-progn)))
         (er-progn
          (chk-value-triple-fn (cadr form) state)
          (if (consp (cddr form))
            (chk-value-triple-fn (cons 'progn (cddr form)) state)
            (value :invisible))
          (value :invisible)))
        (t
         (mv t nil state))))

(defun chk-query-fn (form state)
  (cond ((and (consp form)
              (true-listp (cdr form))
              (symbolp (car form))
              (member (car form) *query-fns*))
         (value :invisible))
        ((and (consp form)
              (true-listp (cdr form))
              (member (car form) '(progn er-progn)))
         (er-progn
          (chk-query-fn (cadr form) state)
          (if (consp (cddr form))
            (chk-query-fn (cons 'progn (cddr form)) state)
            (value :invisible))
          (value :invisible)))
        (t
         (mv t nil state))))

(defun chk-command-fn (form state)
  (cond ((and (consp form)
              (true-listp (cdr form))
              (symbolp (car form))
              (or (member (car form) *undoable-fns*)
                  (member (car form) *query-fns*)
                  (and (eq (car form) 'assign)
                       (consp (cdr form))
                       (member (cadr form) (if (boundp-global 'super-history-globals state)
                                             (@ super-history-globals)
                                             *settings-globals*)))
                  (and (member (car form) '(f-put-global put-global))
                       (consp (cdr form))
                       (consp (cadr form))
                       (eq (caadr form) 'quote)
                       (consp (cdadr form))
                       (member (cadadr form) (if (boundp-global 'super-history-globals state)
                                               (@ super-history-globals)
                                               *settings-globals*)))))
         (value :invisible))
        ((and (consp form)
              (true-listp (cdr form))
              (member (car form) '(progn er-progn)))
         (er-progn
          (chk-command-fn (cadr form) state)
          (if (consp (cddr form))
            (chk-command-fn (cons 'progn (cddr form)) state)
            (value :invisible))
          (value :invisible)))
        (t
         (mv t nil state))))

(defun chk-pkg-string-fn (form state)
  (if (and (stringp form) ; support for "PKG" method of changing packages
           (member-equal form (non-hidden-package-list)))
    (value :invisible)
    (mv t nil state)))


(defun categorize-input-fn (form state)
  (state-global-let*
   ((inhibit-output-lst *valid-output-names*))
   (if (raw-mode-p state)
     (er-or
      (er-progn
       (chk-query-fn form state)
       (value :QUERY))
      (if (atom form)
        (value :VALUE)
        (value :RAW)))
     (er-or
      (er-progn
       (chk-in-package-fn form state)
       (value :IN-PACKAGE))
      (er-progn
       (chk-begin-book-fn form state)
       (value :BEGIN-BOOK))
      (er-progn
       (chk-value-triple-fn form state)
       (value :VALUE-TRIPLE))
      
      ;;;Note: harshrc: Swapped EVENT and QUERY
      (er-progn
       (chk-query-fn form state)
       (value :QUERY))
      
      (er-progn
       (chk-top-level-event-fn form state)
       (value :EVENT))
      
      (er-progn
       (chk-pkg-string-fn form state)
       (value :COMMAND))
      (er-progn
       (chk-command-fn form state)
       (value :COMMAND))
      (er-let*
        ((stobjs-out (er-trans-stobjs-out-fn form state)))
        (if (nil-listp stobjs-out)
          (if (symbolp form)
            (mv-let (erp v state)
                    (ld (list form) :ld-error-action :return :ld-user-stobjs-modified-warning t)
                    (if (or erp (equal v :error))
                      (value :BAD)
                      (value :VALUE)))
            (value :VALUE))
          (value :ACTION)))
      (value :BAD)))))

(defmacro categorize-input (form-expr)
  `(categorize-input-fn ,form-expr state))

(defmacro print-input-categorization (form)
  `(mv-let (erp val state)
           (categorize-input-fn ',form state)
           (if (or erp (not (symbolp val)))
             (mv t :invisible state)
             (fmx-canonical "CATEGORY~y0~%" val))))


;; Keyword command stuff

(defmacro colon-q () '(acl2::exit-ld state))

; should be redundant if acl2 version <= 3.3
(defun acl2::no-lambda-keywordsp (acl2::lst)
  (declare (xargs :guard (true-listp acl2::lst)))
  (cond ((null acl2::lst) t)
        ((acl2::lambda-keywordp (car acl2::lst))
         nil)
        (t (acl2::no-lambda-keywordsp (cdr acl2::lst)))))


(defun get-keyword-info (key state)
  (let* ((wrld (w state))
         (aliases (ld-keyword-aliases state))
         (name (symbol-name key))
         (sym (intern name "ACL2"))
         (temp (assoc-eq key aliases)))
    (cond
     (temp         (cdr temp))
     ((eq sym 'acl2::q)  (list 0 'colon-q))
     ((function-symbolp sym wrld)
      (list (length (acl2::formals sym wrld)) sym))
     ((getprop sym 'acl2::macro-body nil 'current-acl2-world wrld)
      (let ((margs (getprop sym 'acl2::macro-args
                            '(:error "See LD-READ-KEYWORD-COMMAND.")
                            'current-acl2-world wrld)))
        (if (acl2::no-lambda-keywordsp margs)
          (list (length margs) sym)
          :lambda-keywords)))
     (t :undefined))))


(defmacro keyword-info (key-expr)
  `(get-keyword-info ,key-expr state))


(defmacro print-keyword-info (key)
  `(print-canonical (keyword-info ',key)))
