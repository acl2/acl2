(defpkg
 #+acl2s "ACL2S-DEV" #-acl2s "ACL2S-HOOKS"
 (append
  '(acl2s ;for ttag
    chk-embedded-event-form *primitive-event-macros* value set-w!
    ld-evisc-tuple connected-book-directory guard-checking-on
    inhibit-output-lst print-clause-ids acl2-raw-mode-p
    ttags-allowed
    raw-mode-restore-lst saved-output-token-lst tainted-okp
    in-package-fn defpkg-fn pe! trans! pso pso! value-triple
    value set-w! default-evisc-tuple reset-prehistory reset-prehistory-fn

    
    progn! untouchable-fns untouchable-vars ld-redefinition-action
    set-ld-skip-proofsp set-ld-redefinition-action set-ld-prompt
    set-ld-keyword-aliases set-ld-pre-eval-filter set-ld-error-triples
    set-ld-error-action set-ld-query-control-alist set-cbd-fn
    set-raw-mode set-raw-mode-fn set-tainted-okp
    push-untouchable-fn remove-untouchable-fn
    set-raw-mode-on set-raw-mode-off temp-touchable-vars temp-touchable-fns
    set-temp-touchable-vars set-temp-touchable-fns built-in-program-mode-fns

    ; hacker stuff
    progn!-with-bindings
    hacker ; documentation topic
    progn+touchable
    progn=touchable
    progn!+touchable
    progn!=touchable
    with-touchable ; alias
    progn+redef
    with-redef-allowed ; alias
    in-raw-mode
    with-raw-mode ; alias
    assert-program-mode
    ensure-program-only-flag
    ensure-program-only
    has-special-raw-definition ; state global
    ensure-special-raw-definition-flag
    assert-no-special-raw-definition
    reconstruct-declare-lst
    modify-raw-defun-permanent
    progn+all-ttags-allowed
    deflabels
    ttag-skip-proofs
    progn+ttag-skip-proofs
    redefun+rewrite
    modify-raw-defun
    redefun defcode

    ; content assist stuff
;;    string-prefix string-prefix1 events-with-prefix
  ;  functions-with-prefix 
   ; constants-with-prefix 
    ;macros-with-prefix 
    ;theorems-with-prefix
    
    
    global-val global-value current-acl2-world ld-level *wormholep* raw-mode-p
    max-absolute-event-number getprop er-let* *valid-output-names*
    state-global-let* extension absolute-to-relative-command-number
    access-command-tuple-number global-set-lst command-number-baseline
    event-number-baseline next-absolute-command-number add-command-landmark
    next-absolute-event-number add-event-landmark scan-to-command
    certify-book-fn f-get-global f-put-global f-boundp-global ttags-seen
    checkpoint-processors soft skip-proofs-seen redef-seen ttag col erp
    in-local-flg certify-book-disabledp fmx chk-well-formed-ttags
    chk-acceptable-ttags1 *primitive-event-macros* primitive-event-macros
    get-portcullis-cmds acl2-version earlier-acl2-versionp trans-eval
    symbol-class good-bye-fn formals
    
    trace-specs trace$ trace* trace! trace$-lst trace$-fn
    untrace$ untrace$-fn maybe-untrace$ maybe-untrace$-fn
    msg first-trace-printing-column trace-level
    inline-book compute-inline-book-value encapsulate-book)
  
  #-acl2s ; exports; don't export during interactive development
  '(begin-book book-beginning progn!-with-bindings
    temp-touchable-vars temp-touchable-fns *settings-globals*
    *critical-settings-globals* *presentation-settings-globals*)
  

  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*)))