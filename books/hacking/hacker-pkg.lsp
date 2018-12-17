; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "ACL2-HACKER"
 (append
  '(; things we want from ACL2 package that aren't in *acl2-exports*:
    value set-w! assert-event msg
    ld-evisc-tuple connected-book-directory guard-checking-on
    inhibit-output-lst print-clause-ids acl2-raw-mode-p 
    raw-mode-restore-lst saved-output-token-lst tainted-okp
    in-package-fn defpkg-fn pe! trans! pso pso! value-triple
    default-evisc-tuple ttag hard soft

    progn! untouchable-fns untouchable-vars ld-redefinition-action
    set-ld-skip-proofsp set-ld-redefinition-action set-ld-prompt
    set-ld-keyword-aliases set-ld-pre-eval-filter set-ld-error-triples
    set-ld-error-action set-ld-query-control-alist set-cbd-fn
    set-raw-mode set-raw-mode-fn set-tainted-okp
    push-untouchable-fn remove-untouchable-fn
    set-raw-mode-on set-raw-mode-off temp-touchable-vars temp-touchable-fns
    set-temp-touchable-vars set-temp-touchable-fns
    built-in-program-mode-fns program-fns-with-raw-code
    
    global-value current-acl2-world ld-level *wormholep* raw-mode-p
    max-absolute-event-number getprop er-let* *valid-output-names*
    state-global-let* extension absolute-to-relative-command-number
    access-command-tuple-number global-set-lst command-number-baseline
    event-number-baseline next-absolute-command-number add-command-landmark
    next-absolute-event-number add-event-landmark scan-to-command
    certify-book-fn f-get-global f-put-global f-boundp-global
    checkpoint-processors global-val acl2-version earlier-acl2-versionp)
    
  '(; defined here and "exported" to ACL2 package:
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
    )
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))

