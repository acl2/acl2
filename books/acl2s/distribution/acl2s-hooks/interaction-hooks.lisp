(in-package "ACL2S-HOOKS")

(include-book "canonical-print")
(include-book "categorize-input")

(include-book "hacking/hacker" :dir :system)
(include-book "hacking/defcode" :dir :system :ttags ((defcode)))
(include-book "hacking/redefun" :dir :system)
(include-book "hacking/rewrite-code" :dir :system)

(include-book "super-history" :ttags ((:acl2s-super-history) (defcode)))

(include-book "hacking/raw" :dir :system)

(include-book "protection-hooks" :ttags ((:acl2s-protection)
                                         (:acl2s-super-history)
                                         (defcode)))

(program)
(set-state-ok t)




;; ENVIRONMENT STUFF

(defun dump-environment-info (state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (erp in-wormhole state)
          (acl2::wormhole-p state)
          (declare (ignore erp))
          (mv (list (@ current-package)
                    (@ ld-level)
                    (if in-wormhole 1 0)
                    (if (acl2::raw-mode-p state) 1 0)
                    (non-hidden-package-list)
                    (max-absolute-event-number (w state))
                    (if (boundp-global 'super-history state)
                      (len (@ super-history))
                      0)
                    (if (boundp-global 'super-history-reverted state)
                      (len (@ super-history-reverted))
                      0))
              state)))


(defun begin-environment (state)
  (mv-let (env-info state)
          (dump-environment-info state)
          (mv-let (erp val state)
                  (with-upcase-base10
                   (mv-let (col state)
                           (fmt1 "$~@p{$~%~xx$~@p$"
                                 (list
                                  (cons #\p "EnViRoNmEnT")
                                  (cons #\x env-info))
                                 0 *standard-co* state nil)
                           (mv nil col state)))
                  (declare (ignore erp val))
                  state)))

(defun end-environment (state)
  (mv-let (irrel-col state)
          (fmt1 "$~@p}$~%"
                (list (cons #\p "EnViRoNmEnT"))
                0 *standard-co* state nil)
          (declare (ignore irrel-col))
          state))


;;SUPPORT FOR :U, :UBT
#| ; superceded by code in super-history
(defun ubt-cd-to-absevt (cd state)
  (er-let*
    ((cd-wrld (acl2::er-decode-cd cd (w state) ':ubt state)))
    (value (max-absolute-event-number (scan-to-command (cdr cd-wrld))))))

(defmacro print-ubt-absevt (cd)
  `(er-let*
     ((n (ubt-cd-to-absevt ',cd state)))
     (fmx-canonical "INDEX:~p0~%" n)))

(defun ubu-cd-to-absevt (cd state)
  (er-let*
    ((cd-wrld (acl2::er-decode-cd cd (w state) ':ubu state)))
    (value (max-absolute-event-number cd-wrld))))

(defmacro print-ubu-absevt (cd)
  `(er-let*
     ((n (ubu-cd-to-absevt ',cd state)))
     (fmx-canonical "INDEX:~p0~%" n)))
|#

;; ACTIVATION, part 1

(defun acl2s-interactionp (state)
  (and (f-boundp-global 'acl2s-interactionp state)
       (f-get-global 'acl2s-interactionp state)))



;; hooks
(defttag :acl2s-interaction)

(progn+touchable :all

(redefun+rewrite
 acl2::ld-print-prompt
 (:carpat %body%
  :vars %body%
  :repl (pprogn
         (if (and (acl2s-interactionp state)
                  (eq (standard-oi state) *standard-oi*))
           (begin-environment state)
           state)
         (mv-let (col state)
                 %body%
                 (pprogn
                  (if (and (acl2s-interactionp state)
                           (eq (standard-oi state) *standard-oi*))
                    (end-environment state)
                    state)
                  (mv col state))))))

(redefun+rewrite
 acl2::ld-read-eval-print
 :seq
 (:carpat %body%
  :vars %body%
  :repl (let ((old-std-oi-interaction (standard-oi state)))
          %body%))
 (:carpat (acl2::ld-print-results %trans-ans% state)
  :vars %trans-ans%
  :mult 1
  :repl (pprogn
         (if (and (equal old-std-oi-interaction *standard-oi*)
                  (acl2s-interactionp state))
           (prog2$ (fmx-to-comment-window "${~@0}$~%" "SuCcEsS")
                   state)
           state)
         (acl2::ld-print-results %trans-ans% state))))

; package dump stuff
(redefun+rewrite
 acl2::defpkg-fn
 (:carpat (let* ((acl2::imports %val%)
                 . %rst%)
            %body%)
  :vars (%val% %rst% %body%)
  :mult 1
  :repl (let* ((acl2::imports %val%)
                 . %rst%)
            (pprogn
             (if (acl2s-interactionp state)
               (pfmx-canonical "$~@0{$~%~x1~%$~@0}$~%" "DeFpKg" (cons acl2::name acl2::imports))
               state)
             %body%))))

(defun dump-pkgs (names state)
  (if (endp names)
    state
    (pprogn
     (let ((imports (package-imports (car names))))
       (if (consp imports)
         (pfmx-canonical "$~@0{$~%~x1~%$~@0}$~%" "DeFpKg" (cons (car names) imports))
         state))
     (dump-pkgs (cdr names) state))))


; trace* modification stuff

;; if guard-checking is :none and there are functions being
;; traced, also use that during proofs
(redefun+rewrite
 acl2::prove
 (:carpat (acl2::state-global-let*
           ((acl2::guard-checking-on nil)
            . %bindings-rest%)
           %body%)
  :vars (%body% %bindings-rest%)
  :mult *
  :repl (acl2::state-global-let*
         ((acl2::guard-checking-on
           (if (and (equal (@ acl2::guard-checking-on) :none)
                    (acl2::boundp-global 'acl2::trace-specs state)
                    (@ acl2::trace-specs))
             :none
             nil))
          . %bindings-rest%)
         %body%)))


#|
; ought to be defined in tracing stuff
(defun acl2::stobj-evisceration-alist (acl2::user-stobj-alist state)
  (cond ((endp acl2::user-stobj-alist)
         (list (cons (acl2::coerce-state-to-object state)
                     acl2::*evisceration-state-mark*)))
        (t (cons (cons (cdar acl2::user-stobj-alist)
                       (acl2::evisceration-stobj-mark (caar acl2::user-stobj-alist) nil))
                 (acl2::stobj-evisceration-alist (cdr acl2::user-stobj-alist) state)))))

(defun acl2::trace-evisceration-alist (state)
  (append (acl2::world-evisceration-alist state nil)
          (acl2::stobj-evisceration-alist (acl2::user-stobj-alist state) state)))
; done with ought to be defined in tracing stuff
|#

) ; end progn+touchable

;; atwalter 2022-09-13
;; we used to modify read-object here but that caused issues with
;; certification so it was moved to runtime.lsp.

(defttag nil)

(make-event (pprogn (f-put-global 'acl2s-interactionp nil state)
                    (value '(value-triple nil))))

;; ACTIVATION, part 2

(defun acl2s-interaction-begin (state)
  (pprogn
   (f-put-global 'acl2s-interactionp t state)
   (dump-pkgs (non-hidden-package-list) state)
   (value t)))

(push-untouchable acl2s-interactionp nil)
