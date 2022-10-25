(in-package "ACL2S-HOOKS")
(include-book "canonical-print")
(include-book "categorize-input")

(include-book "hacking/hacker" :dir :system)
(include-book "hacking/defcode" :dir :system :ttags ((defcode)))
(include-book "hacking/redefun" :dir :system)
(include-book "hacking/rewrite-code" :dir :system)

(include-book "super-history" :ttags ((:acl2s-super-history) (defcode)))

(include-book "hacking/raw" :dir :system)

(program)
(set-state-ok t)

;; PASSWORD STUFF

(defun acl2s-password-hash (password)
  (let ((n (+ 4984190985322139823307306678324857897
              (acl2-count password))))
    (mod (* n n)
         1976322537236016347623339359149920390129)))

(defun acl2s-passwordp (password state)
  (equal (acl2s-password-hash password) (@ acl2s-password)))

(defun acl2s-protection-begin (password state)
  (if (boundp-global 'acl2s-password state)
    (er soft 'set-acl2s-password "Password already assigned.")
    (er-progn
     (assign acl2s-password (acl2s-password-hash password))
     (value :invisible))))

(defun clear-acl2s-password (password state)
  (if (boundp-global 'acl2s-password state)
    (if (acl2s-passwordp password state)
      (pprogn (makunbound-global 'acl2s-password state)
              (value :invisible))
      (er soft 'clear-acl2s-password "Bad password given."))
    (value :invisible)))

(push-untouchable acl2s-password nil)

(defun acl2s-protected-modep (state)
  (boundp-global 'acl2s-password state))



;; SUPER-HISTORY PROTECTION

(defun user-revert-super-history (n password state)
  (cond
   ((not (acl2s-passwordp password state))
    (er soft 'revert-super-history "Not authorized."))
   (t (revert-super-history n state))))

(push-untouchable (update-super-history
                   restore-current-super-history
                   revert-super-history) t)



;; hooks
(defttag :acl2s-protection)

;; atwalter 2022-09-13
;; we used to modify good-bye-fn here to prevent users from exiting
;; with good-bye, but that caused issues with certification so it was
;; moved to runtime.lsp.

(progn+touchable :all

; non-wormhole ld of *standard-oi* must be at ld-level 1 
(redefun+rewrite
 acl2::chk-acceptable-ld-fn1-pair
 (:carpat (and (symbolp %val%)
               (open-input-channel-p %val% :object state) . %cdr%)
  :vars (%val% %cdr%)
  :mult #-acl2s 2 ;(%val% . val) and (%val% . (cdr last-cons))
        #+acl2s * ; not required in interactive development
  :repl (and (symbolp %val%)
             (open-input-channel-p %val% :object state)
             (or (not (acl2s-protected-modep state))
;;; harshrc 23 Jan 2012 TODO
;;; changed 1 to 2. because timeout is a nested ld
;;; check that nothing breaks.
                 (<= (@ ld-level) 2)
                 (not (eq %val% *standard-oi*)))
             . %cdr%)))

 ; exit properly on *standard-oi* EOF
(redefun+rewrite
 acl2::ld-read-eval-print
 (:carpat (prog2$ (and (equal (standard-oi state) *standard-oi*)
                       (good-bye))
                  state)
  :mult #-acl2s 1
        #+acl2s * ; not required in interactive development
  :repl (if (equal (standard-oi state) *standard-oi*)
          (pprogn (makunbound-global 'acl2s-password state)
                  (prog2$ (good-bye) state))
          state)))
)

(defttag nil)#|ACL2s-ToDo-Line|#

