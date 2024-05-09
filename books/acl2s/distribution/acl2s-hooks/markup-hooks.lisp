(in-package "ACL2S-HOOKS")

(include-book "canonical-print")

(include-book "hacking/hacker" :dir :system)
(include-book "hacking/defcode" :dir :system :ttags ((defcode)))
(include-book "hacking/redefun" :dir :system)
(include-book "hacking/rewrite-code" :dir :system)

(program)
(set-state-ok t)

;; MARKUP STUFF

(defun acl2s-markupp (state)
  (and (boundp-global 'acl2s-markupp state)
       (get-global 'acl2s-markupp state)))

(defun acl2s-markup-begin (state)
  (assign acl2s-markupp t))

(push-untouchable acl2s-markupp nil)



;;WINDOW INTERFACE STUFF


;(defun start-acl2s-window-interface (state)
;  (declare (xargs :mode :program
;                  :stobjs state))
;  (er-progn (assign acl2::window-interfacep t)
;            (assign acl2::window-interface-prelude "")  ; TODO
;            (assign acl2::window-interface-postlude "") ; TODO
;        (ld 
;         '((push-untouchable (acl2::window-interfacep
;                  acl2::window-interface-prelude
;                  acl2::window-interface-postlude) nil))
;         :ld-error-action :error
;         :ld-prompt nil
;         :ld-verbose nil)
;            (value :invisible)))



(defun print-checkpoint (fmt-string state)
  (pfmx-canonical "$ChEcKpOiNt{$~@0$ChEcKpOiNt}$~%" fmt-string))


;; hooks
(defttag :acl2s-markup)

(progn+touchable :all

(redefun+rewrite
 acl2::waterfall-msg1
 (:carpat %body%
  :vars %body%
  :repl (pprogn
         (if (and (acl2s-markupp state)
                  (f-boundp-global 'checkpoint-processors state)
                  (member-eq acl2::processor (@ checkpoint-processors)))
           (print-checkpoint (acl2::tilde-@-clause-id-phrase acl2::cl-id) state)
           state)
         %body%)))

(redefun+rewrite
 acl2::waterfall
 (:carpat %body%
  :vars %body%
  :repl (pprogn
         (if (and (acl2s-markupp state)
                  (f-boundp-global 'checkpoint-processors state)
                  (not (member-eq 'proof-tree (@ inhibit-output-lst))))
           ;; cond matches that from initialize-proof-tree1:
           (cond ((and (null acl2::pool-lst) (eql acl2::forcing-round 0))
                  state)
                 (acl2::pool-lst
                  (if (member-eq :induct (@ checkpoint-processors))
                    (print-checkpoint
                     (acl2::tilde-@-pool-name-phrase acl2::forcing-round acl2::pool-lst)
                     state)
                    state))
                 (t
                  (if (member-eq :forcing-round (@ checkpoint-processors))
                    (print-checkpoint
                     (acl2::tilde-@-pool-name-phrase acl2::forcing-round acl2::pool-lst)
                     state)
                    state)))
           state)
         %body%)))

#|
(redef-rewrite
 acl2::waterfall-print-clause-body
 (:pat "~@0~|~q1.~|"
  :repl (if (acl2s-markupp state)
          "$ClAuSe{$~%~@0$ClAuSe$~|~q1~|$ClAuSe}$~%"
          "~@0~|~q1.~|")
  :mult +))
|#

); progn+touchable

(defttag nil)#|ACL2s-ToDo-Line|#

