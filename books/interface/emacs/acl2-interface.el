
;; Add interface for various acl2 buffers.
;; Sep 20 94 MKS

;; ----------------------------------------------------------------------
;; USER SETTINGS

;; The following controls what features of the interfaces get used.
;; These settings mirror those in start-inferior-acl2.el.
;; You can override these setting by setting them in your .emacs file.

;; The variable, *acl2-user-map-interface*, is an alist of modes . (list of features).
;; The features currently supported are: menu-bar, pop-up-menu, and keys.
;; The default below says add them all.

;; Before the menu-bar, popup-menu or keys are defined we check
;; the following alist to see what the user wants.

(defvar *acl2-user-map-interface*
  '((inferior-acl2-mode-map menu-bar popup-menu keys)
    (shell-mode-map         menu-bar popup-menu keys)
    (acl2-mode-map          menu-bar popup-menu keys)
    (prooftree-mode-map     menu-bar popup-menu keys)))

;; (defvar *acl2-proof-tree-height* 17)
;; (defvar *checkpoint-recenter-line* 3)

;; ----------------------------------------------------------------------
;; Load all of the various acl2-interface files, if necessary.

; The changes below were made August 2014 as suggested by Camm
; Maguire, "in response to a Debian bug regarding certain emacs
; policies", "to load the byte compiled versions when available".

;(load "inf-acl2.el")			;(require 'inf-acl2)
;(load "mfm-acl2.el")			;(require 'mfm-acl2)
;(load "interface-macros.el")		;(require 'interface-macros)
(require 'inf-acl2)
(require 'mfm-acl2)
(require 'interface-macros)

(update-mode-menu-alist *acl2-user-map-interface*)

;(load "acl2-interface-functions.el")
(load "acl2-interface-functions")

;; ----------------------------------------------------------------------
;; Specials used by functions in interface-macros.el.

;; MENU-BAR-FINAL-ITEMS is a global, honored by all menu-bar presentations.
;; If the menu-bar contains any element whose car (a SYMBOL)
;; is in it, that element will appear after any not mentioned.
;; The ordering of MENU-BAR-FINAL-ITEMS is honored in the presentation.
(setq menu-bar-final-items '(events help-acl2 help))

(defconst general-wrapper "(acl2-wrap (acl2::%s))\n")
(defconst verify-wrapper "(lisp %s)\n")
(defconst acl2-wrapper   "(%s)\n")
(defconst interface-wrapper acl2-wrapper)

(setq interface-to-top  '(inf-acl2-last-line-to-top))
(setq menu-bar-prefix   "acl2-menu-bar-%s")

(setq interface-menu-function  '(inf-acl2-send-string <command> <arg>))
(setq interface-popup-function '(inf-acl2-send-string <command> <arg>))

;; These alists allow us to handle some arguments to menu and popup function
;; differently from the defaults above.

(setq menu-arg-functions
      (append (cons 'cd
		    '(cond ((not cd) (beep t))
			   (t (inf-acl2-send-string <command> cd))))
	      menu-arg-functions))

(setq popup-arg-functions
      (append (cons 'cd
		    '(let ((thing (thing-at-click click 'symbol))
			   (number (thing-at-click click 'number)))
		       (cond (thing (inf-acl2-send-string <command> thing))
			     ((and (stringp number)
				   (numberp (setq number (int-to-string number))))
			      (inf-acl2-send-string <command> number))
			     (t (beep t)))))
	      popup-arg-functions))

;; ======================================================================
;; Inferior acl2

;; ----------------------------------------------------------------------
;; Inferior acl2 menu bar.  The buffer containing the Acl2 process.

(defconst inf-acl2-menu-bar
  '((:menu "History"
       (:entry "Recent events" "pbt '(:here -10)" :to-top)
       (:entry "Print back through ..."  "pbt '%s" :arg event :to-top)

       (:entry "Undo" "u")
       (:entry "Oops" "oops" )
       (:entry "Undo through ..." "ubt '%s" :arg event)
       (:entry "Undo! through ..." "ubt! '%s" :arg cd)
       (:label "")
       (:entry "Load file ..." acl2-load-file)
       (:label "")
       (:entry "Disable ..." "in-theory (disable %s)" :arg symbol)
       (:entry "Enable ..." "in-theory (enable %s)" :arg symbol)
       (:label "")
       (:entry "Verify guards ..."      "verify-guards '%s" :arg symbol)
       (:entry "Verify termination ..." "verify-termination '%s" :arg symbol)
       (:label "")
       (:entry "Certify-book ..." "certify-book \"%s\"" :arg filename) ; world of 0 commands
       (:entry "Include-book ..." "include-book \"%s\"" :arg filename)
       (:label "")
       (:menu "Compound commands"
	(:entry "Expand ..." "puff '%s" :arg cd :to-top)
	(:entry "Expand! ..." "puff* '%s" :arg cd :to-top))
       (:menu "Table"
	(:entry "Print value ..."    "table  %s" :arg symbol)
	(:entry "Clear ..."          "table %s nil nil :clear" :arg symbol)
	(:entry "Print guard ..."    "table %s nil nil :guard" :arg symbol)
	;; ("Print element ..." "(table <arg1> <arg2>)")
	;; ("Set element ..."   "(table <arg1> <arg2> <arg3>)")
	;; ("Set value ..."     "(table <arg1> nil <arg2> :clear)")
	;; ("Set Guard ..."     "(table <arg1> nil nil :guard <arg2>)")
	))
      (:menu "Print"
       (:entry "Event ..." "pe '%s"  :arg event :to-top)
       (:entry "Event! ..." "pe! '%s" :arg event :to-top)
       (:entry "Back through ..."  "pbt '%s" :arg event :to-top)

       (:entry "Command ..." "pc '%s"  :arg cd :to-top)
       (:entry "Command block ..." "pcb '%s" :arg cd :to-top)
       (:entry "Full Command block ..." "pcb! '%s" :arg cd :to-top)

       (:entry "Signature ..." "args '%s" :arg event :to-top)
       (:entry "Formula ..." "pf '%s" :arg event :to-top)
       (:entry "Properties ..." "props '%s" :arg event :to-top)

       (:entry "Print connected book directory" "cbd")

       (:entry "Rules whose top function symbol is ..." "pl '%s" :arg event :to-top)
       (:entry "Rules stored by event ..." "pr '%s"   :arg event :to-top)
       (:entry "Rules stored by command ..." "pr! '%s" :arg cd :to-top)

       (:entry "Monitored-runes" "monitored-runes"))

      (:menu "Control"
       (:entry "Load ..." "ld \"%s\"" :arg filename)
       (:entry "Compile all" "comp t")
       (:entry "Compile ..." "comp '%s" :arg symbol)

       (:menu "Accumulated Persistence"
	(:entry "Activate" "accumulated-persistence t")
	(:entry "Deactivate" "accumulated-persistence nil")
	(:menu "Display statistics ordered by"
	 (:entry "frames" "show-accumulated-persistence :frames")
	 (:entry "times tried" "show-accumulated-persistence :tries")
	 (:entry "ratio" "show-accumulated-persistence :ratio")))

       (:menu "Break rewrite"
	(:entry "Start general rule monitoring" "brr t")
	(:entry "Stop general rule monitoring" "brr nil")
	(:entry "Print monitored runes"  "monitored-runes")
	(:entry "Monitor rune: ..." "monitor '%s 't" :arg event)
	(:entry "Unmonitor rune: ..." "unmonitor '%s" :arg event)
	;; (:entry "Conditionally exit break-rewrite" "ok-if")
	;; Above needs an argument.
	(:label "")
	(:menu "Commands"
	 (:entry "Abort to ACL2 top-level" "#." :unwrapped)
	 (:entry "Term being rewritten" ":target" :unwrapped)
	 (:entry "Substitution making :lhs equal :target" ":unify-subst" :unwrapped)
	 (:entry "Hypotheses" ":hyps" :unwrapped)
	 (:entry "Ith hypothesis ..." ":hyp %d" :arg integer :unwrapped)
	 (:entry "Left-hand side of conclusion" ":lhs" :unwrapped)
	 (:entry "Right-hand side of conclusion" ":rhs" :unwrapped)
	 (:entry "Type assumptions governing :target" ":type-alist" :unwrapped)
	 (:entry "Ttree before :eval" ":initial-ttree" :unwrapped)
	 (:entry "Negations of backchaining hyps pursued" ":ancestors" :unwrapped)

	 (:label "")
	 (:entry "Rewrite's path from top clause to :target" ":path" :unwrapped)
	 (:entry "Top-most frame in :path" ":top" :unwrapped)
	 (:entry "Ith frame in :path ..." ":frame %d" :arg integer :unwrapped)

	 (:label "")
	 (:menu "AFTER :EVAL"
	  (:entry "Did application succeed?" ":wonp" :unwrapped)
	  (:entry "Rewritten :rhs" ":rewritten-rhs"  :unwrapped)
	  (:entry "Ttree" ":final-ttree" :unwrapped)
	  (:entry "Reason rule failed" ":failure-reason"  :unwrapped))

	 (:menu "CONTROL"
	  (:entry "Exit break" ":ok" :unwrapped)
	  (:entry "Exit break, printing result" ":go" :unwrapped)
	  (:entry "Try rule and re-enter break afterwards" ":eval" :unwrapped))

	 (:menu "WITH NO RECURSIVE BREAKS"
 	  (:entry ":ok!" ":ok!")
	  (:entry ":go!" ":go!")
	  (:entry ":eval!" ":eval!"))

	 (:menu "WITH RUNES MONITORED DURING RECURSION"
  	  (:entry ":ok  ..." ":ok$ %s" :arg sexpr)
	  (:entry ":go ..." ":go$  %s" :arg sexpr)
	  (:entry ":eval ..." ":eval$ %s" :arg sexpr))
	 (:label "")
	 (:entry "Help" ":help")))
       (:entry "Enter Acl2 Loop" "(lp)" :unwrapped)
       (:entry "Quit to Common Lisp" ":Q" :unwrapped)
       (:entry "ABORT" ":good-bye"))

      (:menu "Settings"
       (:menu "Mode"
	 (:entry "Logic" "logic")
	 (:entry "Program" "program")
	 (:entry "Guard checking on" "set-guard-checking t")
	 (:entry "Guard checking off" "set-guard-checking nil"))
       (:menu "Forcing"
	(:entry "On"  "enable-forcing")
	(:entry "Off" "disable-forcing"))
       (:menu "Compile functions"
        (:entry "On"  "set-compile-fns t")
        (:entry "Off" "set-compile-fns nil"))
       (:menu "Proof tree"
	 (:entry "Start prooftree" "start-proof-tree" :pre (start-proof-tree nil))
	 (:entry "Stop prooftree" "stop-proof-tree" :post (stop-proof-tree))
	 (:entry "Checkpoint forced goals on" "checkpoint-forced-goals t")
	 (:entry "Checkpoint forced goals on" "checkpoint-forced-goals nil"))
       (:menu "Inhibit Display of "
	      (:entry "Error messages" "assign inhibit-output-lst '(error)")
	      (:entry "Warnings" "assign inhibit-output-lst '(warning)")
	      (:entry "Observations" "assign inhibit-output-lst '(observation)")
	      (:entry "Proof commentary" "assign inhibit-output-lst '(prove)")
	      (:entry "Proof tree" "assign inhibit-output-lst '(proof-tree)")
	      (:entry "Non-proof commentary" "assign inhibit-output-lst '(event)")
	      (:entry "Summary" "assign inhibit-output-lst '(summary)"))
       (:menu "Unused Variables"
	(:entry "Ignore" "set-ignore-ok t")
	(:entry "Fail"   "set-ignore-ok nil")
	(:entry "Warn"   "set-ignore-ok :warn"))
       (:menu "Irrelevant formulas"
	(:entry "Ok" "set-irrelevant-formals-ok t")
	(:entry "Fail" "set-irrelevant-formals-ok nil")
	(:entry "Warn" "set-irrelevant-formals-ok :warn"))
       (:menu "Load"
	(:menu "Error action"
 	 (:entry "Continue" "set-ld-error-actions :continue")
	 (:entry "Return" "set-ld-error-actions :return")
	 (:entry "Error" "set-ld-error-actions :error"))
	(:menu "Error triples"
	 (:entry "On"  "set-ld-error-triples t")
	 (:entry "Off" "set-ld-error-triples nil"))
	(:menu "Post eval print"
	 (:entry "On" "set-ld-post-eval-print t")
	 (:entry "Off" "set-ld-post-eval-print nil")
	 (:entry "Command conventions" "set-ld-post-eval-print :command-conventions"))
	(:menu "Pre eval filter"
	 (:entry "All" "set-ld-pre-eval-filter :all")
	 (:entry "Query" "set-ld-pre-eval-filter :query"))
	(:menu "Prompt"
  	 (:entry "On" "set-ld-prompt t")
	 (:entry "Off" "set-ld-prompt nil"))
	(:menu "Skip proofs"
	 (:entry "On" "set-ld-skip-proofs t")
	 (:entry "Off" "set-ld-skip-proofs nil"))
	(:menu "Verbose: on"
	 (:entry "On" "set-ld-verbose t")
	 (:entry "Off" "set-ld-verbose nil"))
	(:entry "Redefinition permitted" "redef")
	(:entry "Reset specials" "reset-ld-specials nil")
	(:entry "Reset specials (+ I/O)" "reset-ld-specials t")
	(:menu "HACKERS. DANGER!"		;advanced
	 (:entry "Redefinition permitted!" "redef!"))))

      (:menu "Books"
       (:entry "Print connected book directory" "cbd")
       (:entry "Set connected book directory ..." "set-cbd %s" :arg filename)
       (:entry "Certify-book ..." "certify-book \"%s\"" :arg filename)
       (:entry "Include-book ..." "include-book \"%s\"" :arg filename))

      (:menu "Acl2 Help"
       (:entry "Documentation" "doc '%s" :arg symbol :to-top)
       (:entry "Arguments" "args '%s" :arg symbol :to-top)
       (:entry "More" "more")
       (:entry "Apropos ..." "docs '%s" :arg symbol :to-top)
       (:entry "Menu help" acl2-menu-help))))


;; ----------------------------------------------------------------------
;; Inferior acl2 popup menu.  The buffer containing the Acl2 process.

(defconst inferior-acl2-popup
  '((:entry "Recent events"  "pbt '(:here -10)")
    (:entry ". Print Event"    "pe '%s" :arg event)
    (:entry ". Print Command"  "pc '%s" :arg cd)
    (:entry ". Print back to"  "pbt '%s" :arg cd)
    (:entry ". Disable"        "in-theory (disable %s)" :arg event)
    (:entry ". Enable"         "in-theory (enable %s)" :arg event)
    (:entry "Undo"           "ubt ':here")
    (:entry ". Undo thru"      "ubt '%s" :arg cd)
    (:entry ". Documentation"  "doc '%s" :arg symbol)
    (:entry ". Arguments, etc" "args '%s" :arg symbol)
    (:label "")
    (:entry ". Verify"         acl2-mouse-verify click)))


;; ----------------------------------------------------------------------
;; inferior acl2 keys

(defconst inferior-acl2-keys
  '(("\C-x\C-e" acl2-eval-last-sexp)
    ("\C-c\C-l" acl2-load-file)
    ("\C-c\C-a" acl2-show-arglist)
    ("\C-c\C-d" acl2-describe-sym)
    ("\C-c\C-f" acl2-show-function-documentation)
    ("\C-c\C-v" acl2-show-variable-documentation)
    ("\C-cl"    acl2-load-file)
    ("\C-ck"    acl2-compile-file)
    ("\C-ca"    acl2-show-arglist)
    ("\C-cd"    acl2-describe-sym)
    ("\C-cf"    acl2-show-function-documentation)
    ("\C-cv"    acl2-show-variable-documentation)))

(define-interface inferior-acl2-mode inferior-acl2-mode-map
                  inf-acl2-menu-bar
                  '(inout completion signals)
		  inferior-acl2-popup
		  inferior-acl2-keys)

;; ======================================================================
;; Acl2 mode

;; ----------------------------------------------------------------------
;; Acl2 mode popup menu.  For buffers containing Acl2 code.

;; For acl2-mode-map
;; What happened to default-menu ???  We just overwrite it.

(defconst acl2-menu-bar-value nil)

(defconst acl2-popup-menu-value
      '((:entry ". Send to Acl2" acl2-eval-event-at-click :arg click)

	(:entry "Send region to Acl2" acl2-mouse-eval-region)
	(:entry "Send buffer to Acl2" acl2-mouse-eval-buffer)

	(:entry ". Add hint" add-hint-to-defun-at-click :arg click)
	(:entry "Go to inferior Acl2" switch-to-acl2-eof)
	(:entry ". Verify" acl2-mouse-verify :arg click)))

(defconst acl2-keys			; due to inferior acl2
  '(("\C-x\C-e" acl2-eval-last-sexp)
    ("\C-c\C-r" acl2-eval-region)
    ("\M-\C-x"  acl2-eval-event)
    ("\C-c\C-e" acl2-eval-event)
    ("\C-c\C-z" switch-to-acl2-eof)
    ("\C-c\C-l" acl2-load-file)
    ("\C-c\C-a" acl2-show-arglist)
    ("\C-c\C-d" acl2-describe-sym)
    ("\C-c\C-f" acl2-show-function-documentation)
    ("\C-c\C-v" acl2-show-variable-documentation)
    ("\C-ce"    acl2-eval-event-and-go)
    ("\C-cr"    acl2-eval-region-and-go)))

(define-interface acl2-mode acl2-mode-map
                  acl2-menu-bar-value
		  nil
		  acl2-popup-menu-value
		  acl2-keys)


;; ======================================================================
;; Prooftree mode

;; ----------------------------------------------------------------------
;; Prooftree mode menu-bar menu.

(defconst prooftree-menu-bar
  '((:menu "Prooftree"
	   (:entry "Checkpoint" acl2-menu-checkpoint)
	   (:entry "Checkpoint / Suspend" acl2-menu-checkpoint-suspend)
	   (:entry "Suspend proof tree" suspend-proof-tree)
	   (:entry "Resume proof tree" resume-proof-tree)
	   (:entry ". Goto subgoal" goto-subgoal)
	   (:entry "Help" checkpoint-help)
	   )))


;; ----------------------------------------------------------------------
;; Prooftree pop-up menu

;; Unconditionally expects prooftree-mode-map to be set.
;; Prooftree mode should have already been established by mfm-acl2.

(defconst prooftree-popup-menu-value
      '((:entry ". Checkpoint"         acl2-mouse-checkpoint :arg click)
	(:entry ". Goto subgoal"       goto-subgoal-menu :arg click)
	(:entry ". Checkpoint/Suspend" acl2-mouse-checkpoint-suspend :arg click)
	(:entry "Suspend proof tree" suspend-proof-tree)
	(:entry "Resume proof tree"  resume-proof-tree)
	(:entry "Help"               checkpoint-help)
	))

;; Defined in mfm-acl2 so that checkpoint-help can use it.
(defvar prooftree-subkey)
(setq prooftree-subkey "\C-z")

;; prooftree-subkeymap was set by prooftree-mode.el.  Now do it here.
(defvar prooftree-subkeymap (make-sparse-keymap))

(defvar old-prooftree-subkey (key-binding prooftree-subkey))

(define-key prooftree-mode-map prooftree-subkey prooftree-subkeymap)

(defconst prooftree-keys
; WARNING: Keep this in sync with the corresponding definition in
; key-interface.el.
  (list
   (list 'prooftree-subkeymap "z" old-prooftree-subkey)
   (list 'prooftree-subkeymap "c" 'checkpoint)
   (list 'prooftree-subkeymap "s" 'suspend-proof-tree)
   (list 'prooftree-subkeymap "r" 'resume-proof-tree)
   (list 'prooftree-subkeymap "g" 'goto-subgoal)
   (list 'prooftree-subkeymap "h" 'checkpoint-help)
   (list 'prooftree-subkeymap "?" 'checkpoint-help)
   (list 'prooftree-subkeymap "o" 'prooftree-select-other-frame)
   (list 'prooftree-subkeymap "b" 'visit-proof-tree)
   (list 'prooftree-subkeymap "B" 'visit-proof-tree-other-frame)))

(define-interface prooftree-mode	;mode
                  prooftree-mode-map	;mode-map
                  prooftree-menu-bar
		  nil			;menu-bar-remove
		  prooftree-popup-menu-value
		  prooftree-keys)

;; Just in case this file gets loaded after checkpointing has started.
;; (if (and (fboundp 'checkpoint)
;; 	 (bufferp (get-buffer "prooftree")))
;;     (save-excursion
;;       (set-buffer "prooftree")
;;       (if (not (equal major-mode 'prooftree-mode))
;; 	(prooftree-mode)
;; 	(run-hooks prooftree-mode-hook))))

(provide 'acl2-interface)

;; ======================================================================
;; TODO:
;;
;; ======================================================================
;; LOG:
;;



