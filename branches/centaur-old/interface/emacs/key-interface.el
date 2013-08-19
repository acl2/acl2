
;; Add key interface for prooftree buffers.
;; March 3 95 MKS 

;; ----------------------------------------------------------------------
;; USER SETTINGS

;; (defvar *acl2-proof-tree-height* 17)
;; (defvar *checkpoint-recenter-line* 3)

;; ----------------------------------------------------------------------
;; Load all of the various acl2-interface files, if necessary.

(load "mfm-acl2.el")			;(require 'mfm-acl2)

;; (load "interface-macros.el")		;(require 'interface-macros)
;; Replaced by the following defvar and four functions, which is all this 
;; file used from interface macros.

;; Begin insert

(defvar mode-menu-alist nil)

;; WARNING:  Be sure that if should-i-install, update-mode-menu-alist,
;; remove-mode-menu-alist, define-mode-keys, or extend-hook is changed, then it
;; is also changed in key-interface.el.

(defun should-i-install (mode feature)
  ;; mode is mode-name
  (memq feature (cdr (assoc mode mode-menu-alist))))

(defun update-mode-menu-alist (l)
  (if (not (consp (car l)))
      (setq l (cons l nil)))
  (setq mode-menu-alist 
	(append l (remove-mode-menu-alist mode-menu-alist l))))

(defun remove-mode-menu-alist (alist l)
  (cond ((null alist) l)
	((assoc (car (car alist)) l)
	 (remove-mode-menu-alist (cdr alist) l))
	(t (cons (car alist) (remove-mode-menu-alist (cdr alist) l)))))

(defun define-mode-keys (mode-map-name mode-map keys)
  ;; An entry in keys may have two forms:
  ;; (key function)     
  ;; (keymap key function)
  ;; The second allows you to create subkeymaps, e.g. Control-Z
  (if (should-i-install mode-map-name 'keys)
      (mapcar
       (function (lambda (x)
		   (if (equal (length x) 2)
		       (define-key mode-map (car x) (car (cdr x)))
		       (if (keymapp (eval (car x)))
			   (define-key (eval (car x)) (car (cdr x)) (car (cdr (cdr x))))
			   (error
			    (format "Keymap %s not defined in mode %s" (car x) (car mode-map)))))))
       keys)))

(defun extend-hook (hook entry)
  ;; Add an entry onto a mode-hook, being sensitive to the
  ;; stupid Emacs permission for it to be a function or list
  ;; of functions.
  (cond ((null hook) (list entry))
	((symbolp hook) (if (not (equal entry hook)) (list hook entry) hook))
	((not (consp hook)) 
	 (message (format "Strange hook, %s, replaced by %s." hook entry))
	 (list entry))
	((equal (car hook) 'lambda)
	 (list hook entry))
	((member-equal entry hook) hook)
	(t (append hook (list entry)))))

;; end insert

(update-mode-menu-alist *acl2-user-map-interface*)

;; Defined in mfm-acl2 so that checkpoint-help can use it.
(defvar prooftree-subkey)
(setq prooftree-subkey "\C-z")

;; prooftree-subkeymap was set by prooftree-mode.el.  Now do it here.
(defvar prooftree-subkeymap (make-sparse-keymap))

(defvar old-prooftree-subkey (global-key-binding prooftree-subkey))

(define-key (current-global-map) prooftree-subkey prooftree-subkeymap)

(defconst prooftree-keys
; WARNING: Keep this in sync with the corresponding definition in
; acl2-interface.el.
  (list
   (list 'prooftree-subkeymap "z" old-prooftree-subkey)
   (list 'prooftree-subkeymap "c" 'checkpoint)
   (list 'prooftree-subkeymap "s" 'suspend-proof-tree)
   (list 'prooftree-subkeymap "r" 'resume-proof-tree)
   (list 'prooftree-subkeymap "g" 'goto-subgoal)
   (list 'prooftree-subkeymap "h" 'checkpoint-help)
   (list 'prooftree-subkeymap "?" 'checkpoint-help)
   (list 'prooftree-subkeymap "o" 'select-other-frame-with-focus)
   (list 'prooftree-subkeymap "b" 'visit-proof-tree)
   (list 'prooftree-subkeymap "B" 'visit-proof-tree-other-frame)))         

(define-mode-keys 'global (current-global-map) prooftree-keys)

(provide 'key-interface)
