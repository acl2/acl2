
;; Load the emacs interface for acl2 when it is running in a 
;; shell buffer in shell-mode.
;; May 13 94 Kaufmann & MKSmith

;; ASSUMPTION: load path contains the directory this file resides in.

(defvar *acl2-user-map-interface*
  '((prooftree-mode-map keys)))

(require 'key-interface)

;; (defvar *selected-mode-map*)
(defvar inferior-acl2-buffer)

(defun initialize-mfm-buffer-variables ()
  (setq *mfm-buffer* "*shell*")
  ;; (setq *selected-mode-map* shell-mode-map)
  (setq inferior-acl2-buffer *mfm-buffer*))

(defvar shell-mode-hook nil)
(setq shell-mode-hook
      (extend-hook shell-mode-hook 'initialize-mfm-buffer-variables))

(defun start-shell-acl2 ()
  (interactive)
  (require 'shell)
  ;; Looks redundant.
  ;;(setq shell-mode-hook
	;;(extend-hook 'initialize-mfm-buffer-variables shell-mode-hook))
  (shell))
