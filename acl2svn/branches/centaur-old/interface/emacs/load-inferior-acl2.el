
;; Load the emacs interface for acl2 and start it running in an
;; inferior-acl2 buffer.

;; May 13 94 Kaufmann & MKSmith
;; Sep 25 94 MKSmith

;; THIS GOES IN THE USER'S .emacs FILE,
;; after loadpath is set to include this dir.

; BEGIN INSERT after this line
; 
; (autoload 'run-acl2
;   "top-start-inferior-acl2" 
;   "Open communication between acl2 running in shell and prooftree." t)
;
;  END INSERT before this line

(require 'acl2-interface)		;loads everything else

(defun initialize-mfm-buffer-variables ()
  (setq *mfm-buffer* inferior-acl2-buffer))

(setq inferior-acl2-mode-hook
	(extend-hook inferior-acl2-mode-hook 'initialize-mfm-buffer-variables))

(defun load-inferior-acl2 ()
  (interactive)
  (run-acl2 inferior-acl2-program))
