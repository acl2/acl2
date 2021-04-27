; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE file in the main ACL2 source directory for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; DOCUMENTATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains code for real-time monitoring of ACL2 rewrites
; (Dynamically Monitoring Rewrites, or "dmr").  This file is automatically
; loaded by emacs-acl2.el.

; We thank Robert Krug for useful contributions.

; To start (or restart) dynamically monitoring rewrites:
;   control-t 1
; To stop dynamically monitoring rewrites:
;   control-t 2
;   or just hide the monitoring buffer

; See also "User-settable variables" below.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User-settable dmr variables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following may be set by the user to any positive number of seconds.
; If you set this, consider also setting Common Lisp variable *dmr-interval*.
(defvar *acl2-timer-display-interval*
  0.10)

(defvar *dmr-buffer-name*
  (concat "acl2-dmr-" (getenv "USER")))

(defvar *dmr-file-name*
; Keep this in sync with *dmr-file-name* in the ACL2 Common Lisp sources.
  (concat "/tmp/" *dmr-buffer-name*))

; See also "Debug" below, for advanced users.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Debug
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *dmr-debug-p* nil)
(defvar *dmr-debug-output* nil)
(defvar *dmr-debug-output-raw* nil)
(defun dmr-clear-debug ()
  (interactive)
  (when *dmr-debug-output*
    (setq *dmr-debug-output* nil))
  (when *dmr-debug-output-raw*
    (setq *dmr-debug-output-raw* nil)))
(defun dmr-write-debug ()
  (insert (format "%S" (reverse *dmr-debug-output*))))
(defun dmr-write-debug-raw ()
  (insert (format "%S" (reverse *dmr-debug-output-raw*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *dmr-delete-string*

; WARNING: Keep this in sync with corresponding ACL2 definition.

  "delete-from-here-to-end-of-buffer")

(defvar *dmr-delete-string-length*
  (length *dmr-delete-string*))

(defun acl2-start-of-region-to-be-deleted ()
  (goto-char (point-min))
  (and (search-forward *dmr-delete-string* nil t)
       (match-beginning 0)))

(defvar *dmr-previous-string* "")

(defun dmr-star-lines-to-end ()
  (let ((max-1 (1- (point-max))))
    (while (progn (end-of-line)
		  (< (point) max-1))
      (forward-char 1) ; past newline
      (delete-char 1) ; delete space
      (insert "*"))))

(defvar *dmr-finished-string*
  "  No proof is in progress.
")

(defun dmr ()
  (when (file-exists-p *dmr-file-name*)
    (let ((buf (get-buffer-create *dmr-buffer-name*)))
      (if (get-buffer-window buf) ; Can we see the buffer?
          (with-current-buffer buf
            (let ((saved-point (point)))
              (insert-file-contents-literally *dmr-file-name* nil nil nil t)
              (let* ((new-string (buffer-string))
                     (max (length new-string)))
                (if (and (<= *dmr-delete-string-length* max)
                         (equal (substring new-string
                                           0
                                           *dmr-delete-string-length*)
                                *dmr-delete-string*))

; This is the case where the proof has completed, indicated by nothing in the
; file before the delete string.

                    (progn (setq new-string *dmr-finished-string*)
                           (delete-region (point-min) (point-max))
                           (insert *dmr-finished-string*)
                           (setq *dmr-previous-string* nil))
                  (let ((common (and *dmr-previous-string*
                                     (compare-strings
                                      new-string 0 max
                                      *dmr-previous-string* 0 max))))
                    (if *dmr-debug-p*
                        (setq *dmr-debug-output-raw*
                              (cons (buffer-string) *dmr-debug-output-raw*)))
                    (setq *dmr-previous-string* new-string)
                    (let ((start (acl2-start-of-region-to-be-deleted)))
                      (and start (delete-region start (1+ max))))
                    (if (eq common t) ; very unlikely, given delete marker
                        (progn
                          (if (< saved-point (point-max))
                              (goto-char saved-point)
                            (goto-char (point-max)))
                          (if *dmr-debug-p*
                              (setq *dmr-debug-output*
                                    (cons (buffer-string) *dmr-debug-output*))))
                      (goto-char (if common
                                     (min (abs common) (point-max))
                                   (point-min)))
                      (beginning-of-line)
                      (if (< (point) (point-max))
                          (delete-char 1))
                      (let ((star-point (point)))
                        (insert "*")
                        (dmr-star-lines-to-end)
                        (if *dmr-debug-p*
                            (setq *dmr-debug-output*
                                  (cons (buffer-string) *dmr-debug-output*)))
                        (if (< saved-point star-point)
                            (goto-char saved-point)
                          (goto-char star-point)))))))))
        (acl2-stop-monitor)))))

(defvar *dmr-timer* nil)

(defun acl2-start-monitor ()
  (interactive)
  (when *dmr-timer*

; Restart the timer in case *acl2-timer-display-interval* has been changed.

    (cancel-timer *dmr-timer*))
  (setq *dmr-timer* (run-with-timer *acl2-timer-display-interval*
                                    *acl2-timer-display-interval*
                                    'dmr))
  (switch-to-buffer (get-buffer-create *dmr-buffer-name*)))

(defun acl2-stop-monitor ()
  (interactive)
  (when *dmr-timer*
    (if (string-match "XEmacs" emacs-version)
        (if (fboundp 'delete-itimer)
	    (delete-itimer *dmr-timer*)
	  (error "delete-itimer is unbound;
please contact matthew.j.kaufmann@gmail.com"))
      (cancel-timer *dmr-timer*))
    (setq *dmr-timer* nil)))

(defvar ctl-t-keymap)

; The following won't be necessary if emacs/emacs-acl2.el is loaded first.
; Keep this in sync with that code (the two should be identical).
(when (not (boundp 'ctl-t-keymap))

; This trick probably came from Bob Boyer, to define a new keymap; so now
; control-t is the first character of a complex command.
  (setq ctl-t-keymap (make-sparse-keymap))
  (define-key (current-global-map) "\C-T" ctl-t-keymap)

; Control-t t now transposes characters, instead of the former control-t.
  (define-key ctl-t-keymap "\C-T" 'transpose-chars)
  (define-key ctl-t-keymap "\C-t" 'transpose-chars)
  )

(define-key ctl-t-keymap "0" 'dmr-clear-debug)
(define-key ctl-t-keymap "1" 'acl2-start-monitor)
(define-key ctl-t-keymap "2" 'acl2-stop-monitor)
