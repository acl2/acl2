;; overkill.el - emacs support for overkill
;; Written by Jared Davis and Doug Harper


;; INTRODUCTION
;;
;; This file provides an emacs interface to the overkill build system, which
;; will monitor your build's progress.  You can add this to your .emacs file so
;; that it will be available, or use load-file to install it at your
;; convenience.
;;
;; After loading this file, simply invoke "M-x overkill" at the minibuffer, and
;; a new buffer named "overkill" will be created that will monitor your
;; Overkill build progress.  The buffer will automatically refresh itself every
;; five seconds (configurable below) with an updated display of which files
;; have been built successfully and so forth.
;;
;; When you are done with your build, you can type "M-x cancel-overkill" to
;; stop the timer loop.  (The buffer will remain, it just won't be updated).



;; CONFIGURATION
;;
;; You must properly configure the variables below in order for this system
;; to work:

;; overkill-directory
;; Enter the path to $(MAKEDIR)/overkill

(defconst overkill-directory "/rfs/proj/milsrtos/Users/jared/5/make/overkill")


;; overkill-buffer-name
;; Enter the name of the buffer to use (default: "overkill")

(defconst overkill-buffer-name "overkill")


;; overkill-delay
;; Enter the time to wait between updates, in seconds (default: 5)

(defconst overkill-delay 5)




;; IMPLEMENTATION
;;
;; You probably don't want to edit anything below this line, unless you are
;; wanting to change how the emacs interface is implemented.

(defconst overkill-display-script 
  (concat overkill-directory "/display.sh"))

(defconst overkill-results-file 
  (concat overkill-directory "/RESULTS"))

(defconst overkill-hosts-file 
  (concat overkill-directory "/HOSTS"))

(defconst overkill-books-file
  (concat overkill-directory "/BOOKS"))


(defun step-overkill ()

  ;; erase the update buffer
  (let ((original (current-buffer)))
    (switch-to-buffer overkill-buffer-name 'without-updating-history)
    (erase-buffer)
    (switch-to-buffer original 'without-updating-history))

  ;; call the display script
  (call-process overkill-display-script  ; script to invoke
		nil                      ; no stdin for display script
		overkill-buffer-name     ; buffer to send results to
		nil                      ; wait until done to display
		overkill-results-file    ; arg1 for display script
		overkill-hosts-file      ; arg2 for display script 
		overkill-books-file      ; arg3 for display script
		)

  ;; move to the top of the update buffer
  (let ((original (current-buffer)))
    (switch-to-buffer overkill-buffer-name 'without-updating-history)
    (goto-char (point-min))
    (switch-to-buffer original 'without-updating-history))
  )


(defvar overkill-timer)

(defun overkill ()
  (interactive)  
  (switch-to-buffer overkill-buffer-name)
  (setq overkill-timer (run-with-timer 0 5 'step-overkill)))

(defun cancel-overkill ()
  (interactive)
  (cancel-timer overkill-timer))

