;; May, 1994 [modified Oct., 1997]
;; Matt Kaufmann and Mike Smith

;; This file lets one attach a filter and a collection of buffers to a
;; process in emacs.  See mfm-acl2.el for an example of how to use the
;; utilities in this file.  It should work in emacs version 18, emacs version
;; 19 with comint, and version 19 with an old-style shell (Bill Schelter's
;; sshell.el).

;; If using this with buffers that use comint for processes, it's a good idea
;; to (setq mfm-comint-p t) in one's .emacs file.  Otherwise, this file uses
;; comint (i.e., mfm-comint-p is t) if and only if the emacs version is 19 or
;; later and Schelter's sshell is not present as a feature.

;; Possible future extensions:

; Consider saving the buffer's process filter before installing our
; own, and restoring it when executing stop-proof-tree.  This is also
; important to do when we change the *mfm-buffer*.

; Think about the effect of renaming a shell buffer.

; Create a way for #<\<e ... #>\> to cause the form to be read into
; emacs and evaluated.

(defvar mfm-emacs-version
  (if (and (boundp 'emacs-version)
           (stringp emacs-version)
           (< 1 (length emacs-version))
           (string-match "[0-9][0-9]" (substring emacs-version 0 2)))
      (string-to-number (substring emacs-version 0 2))
    (error "The file mfm.el works for emacs versions 18 and 19, but not yours.")))

(defvar mfm-comint-p
  (and (<= 19 mfm-emacs-version)
       (not (featurep 'sshell))))

; For the byte compiler:

(defvar last-input-end)
(defvar comint-last-input-end)
(defvar comint-output-filter-functions)
(defvar comint-last-output-start)

(defun mfm-update-last-input-end (nchars)
  (let ((end (if mfm-comint-p 
                 comint-last-input-end
               last-input-end)))
    (if (and end
             (marker-buffer end)
             (= (point) end))
        (set-marker end (- end nchars)))))

(defun mfm-update-last-output-start (ostart)
  (if mfm-comint-p
      (set-marker comint-last-output-start ostart)
    nil))

(defun mfm-force-mode-line-update ()
  (if mfm-comint-p
      (force-mode-line-update)
    nil))

; e.g., "*shell*"
(defvar *mfm-buffer* nil)

; The following is adapted from a contribution from Noah Friedman, from his
; ftelet mode.
(defun ftelnet-carriage-filter (string)
  (let* ((point-marker (point-marker))
         (proc (get-buffer-process (current-buffer)))
         (end (if proc (process-mark proc) (point-max)))
         (beg (or (and proc
                       (boundp 'comint-last-output-start)
                       comint-last-output-start)
                  (- end (length string)))))
    (goto-char beg)
    (while (search-forward "\C-m" end t)
      (delete-char -1))
    (goto-char point-marker)))

(defvar *mfm-secondary-filter-functions* '(ftelnet-carriage-filter))

(defvar *mfm-secondary-buffer* nil
  "This variable is NIL if we are not currently accumulating output
to the secondary buffer.  If we are its value is that buffer.")

(defvar *mfm-secondary-buffer-name-alist* nil)

; We were relying on the rarity of the breaking up of a string #<\<0 or
; #>\>  So far so good, said the guy falling past the 82nd floor....
; Broke.  So we are fixing it.

(defvar *mfm-protocol-start* "#"
  "Character used to start and stop redirection.")

(defun mfm-initial-secondary-start ()
  (format "#<[\\]<[%s]" 
          (apply 'concat
                 (mapcar 'char-to-string
                         (mapcar 'car
                                 (mapcar 'cdr
                                         *mfm-secondary-buffer-name-alist*))))))

(defvar *mfm-secondary-start*
  (mfm-initial-secondary-start))

(defvar *mfm-secondary-stop* "#>[\\]>")

; The value of *mfm-secondary-stop-len* should be the length of any string that
; matches *mfm-secondary-stop*.
(defvar *mfm-secondary-stop-len* 4)

(defvar *mfm-paused-buffers* nil)

(defvar *mfm-secondary-buffer-alist* nil)

(defun mfm-output-filter-functions ()
  (if mfm-comint-p
      (delete t comint-output-filter-functions)
    nil))

(defun mfm-paused-buffers (alist)
  (if (null alist)
      nil
    (if (memq 'pause (cdr (cdr (car alist))))
        (cons (car (car alist))
              (mfm-paused-buffers (cdr alist)))
      (mfm-paused-buffers (cdr alist)))))

(defun mfm-create-buffers-from-secondary-buffer-name-alist ()
  ;; This is OK even if some or all of the buffers already exist.
  (setq *mfm-secondary-buffer-alist*
	(mapcar (function (lambda (pair)
			    (cons (car (cdr pair))
				  (get-buffer-create (car pair)))))
		*mfm-secondary-buffer-name-alist*)))

(defun mfm-initialize-secondary-buffer-alist ()
  (mfm-create-buffers-from-secondary-buffer-name-alist)
  (setq *mfm-paused-buffers*
        (mfm-paused-buffers *mfm-secondary-buffer-name-alist*))
  (setq *mfm-secondary-start*
        (mfm-initial-secondary-start)))

(defvar *mfm-saved-tail* "")
(defvar *mfm-secondary-text* "")

(defun mfm-string-start (string)
  ;; Return nil or pair.
  ;; If pair = (n NIL), then we have a match for *mfm-secondary-start* at n.
  ;; If pair = (n T),   then we have a match for *mfm-protocol-start* at n, and
  ;;  n indexs one of the last four characters of string.
  (let ((start (string-match *mfm-secondary-start* string)))
    (cond (start (list start nil))
	  ((string-match *mfm-protocol-start* string (max (- (length string) 4) 0))
	   (list (match-beginning 0) t))
	  (t nil))))

(defun mfm-string-stop (string)
  ;; Return nil or pair.
  ;; If pair = (n NIL), then we have a match for *mfm-secondary-stop* at n;
  ;; elseif pair = (n T), then we have a match for *mfm-protocol-start* at n,
  ;; and n indexes one of the last four characters of string.
  (let ((stop (string-match *mfm-secondary-stop* string)))
    (cond (stop (list stop nil))
	  ((string-match *mfm-protocol-start*
                         string
                         (max (- (length string) 3) 0))
	   (list (match-beginning 0) t))
	  (t nil))))

(defun mfm-output-filter (process string)
  ;; At this point we need to check if secondary start or stop
  ;; is contained in string.
  ;; Previously error prone in case of xxx START xx START xx STOP xx STOP xx...
  ;; Modified to handle start and stop broken across successive strings.
  ;; E.g., xxxSTA RTxxxx xxxxST OPxxx
  (setq string (concat *mfm-saved-tail* string))
  (setq *mfm-saved-tail* "")
  (if *mfm-secondary-buffer*
      ;; We are currently writing to one of the secondary buffers.
      (let ((stop (mfm-string-stop string)))
	(cond ((null stop)
	       (setq *mfm-secondary-text*
		       (concat *mfm-secondary-text* string)))
	      ((null (car (cdr stop)))
	       (setq stop (car stop))
               ;; Write the accumulated text, including the appropriate part of
               ;; STRING.  First write the current point as the first line.
	       (mfm-output-to-secondary
                *mfm-secondary-buffer*
                (concat *mfm-secondary-text*
                        (substring string 0 stop)))
               (setq *mfm-secondary-buffer* nil)
	       (setq *mfm-secondary-text* "")
	       (mfm-output-filter
		process
		(substring string (+ stop *mfm-secondary-stop-len*))))
	      ((car (cdr stop))
	       (setq stop (car stop))
	       ;; May or may not be done.
	       ;; Add the accumulated text to *mfm-secondary-text*.
	       (setq *mfm-secondary-text*
		       (concat *mfm-secondary-text* (substring string 0 stop)))
	       (setq *mfm-saved-tail* (substring string stop)))))

    (let* ((start (mfm-string-start string))
           (end (and start (match-end 0))))
      (cond ((null start) (mfm-output-to-primary process string))
            ((null (car (cdr start)))
	     (setq start (car start))
             ;; Write the appropriate part of STRING to primary output
             ;; Then enter secondary buffer mode.
             (mfm-output-to-primary process
                                    (substring string 0 start))
             (setq *mfm-secondary-buffer*
                   (cdr (assq (aref string (1- end))
                              *mfm-secondary-buffer-alist*)))
             (if (null (buffer-name *mfm-secondary-buffer*))
                 (progn (mfm-create-buffers-from-secondary-buffer-name-alist)
                        (setq *mfm-secondary-buffer*
                              (cdr (assq (aref string (1- end))
                                         *mfm-secondary-buffer-alist*)))))
             (mfm-output-filter process (substring string end)))
	    ((car (cdr start))
	     (setq start (car start))
	     (mfm-output-to-primary process (substring string 0 start))
	     (setq *mfm-saved-tail* (substring string start)))))))

(defun mfm-output-to-primary (process string)
  ;; First check for killed buffer
  (let ((oprocbuf (process-buffer process)))
    (if (and oprocbuf (buffer-name oprocbuf))
        (let ((obuf (current-buffer))
              (opoint nil) (obeg nil) (oend nil))
          (set-buffer oprocbuf)
          (setq opoint (point))
          (setq obeg (point-min))
          (setq oend (point-max))
          (let ((buffer-read-only nil)
                (nchars (length string))
                (ostart nil))
            (widen)
            (goto-char (process-mark process))
            (setq ostart (point))
            (if (<= (point) opoint)
                (setq opoint (+ opoint nchars)))
            ;; Insert after old_begv, but before old_zv.
            (if (< (point) obeg)
                (setq obeg (+ obeg nchars)))
            (if (<= (point) oend)
                (setq oend (+ oend nchars)))
            (insert-before-markers string)
            ;; Don't insert initial prompt outside the top of the window.
            (if (= (window-start (selected-window)) (point))
                (set-window-start (selected-window) (- (point) (length string))))
            (mfm-update-last-input-end nchars)
            (mfm-update-last-output-start ostart)
            (set-marker (process-mark process) (point))
            (mfm-force-mode-line-update))

          (narrow-to-region obeg oend)
          (goto-char opoint)
          (ftelnet-carriage-filter string)
          (let ((functions (mfm-output-filter-functions)))
            (while functions
              (funcall (car functions) string)
              (setq functions (cdr functions))))
          (set-buffer obuf)))))

(defun member-equal (a lst)
  ;; because member is not defined in version 18
  (if (null lst)
      nil
    (if (equal a (car lst))
        lst
      (member-equal a (cdr lst)))))

(defun mfm-paused-p (buffer-name)
  (member-equal buffer-name *mfm-paused-buffers*))

(defun mfm-output-to-secondary (oprocbuf string)
  ;; First check that buffer exists.
  (if (and oprocbuf (buffer-name oprocbuf))
      (let ((obuf (current-buffer)))
        (if ; Stop output to "pause" buffers.
            (mfm-paused-p (buffer-name oprocbuf))
            nil
          (set-buffer oprocbuf)
          ;; Clear buffer before displaying string.
          (delete-region (point-min) (point-max))
          (let ((buffer-read-only nil))
            (insert string))
          (mfm-force-mode-line-update)
          (let ((functions *mfm-secondary-filter-functions*))
            (while functions
              (funcall (car functions) string)
              (setq functions (cdr functions))))
          (set-buffer obuf)))))

(defun mfm-abort-secondary-buffer ()

  "Flush the text currently being sent to the secondary buffer and
resume sending text to primary buffer.  This does not stop or pause
the sending of output to secondary buffers; it merely flushes the
current stream being sent to a secondary buffer (if any)."

  (interactive)
  (setq *mfm-secondary-buffer* nil)
  (setq *mfm-saved-tail* "")
  (setq *mfm-secondary-text* ""))

(defun mfm-interrupt-subjob ()
  (interactive)
  (progn
    (mfm-abort-secondary-buffer)
    ;; use funcall here to avoid confusing the compiler
    (if mfm-comint-p
        (if (eq major-mode 'telnet-mode)
            (funcall 'telnet-interrupt-subjob)
          (funcall 'comint-interrupt-subjob))
      (funcall 'interrupt-shell-subjob))))

(defun mfm-set-keymap-interrupt ()
  (save-excursion
    (if *mfm-buffer*
        (progn (set-buffer *mfm-buffer*)
               (define-key (current-local-map)
                 "\C-C\C-C"
                 'mfm-interrupt-subjob)))))

(defun mfm-select-buffer-window (buffer)

  "Select a window containing the given buffer if there is one; otherwise, make
the current window fill the frame, and select the indicated buffer."
  (let ((w (get-buffer-window buffer)))
    (if w
        (select-window w)
      (progn (delete-other-windows)
             (switch-to-buffer buffer)))))

(provide 'mfm)

