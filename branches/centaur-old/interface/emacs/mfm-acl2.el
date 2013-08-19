;; May, 1994
;; Matt Kaufmann and Mike Smith

(require 'mfm)

;; Possible future extensions:

; Arrange that stop-proof-tree sends an appropriate string to the ACL2
; process, with both #+acl2-loop-only and #-acl2-loop-only in it, so
; that the proof-tree output is inhibited in ACL2 whether we're in a
; break or not.  Similarly for start-proof-tree.  If that sort of thing
; works, consider options for suspend-proof-tree and resume-proof-tree
; that interrupt and resume an ACL2 proof.

; We need to be able to distinguish GNU emacs 19 and its descendents from
; 18 and lemacs and ...
; Fortunately, mfm.el already provides this test by setting 
; mfm-emacs-version to the version number if it can figure it out.

; From mfm.el, we need to re-assign this value:
(defconst *mfm-secondary-buffer-name-alist* '(("prooftree" ?0)))

(defconst *acl2-proof-tree-height-default* 17)
(defconst *checkpoint-recenter-line-default* 3)
; The following are set by start-proof-tree.
(defvar *acl2-proof-tree-height* *acl2-proof-tree-height-default*)
(defvar *checkpoint-recenter-line* *checkpoint-recenter-line-default*)

(defvar *proof-tree-start-string* "\n<< Starting proof tree logging >>"
  "Must match the corresponding ACL2 string; do not change this!")

(defvar *last-acl2-point-max* nil)

; The last process saved when mfm-output-filter was installed:
(defvar *saved-acl2-process-filter*)

; *prooftree-marker* is a marker into the prooftree buffer, or nil.  It need
; not have any meaningful position; such position would be stored in
; overlay-arrow-position.  The only reason we have *prooftree-marker* is to
; avoid the need to keep creating new markers.
(defvar *prooftree-marker* nil)

; *** MOVED TO acl2-interface.
;(defvar ctl-z-keymap (make-sparse-keymap))
;(defvar old-ctl-z-key (key-binding "\C-Z"))

; The following is an emacs variable that we appropriate.
(setq overlay-arrow-string ">")

(defun save-last-acl2-point-max (string)
  (if (and *mfm-secondary-buffer*
           (equal (buffer-name *mfm-secondary-buffer*) "prooftree"))
      (setq *last-acl2-point-max*
            (save-excursion
              (set-buffer *mfm-buffer*)
              (point-max)))))

(defun clear-overlay-from-prooftree-buffer (string)
  (if (not (mfm-paused-p "prooftree"))
      (setq overlay-arrow-position nil)))

(defmacro message-beep (&rest args)
  (list 'progn
        '(beep)
        (cons 'message args)))

(defun initialize-proof-tree-windows (do-init)
  (or (and (not do-init)
           *acl2-proof-tree-height*)
      (setq *acl2-proof-tree-height*
            (if (numberp *acl2-proof-tree-height*)
                (read-from-minibuffer
                 (format "Height of proof tree window (currently %d): "
                         *acl2-proof-tree-height*)
                 (format "%d" *acl2-proof-tree-height*)
                 nil t)
              (read-from-minibuffer
               (format "Height of proof tree window (default %d):"
                       *acl2-proof-tree-height-default*)
               (format "%d" *acl2-proof-tree-height-default*)
               nil t)))))

(defun initialize-acl2-buffer-process (do-init)
  ;; returns non-nil upon success, nil upon failure
  (let* ((proc-try (and (not do-init)
                        *mfm-buffer*
                        (get-buffer-process *mfm-buffer*)))
         (proc
          (or proc-try
              (and
               (setq *mfm-buffer*
                     (if (stringp *mfm-buffer*)

; Keep the following in sync with stop-proof-tree

                         (let ((proc (get-buffer-process *mfm-buffer*)))
                           (if (and proc
                                    (boundp '*saved-acl2-process-filter*))
                               ;;so, we've done at least one save
                               (set-process-filter proc *saved-acl2-process-filter*))
                           (read-from-minibuffer
                            (format "ACL2 buffer (currently %s): "
                                    *mfm-buffer*)
                            *mfm-buffer* nil))
                       (read-from-minibuffer "ACL2 buffer: " "*shell*" nil)))
               (get-buffer-process *mfm-buffer*)))))
    (and proc
         (let ((fltr (process-filter proc)))
           (if (not (eq fltr 'mfm-output-filter))
               (progn (setq *saved-acl2-process-filter* fltr)
                      (set-process-filter proc 'mfm-output-filter)))
           (if (not (memq 'save-last-acl2-point-max
                          *mfm-secondary-filter-functions*))
               (setq *mfm-secondary-filter-functions*
                     (cons 'save-last-acl2-point-max
                           *mfm-secondary-filter-functions*)))
           (if (not (memq 'clear-overlay-from-prooftree-buffer
                          *mfm-secondary-filter-functions*))
               (setq *mfm-secondary-filter-functions*
                     (cons 'clear-overlay-from-prooftree-buffer
                           *mfm-secondary-filter-functions*)))
           (mfm-set-keymap-interrupt)
           t))))

(defun initialize-checkpoint-recenter-line (do-init)
  (or (and (not do-init)
           *checkpoint-recenter-line*)
      (setq *checkpoint-recenter-line*
            (if (numberp *checkpoint-recenter-line*)
                (read-from-minibuffer
                 (format "Line for top of checkpoint display (currently %d): "
                         *checkpoint-recenter-line*)
                 (format "%d" *checkpoint-recenter-line*)
                 nil t)
              (read-from-minibuffer
               (format "Line for top of checkpoint display (default %d): "
                       *checkpoint-recenter-line-default*)
               (format "%d" *checkpoint-recenter-line-default*)
               nil t)))))

;; CHECKPOINT-HELP assumes these keys have been bound.
;; So we defvar it here.
(defvar prooftree-subkey "\C-Z")

(defun checkpoint-help ()
  "Provides information about proof-tree/checkpoint tool.
Use `C-h d' to get more detailed information for specific functions."
  (interactive)
  ;; Here is how to do it in emacs 19:
  ;; (describe-bindings "\C-Z")
  ;; But in emacs 18, describe-bindings doesn't take an arg, so:
  (with-output-to-temp-buffer "*Help*"
    (princ "Checkpoint help.  
Use `C-h d' to get information on specific functions.

default key(s)  binding
--------------  -------

C-z ?, C-z h    checkpoint-help
C-z g           goto-subgoal
C-z r           resume-proof-tree
C-z s           suspend-proof-tree
C-z c           checkpoint
C-z o           select-other-frame-with-focus
C-z b           visit-proof-tree
C-z B           visit-proof-tree-other-frame
C-z z           [old C-z; suspends emacs or iconifies frame]
")))

;; *** INITIALIZE-PROOF-TREE-KEYS handled by acl2-interface.el
;; Actually, the DEFINE-INTERFACE macro sets up the mode hook for
;; prooftree mode.

;;; The following code sets up the prooftree in prooftree mode, which is just
;;; Fundamental mode.  But this allows us to use the prooftree-mode-map and
;;; prooftree-mode-hook to set up menu and moused based interactions in a
;;; principled fashion.

(defvar prooftree-mode-map (make-keymap))

(defvar prooftree-mode-hook '()
  "*Hook for customizing inferior prooftree mode.")

;;; Example: (define-key prooftree-mode-map "\C-Q" 'foo)

(defun prooftree-mode () 
  "Major mode for interacting with prooftree buffers.

\\{prooftree-mode-map}

Customization:  Entry to this mode runs the hooks on `prooftree-mode-hook'.
"
  (interactive)
  (setq major-mode 'prooftree-mode)
  (setq mode-name "Prooftree")
  (use-local-map prooftree-mode-map)
  (run-hooks 'prooftree-mode-hook))

;;; end of prooftree-mode.

(defun start-proof-tree-setup ()
  (delete-other-windows)
  (switch-to-buffer *mfm-buffer*)
  (split-window-vertically *acl2-proof-tree-height*)
  (switch-to-buffer "prooftree")
  (prooftree-mode)
  (other-window 1))

(defun start-proof-tree (do-init)

  "Start the ACL2 proof tree display.  With an argument, queries for values of
user-settable parameters.  This also queries for the ACL2 buffer the first time
it is called."

  (interactive "P")
  (initialize-proof-tree-windows do-init)
  (initialize-checkpoint-recenter-line do-init)
  (if (initialize-acl2-buffer-process do-init)
      (progn (setq *mfm-secondary-buffer* nil)
             (mfm-initialize-secondary-buffer-alist)
             (start-proof-tree-setup))
      (error "No process; start shell or inferior-acl2 and start-proof-tree again."))

; Handled by acl2-interface.el:
; (if (not (equal ctl-z-keymap (key-binding "\C-Z")))
;     (initialize-proof-tree-keys do-init))
  )

(defun start-proof-tree-noninteractive (mfm-buffer)

  "A typical call of this function is:

  (start-proof-tree-noninteractive \"*shell*\")

You may find it useful to put the above form followed by some version of the
following forms in your .emacs file, assuming that you have loaded ACL2 file
emacs/emacs-acl2.el.  The result should be the start of a new frame (perhaps
after you click in the initial emacs window) to the side of the first frame,
with the \"prooftree\" buffer displayed in the new frame.

  (cond ((and (eq window-system 'x)
              (fboundp 'x-display-pixel-width)
              (= (x-display-pixel-width) 2048) ; for a wide monitor
              )
         (delete-other-windows)
         (if (boundp 'emacs-startup-hook) ; false in xemacs
             (push 'new-prooftree-frame emacs-startup-hook))))"

; Typical call:
; 
  (setq *mfm-buffer* mfm-buffer)
  (start-proof-tree nil))

(defun stop-proof-tree ()

  "Stop the ACL2 proof tree display, and delete all windows except for one,
which will contain the ACL2 buffer, emacs variable *mfm-buffer*.  See also
suspend-proof-tree."

  (interactive)
  (let ((proc (get-buffer-process *mfm-buffer*)))
    (if (not proc)
        (message-beep "No process for ACL2 buffer (emacs variable *mfm-buffer*), %s."
		      *mfm-buffer*)
      (if (boundp '*saved-acl2-process-filter*) ;so, we've done at least one save
          (set-process-filter proc *saved-acl2-process-filter*))
      (delete-other-windows)
      (switch-to-buffer *mfm-buffer*))))

(defun suspend-proof-tree (&optional suppress-message)
  ;; Returns non-nil if and only if anything happens.

  "Freeze the contents of the \"prooftree\" buffer, until
resume-proof-tree is invoked.  Unlike stop-proof-tree, the only effect
of suspend-proof-tree is to stop putting characters into the
\"prooftree\" buffer; in particular, strings destined for that buffer
continue NOT to be put into the primary buffer, which is the value of
the emacs variable *mfm-buffer*."

  (interactive)
  (if (not (mfm-paused-p "prooftree"))
      (progn (setq *mfm-paused-buffers*
                   (cons "prooftree" *mfm-paused-buffers*))
             (or suppress-message
                 (message "suspending prooftree"))
             t)
    (or suppress-message
        (message-beep "prooftree is already suspended"))
    nil))

(defun remove1-equal-rec (elt lst)
  (if (null lst)
      lst
    (if (equal elt (car lst))
        (cdr lst)
      (cons (car lst) (remove1-equal-rec elt (cdr lst))))))

(defun remove1-equal (elt lst)
  (if (member-equal elt lst)
      (remove1-equal-rec elt lst)
    lst))

(defun visit-proof-tree ()
  "Switch to the proof tree buffer in another window unless there is only one
window, in which case swtich in the current window."
  (interactive)
  (if (< 1 (count-windows))
      (other-window 1))
  (switch-to-buffer "prooftree"))

(defun resume-proof-tree (&optional not-eob-p suppress-message)
; Returns non-nil if and only if anything happens.

  "Resume original proof tree display, re-creating buffer
\"prooftree\" if necessary.  See also suspend-proof-tree.  With prefix
argument:  push the mark, do not modify the windows, and move point to
end of *mfm-buffer*."

  (interactive "P")
  (if (not (get-buffer "prooftree"))
      (mfm-create-buffers-from-secondary-buffer-name-alist))
  (if (not not-eob-p)
      (progn (push-mark (point) nil)
             (goto-char (point-max))
             (start-proof-tree-setup)))
  (if (mfm-paused-p "prooftree")
      (progn
        (setq *mfm-paused-buffers*
              (remove1-equal "prooftree" *mfm-paused-buffers*))
        (or suppress-message
            (if not-eob-p
                (message "resuming prooftree")
              (message "mark set; resuming prooftree")))
        t)
    (or suppress-message
        (if not-eob-p
            (message "prooftree not currently suspended")
          (message "mark set; prooftree not currently suspended")))
    nil))

(defun search-backward-point (string &optional bound no-error repeat-count)
  ;; Same as search-backward in emacs 19, but not in emacs 18 -- except,
  ;; saves excursion.
  (save-excursion
    (search-backward string bound no-error repeat-count)
    (point)))

(defun position-of-checkpoint (checkpoint-string)
  (save-excursion
    (let* ((case-fold-search nil)
           (bound (search-backward-point *proof-tree-start-string* nil t)))
      (if bound
          ;; We treat "*3.4" much differently from "Subgoal 4" or "Goal''".
          ;; The assumption is that the first occurrence of such a string,
          ;; without the trailing slash, is when the goal is pushed; the second
          ;; occurrence is therefor what we want.
          (if (equal (aref checkpoint-string 0) ?*)
              (progn
                (goto-char bound)
                (if (re-search-forward
                     (format "%s[.]?[^./0-9]" checkpoint-string)
                     nil t 2)
                    (let ((saved-point (match-beginning 0)))
                      ;; make sure we're still in the same proof!
                      (and (equal (search-backward-point
                                   *proof-tree-start-string* nil t)
                                  bound)
                           (progn (goto-char saved-point)
                                  (beginning-of-line)
                                  (point))))))
            (if (search-backward (format "\n%s\n" checkpoint-string) bound t)
                (progn (forward-line 1)
                       (point))
              (and (equal checkpoint-string "Goal")
                   bound)))))))

(defun checkpoint-on-line ()
  (let ((bound (save-excursion
                 (end-of-line)
                 (point)))
	(case-fold-search nil))
    (save-excursion
      (beginning-of-line)
      ;; Pretty fancy stuff -- we take special care to let double-quote (")
      ;; terminate the goal name, since goal names sometimes appear in
      ;; double-quotes (as in hints).  Note that we are happy to have regular
      ;; expressions that match too much, as long as we find it rare that they
      ;; do so.
      (if (or (re-search-forward
               "\\(\\[[^\n]+\\]\\)?Goal[^ \n\",]*\\(,\\| \\|$\\|\"\\)"
               bound t)
              (re-search-forward
               "\\(\\[[^\n]+\\]\\)?Subgoal [^ \n\",]*\\(,\\| \\|$\\|\"\\)"
               bound t)
              (re-search-forward
               "[*][1-9][0-9]*\\([.][0-9]+\\)*"
               bound t))
          (let* ((beg (match-beginning 0))
                 (end (match-end 0))
                 (last-char (char-after (1- end))))
            (buffer-substring beg
                              (if (memq last-char '(?\n ?\ ?\" ?\,))
                                  (1- end)
                                end)))))))

(defun checkpoint-from-prooftree-buffer-1 (arg)
  ;; assumes that we're in the exposed prooftree buffer if there is one
  (if (equal arg 0)
      (progn (set-buffer "prooftree")
             (beginning-of-buffer)))
  (prog1 (or (progn (beginning-of-line)
                    (and (looking-at "c")
                         (checkpoint-on-line)))
             (if (search-forward "\nc" nil t)
                 (checkpoint-on-line)
               (goto-char (point-min))
               (and (search-forward "\nc" nil t)
                    (checkpoint-on-line))))
    (forward-line)))

(defun checkpoint-from-prooftree-buffer (buff arg)
  ;; As a side effect, advances one line past the checkpoint found (or, stays
  ;; at the bottom).
  (let ((obuff (current-buffer)))
    (if buff
        (if (equal (buffer-name obuff) "prooftree")
            (checkpoint-from-prooftree-buffer-1 arg)
          (let ((w (get-buffer-window buff)))
            (if w
                (let ((old-w (get-buffer-window obuff)))
                  (select-window w)
                  (prog1
                      (checkpoint-from-prooftree-buffer-1 arg)
                    (select-window old-w)))
              (progn
                ;; This is the only way I've found to move the point.
                (switch-to-buffer buff)
                (prog1
                    (checkpoint-from-prooftree-buffer-1 arg)
                  (switch-to-buffer obuff))))))
      (message-beep "Buffer prooftree not found.")
      nil)))

(defun goto-subgoal-message (new-point saved-point-max)
  (if (or (= new-point saved-point-max)
          (not (save-excursion
                 (forward-line 2) ;in case we're looking at "Goal"
                 (search-forward *proof-tree-start-string* nil t))))
      (message "Point pushed;  Moved to goal in final proof in ACL2 buffer.")
    (message "Point pushed;  Moved to goal in already completed proof.")))

(defun ping-buffer ()
  (insert " ")
  (backward-delete-char 1))

(defun update-prooftree-overlay ()
  ;; Be sure to redisplay after calling this function, or else the overlay may
  ;; not appear.
  (save-excursion
    (if (not (and (markerp *prooftree-marker*)
		  (marker-buffer *prooftree-marker*)))
	(setq *prooftree-marker* (make-marker)))
    (set-buffer "prooftree")
    (save-excursion
      (forward-line -1)
      (setq overlay-arrow-position
            (let ((overlay-point
                   (let ((point (point)))
                     (if (equal point (point-min))
                         nil
                       point))))
              (if overlay-point
                  (set-marker *prooftree-marker*
                              overlay-point
                              (get-buffer "prooftree"))
                nil)))
      (ping-buffer))))

(defun switch-to-mfm-buffer ()
  (let ((w (get-buffer-window *mfm-buffer* t)))
    (cond ((window-live-p w)
	   (select-window w)
	   (let ((focus-follows-mouse nil))
	     (select-frame-set-input-focus (window-frame w))))
	  (t
	   (if (let ((current-frame
		      (window-frame (get-buffer-window (current-buffer)))))
		 (and current-frame
		      (equal (frame-parameter current-frame 'name)
			     "prooftree-frame")))
	       (select-other-frame-with-focus))
	   (switch-to-buffer *mfm-buffer*)))))

(defun goto-subgoal (checkpoint-string &optional bound)

  "Go to the specified subgoal in the ACL2 buffer (emacs variable *mfm-buffer*)
that lies closest to the end of that buffer -- except if the current buffer is
\"prooftree\" when this command is invoked, the subgoal is the one from the
proof whose tree is displayed in that buffer.  A default is obtained, when
possible, from the current line of the current buffer.

If there is more than one frame and *mfm-buffer* is displayed in some frame,
then that frame is made the frame with the cursor, where the the specified goal
is shown.  Otherwise, if the current frame is named \"prooftree-frame\" then we
move to another frame to display the goal in *mfm-buffer*."

  (interactive
   (list (read-from-minibuffer "Goal name: " (checkpoint-on-line))))
  (let ((bound-supplied-p bound)
	(bound (or bound
		   (and (equal (buffer-name (current-buffer)) "prooftree")
			*last-acl2-point-max*)))
	saved-point-max)
    (let ((new-point
	   (save-excursion
	     (set-buffer *mfm-buffer*)
	     (setq saved-point-max (point-max))
	     (goto-char (if bound (min (+ 100 bound) saved-point-max) saved-point-max))
	     (and checkpoint-string
		  (position-of-checkpoint checkpoint-string)))))
      (if new-point
	  (progn
	    (switch-to-mfm-buffer)
	    (push-mark (point))
	    (goto-char new-point)
	    (recenter *checkpoint-recenter-line*)
	    (if bound-supplied-p
		(update-prooftree-overlay)
	      (setq overlay-arrow-position nil))
	    (goto-subgoal-message new-point saved-point-max))
	(message-beep
	 (format "Cannot find goal named \"%s\"." checkpoint-string))))))

(defun checkpoint (keep-suspended-p)

  "Go to a checkpoint, as displayed in the \"prooftree\" buffer with
the character \"c\" in the first column.  With non-zero prefix
argument:  move the point in the ACL2 buffer (emacs variable
*mfm-buffer*) to the first checkpoint displayed in the \"prooftree\"
buffer, suspend the proof tree (see suspend-proof-tree), and move the
cursor below that checkpoint in the \"prooftree\" buffer.  Without a
prefix argument, go to the first checkpoint named below the point in
the \"prooftree\" buffer (or if there is none, to the first
checkpoint).  Note however that unless the proof tree is suspended or
the ACL2 proof is complete or interrupted, the cursor will be
generally be at the bottom of the \"prooftree\" buffer each time it is
modified, which causes the first checkpoint to be the one that is
found.

If the prefix argument is 0, move to the first checkpoint but do not
keep suspended."

  (interactive "P")
  (let ((suspended-p (suspend-proof-tree t))
        (buff (get-buffer "prooftree")))
    (if *mfm-buffer*
        (let ((checkpoint-name (and buff
                                    (checkpoint-from-prooftree-buffer
				     buff keep-suspended-p))))
          (if checkpoint-name
              (goto-subgoal checkpoint-name *last-acl2-point-max*)
            (message-beep "Cannot find a checkpointed goal."))
          (if (and (not keep-suspended-p)
                   suspended-p)
              (resume-proof-tree t t)))
      (if (and (not keep-suspended-p)
               suspended-p)
          (resume-proof-tree t t))
      (message-beep "There is no active ACL2 buffer"))))

(if (not (fboundp 'select-frame-set-input-focus)) ; xemacs
    (defun select-frame-set-input-focus (frame)
      (focus-frame frame)))

(defun select-other-frame-with-focus ()
  "Switch to another frame (which is created if necessary), and make it the one
that contains the cursor."
  (interactive)
  (let ((other-frame (get-other-frame))
	;; So that select-frame-set-input-focus calls x-focus-frame:
        (focus-follows-mouse nil))
    (select-frame-set-input-focus other-frame)))

(if (not (fboundp 'frame-parameter)) ; xemacs
    (defun frame-parameter (frame sym)
      (frame-property frame sym)))

(defun my-select-frame-by-name (frame-name)

;;; Like select-frame-by-name but without causing an error.

  (let ((x (frame-list))
	ans)
    (while x
      (cond ((equal (frame-parameter (car x) 'name)
		    frame-name)
	     (setq ans (car x))
	     (setq x nil)))
      (setq x (cdr x)))
    ans))

(defun prooftree-remaining-frame-width ()
  (let* ((frame-pixel-width (frame-pixel-width))
	 (full-pixel-width
	  (if (fboundp 'display-pixel-width) ; not xemacs
	      (display-pixel-width)
	    (x-display-pixel-width)))
	 (pixel-width-of-new-frame
	  (and full-pixel-width
	       (- full-pixel-width
		  (+ (frame-parameter nil 'left) frame-pixel-width)))))
    (and full-pixel-width
	 (/ (* (frame-width) pixel-width-of-new-frame)
	    frame-pixel-width))))

(defun new-prooftree-frame (&optional doit)
  (interactive "P")
  (cond
   ((and (not doit)
	 (my-select-frame-by-name "prooftree-frame"))
    (beep)
    (message "There is already a frame named prooftree-frame.
Give an argument if you want to create a new frame nonetheless.")
    nil)
   (t
    (let ((new-width (prooftree-remaining-frame-width))
	  (min-width 40)
	  (focus-follows-mouse nil)
	  (old-frame (window-frame (get-buffer-window (current-buffer)))))
      (cond
       ((null new-width)
	(error "Unable to compute available width for new frame."))
       ((or doit (<= min-width new-width)) ; else don't bother
	(let ((new-frame
	       (new-frame (list (cons 'name "prooftree-frame")
				(cons 'width
				      (max min-width new-width))
				(cons 'height (frame-height))
				(cons 'top (frame-parameter nil 'top))
				(cons 'left (+ (frame-parameter nil 'left)
					       (frame-pixel-width)
					       (or (get 'border-width
							'x-frame-parameter)
						   ;; nil in xemacs
						   5)))))))

; We have seen an "X protocol error" that crashes Emacs while running VNC on a
; Mac.  The following ad hoc 20-millisecond sleep seems to solve the problem,
; but we welcome suggestions from Emacs gurus for a better approach.

          (sleep-for 0 20)
	  (select-frame-set-input-focus new-frame)
	  (switch-to-buffer "prooftree")
	  (message "Columns in new frame: %d" (frame-width new-frame))
	  new-frame))
       (t
	(error "Not enough columns available (have %d, need %d); can solve with prefix arg"
	       new-width
	       min-width)))))))

(defun visit-proof-tree-other-frame (&optional doit)
  "Switch to prooftree buffer in \"prooftree-frame\" frame (which is created if
necessary).  Use meta-x select-other-frame-with-focus to switch back to
original frame."
  (interactive "P")
  (let ((old-frame (my-select-frame-by-name "prooftree-frame")))
    (cond
     (old-frame
      (let ((focus-follows-mouse nil))
	(select-frame-set-input-focus old-frame))
      (switch-to-buffer "prooftree"))
     (t (let ((frame (new-prooftree-frame doit)))
	  (select-frame-set-input-focus frame))))))

(provide 'mfm-acl2)
