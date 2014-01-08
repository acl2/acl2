; ACL2 Version 6.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTES-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of Version 2 of the GNU General Public License as
; published by the Free Software Foundation.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Sciences
; University of Texas at Austin
; Austin, TX 78712-1188 U.S.A.

; This file contains code for browsing ACL2 community book
; system/doc/acl2-doc.lisp, which contains the ACL2 system
; documentation.

; The first two forms are copied from emacs-acl2.el.  Keep them in
; sync with the definitions there.

(defvar *acl2-sources-dir*)

; Attempt to set *acl2-sources-dir*.
; WARNING: If you change this form, then also change the same form in
; emacs-acl2.el.
(if (and (not (boundp '*acl2-sources-dir*))
         (file-name-absolute-p load-file-name))
    (let ((pattern (if (string-match "[\\]" load-file-name)
                       "\[^\\]+\\*$"
                     "/[^/]+/*$"))
          (dir (file-name-directory load-file-name)))
      (let ((posn (string-match pattern dir)))
        (if posn
            (setq *acl2-sources-dir*
                  (substring dir 0 (1+ posn)))))))

(defmacro defv (var form)
  `(progn (defvar ,var)
	  (setq ,var ,form)))

(defmacro acl2-doc-init-vars ()
  '(progn
     (defv *acl2-doc-buffer-name*
       "acl2-doc")
     (defv *acl2-doc-index-buffer-name*
       "acl2-doc-index")
     (defv *acl2-doc-index-name* nil)
     (defv *acl2-doc-index-name-found-p* nil)
     (defv *acl2-doc-search-buffer-name*
       "acl2-doc-search")
     (defv *acl2-doc-search-string* nil)
     (defv *acl2-doc-search-regexp-p* nil)
     (defv *acl2-doc-search-separator* "###---###---###---###---###")
     (defv *acl2-doc-history* nil)
     (defv *acl2-doc-history-buffer-name*
       "acl2-doc-history")
     (defv *acl2-doc-return* nil)
     (defv *acl2-doc-all-topics-rev* nil)
     (defv *acl2-doc-state* nil)))

(acl2-doc-init-vars)

; We define the following variable outside acl2-doc-init-vars, so that it is
; not smashed by invoking that macro after running acl2-doc-alist-create.
(defvar *acl2-doc-directory* nil)

; The following variables can be set before loading this file, for
; example in a user's .emacs file.
(defvar *acl2-doc-rendered-combined-pathname*
  (concat *acl2-sources-dir*
	  "books/system/doc/rendered-doc-combined.lsp"))
(defvar *acl2-doc-rendered-combined-pathname-gzipped*
  (concat *acl2-doc-rendered-combined-pathname* ".gz"))
(defvar *acl2-doc-rendered-pathname*
  (concat *acl2-sources-dir*
	  "doc.lisp"))
(defvar *acl2-doc-rendered-combined-url*
  "http://www.cs.utexas.edu/users/moore/acl2/manuals/current/rendered-doc-combined.lsp.gz")
; Set the following to 'ACL2 to get to the ACL2 User's Manual at
; startup, but to 'TOP to get to the acl2+books combined manual.  Here
; we set it to nil, which goes to the acl2+books combined manual if it
; exists, and otherwise offers a choice.
(defvar *acl2-doc-top-default* nil)

(defun acl2-doc-fix-alist (alist)

;;; We delete topics whose names start with a vertical bar.  Most of
;;; these are for the tours anyhow.  We also lose release notes topics
;;; for ACL2(r) from July 2011 and before, but that seems minor
;;; compared to the pain of dealing with these topics, since Emacs
;;; Lisp doesn't seem to use |..| for escaping.

  (let ((ans nil))
    (while alist
      (let* ((entry (pop alist))
             (sym (car entry)))
        (if (and (symbolp sym)          ; always true?
                 (not (equal (aref (symbol-name sym) 0) ?|)))
            (push entry ans))))
    (reverse ans)))

(defun acl2-doc-alist-create (rendered-pathname)
  (when (not (file-exists-p rendered-pathname))
    (error "File %s is missing!" rendered-pathname))
  (let* ((large-file-warning-threshold

; As of November 2013, file books/system/doc/rendered-doc-combined.lsp is
; nearly 15M.  We take a guess here that modern platforms can handle plenty
; more than that, so we rather arbitrarily bump the threshold for a warning up
; to approximately twice the current size.

	  (max large-file-warning-threshold 30000000))
	 (buf0 (find-buffer-visiting rendered-pathname))

; We could let buf = buf0 if buf0 is non-nil.  But if the file was changed
; after loading it into buf0, then we would be operating on a stale buffer.  So
; we ignore buf0 other than to decide whether to delete the buffer just before
; returning from this function.

	 (buf (find-file-noselect rendered-pathname)))
    (with-current-buffer
        buf

; Warren Hunt asked that the acl2-doc buffer be put in the same directory as
; the file from which it was derived.  One basic advantage of this idea is that
; the directory won't depend on where acl2-doc was invoked.

      (setq *acl2-doc-directory* default-directory)
      (save-excursion
        (lisp-mode)
        (goto-char (point-min))
        (forward-sexp 1)
        (forward-line 3)
        (prog1 (acl2-doc-fix-alist (read buf))
	  (when (not buf0)
	    (kill-buffer buf))
          (message "Refreshed from %s" rendered-pathname))))))

(defun acl2-doc-state-initialized-p ()
  (not (null *acl2-doc-state*)))

(defun acl2-doc-rendered-combined-download ()
  "Download the acl2+books combined manual from the web;
then restart the ACL2-Doc browser to view that manual."
  (interactive)
  (cond ((file-exists-p *acl2-doc-rendered-combined-pathname*)
	 (message "Renaming %s to %s.backup"
		  *acl2-doc-rendered-combined-pathname*
		  *acl2-doc-rendered-combined-pathname*)
	 (rename-file *acl2-doc-rendered-combined-pathname*
		      (concat *acl2-doc-rendered-combined-pathname* ".backup")
		      0)))
  (message "Preparing to download %s"
	   *acl2-doc-rendered-combined-url*)
  (url-copy-file
   *acl2-doc-rendered-combined-url*
   *acl2-doc-rendered-combined-pathname-gzipped*)
  (cond ((file-exists-p *acl2-doc-rendered-combined-pathname-gzipped*)
	 (shell-command-to-string
	  (format "gunzip %s"
		  *acl2-doc-rendered-combined-pathname-gzipped*))
	 (or (file-exists-p *acl2-doc-rendered-combined-pathname*)
	     (error "Gunzip failed."))

;;; The following call of acl2-doc-reset may appear to have the
;;; potential to cause a loop: acl2-doc-reset calls
;;; acl2-doc-state-create, which calls
;;; acl2-doc-rendered-combined-fetch, which calls the present
;;; function.  However, acl2-doc-rendered-combined-fetch is
;;; essentially a no-op in this case because of the file-exists-p
;;; check just above.

	 (acl2-doc-reset 'TOP)
	 (acl2-doc-top))
	(t (message "Download/install failed.")
	   nil)))

(defun acl2-doc-rendered-combined-fetch ()
  (or (file-exists-p *acl2-doc-rendered-combined-pathname*)
      (cond
       ((and (file-exists-p *acl2-doc-rendered-combined-pathname-gzipped*)
	     (y-or-n-p
	      (format "Run gunzip on %s? "
		      *acl2-doc-rendered-combined-pathname-gzipped*
		      *acl2-doc-rendered-combined-pathname*)))
	(shell-command-to-string
	 (format "gunzip %s"
		 *acl2-doc-rendered-combined-pathname-gzipped*))
	(or (file-exists-p *acl2-doc-rendered-combined-pathname*)
	    (error "Execution of gunzip seems to have failed!")))
       ((y-or-n-p
	 (format "Download %s and install as %s? "
		 *acl2-doc-rendered-combined-url*
		 *acl2-doc-rendered-combined-pathname*))
	(acl2-doc-rendered-combined-download)))))

(defun acl2-doc-state-create (top-name)

;;; The given top-name is 'ACL2, 'TOP, or nil.  If nil, then we use
;;; the current top-name if one exists; otherwise we use
;;; *acl2-doc-top-default* if specified; otherwise we query.

  (cond
   ((eq top-name 'ACL2)
    (list top-name
	  (acl2-doc-alist-create *acl2-doc-rendered-pathname*)))
   ((and (eq top-name 'TOP)
	 (acl2-doc-rendered-combined-fetch))
    (list top-name
	  (acl2-doc-alist-create *acl2-doc-rendered-combined-pathname*)))
   ((eq top-name 'TOP)
    (error "Combined acl2+books manual not loaded for browsing"))
   ((acl2-doc-rendered-combined-fetch)	; top-name is nil
    (list 'TOP
	  (acl2-doc-alist-create *acl2-doc-rendered-combined-pathname*)))
   ((y-or-n-p
     " Do you want to browse the ACL2 User's Manual even though it
 does not include documentation for the ACL2 community books?
 Note: If your answer is \"y\", then avoid this query by placing the form
 (setq *acl2-doc-top-default* 'ACL2) in your .emacs file. ")
    (list 'ACL2
	  (acl2-doc-alist-create *acl2-doc-rendered-pathname*)))
   (t
    (error "No manual loaded for browsing"))))

(defun acl2-doc-reset (top-name)

;;; The given top-name is 'ACL2, 'TOP, or nil.  See acl2-doc-state-create.

  (let* ((top-name (or top-name
		      (cond
		       ((acl2-doc-state-initialized-p)

;;; The following expression is (acl2-doc-state-top-name), except that we
;;; haven't yet defined that function because we haven't yet defined the
;;; function acl2-doc-maybe-reset.

			(nth 0 *acl2-doc-state*))
		       (*acl2-doc-top-default*))))
	 (new-state (acl2-doc-state-create top-name)))
    (when (get-buffer *acl2-doc-index-buffer-name*)
      (kill-buffer *acl2-doc-index-buffer-name*))
    (when (get-buffer *acl2-doc-search-buffer-name*)
      (kill-buffer *acl2-doc-search-buffer-name*))
    (acl2-doc-init-vars)
    (setq *acl2-doc-state* new-state)
    t))

(defun acl2-doc-maybe-reset ()
  (cond ((not (acl2-doc-state-initialized-p))
	 (acl2-doc-reset nil)
	 t)
	(t nil)))

(defun acl2-doc-state-top-name ()
  (acl2-doc-maybe-reset)
  (nth 0 *acl2-doc-state*))

(defun acl2-doc-state-alist ()
  (acl2-doc-maybe-reset)
  (nth 1 *acl2-doc-state*))

(define-derived-mode acl2-doc-mode
  fundamental-mode
  "ACL2-Doc"
  "Major mode for acl2-doc buffer."

; By using lisp-mode-syntax-tablee, we arrange that the use of colon
; (:) doesn't break up an s-expression.  So for example,
; ACL2-PC::REWRITE is a single s-expression.  This matters because we
; define the function acl2-doc-topic-at-point in terms of
; backward-sexp.  Of course, we could instead evaluate the form
; (modify-syntax-entry ?: "w" acl2-doc-mode-syntax-table) but we start
; this way, in case other characters are missing and also because this
; approach might conceivably be useful for people who are navigating
; lisp forms in the acl2-doc buffer.

  :syntax-table lisp-mode-syntax-table)

; Arrange that files ending in .acl2-doc come up in acl2-doc mode.
; See also the emacs documentation for auto-mode-alist.
(if (not (assoc "\\.acl2-doc\\'" auto-mode-alist))
    (push '("\\.acl2-doc\\'" . acl2-doc-mode) auto-mode-alist))

(defun switch-to-acl2-doc-buffer ()
  (switch-to-buffer *acl2-doc-buffer-name*)

;;; The next two forms need only be evaluated when the buffer is first
;;; created, but it is likely harmless to go ahead and evaluate them
;;; every time.

  (acl2-doc-mode)
  (setq default-directory *acl2-doc-directory*)
  t)

(defun acl2-doc-print-topic (tuple)

; Warning: Do not set the buffer to read-only here, because this
; function may be called repeatedly for the same buffer, e.g., by
; function acl2-doc-search-buffer.

  (insert (format "Topic: %s\nParent list: %s\n%s\n%s\n"
                  (nth 0 tuple)
                  (nth 1 tuple)
                  (if (equal (length tuple) 4)
		      (if (eq (nth 0 tuple) 'TOP)
			  ""
			(format "Source: %s\n" (nth 3 tuple)))
		    (if (eq (acl2-doc-state-top-name) 'ACL2)
			""
		      "Source: ACL2 Sources\n"))
		  (nth 2 tuple)))
  (set-buffer-modified-p nil)
  (force-mode-line-update))

(defun acl2-doc-display-basic (entry)

;;; Entry is a history entry, hence of the form (point name parents
;;; string).

;;; The first form below is unnecessary if the caller is
;;; acl2-doc-display, but it's cheap.

  (switch-to-acl2-doc-buffer)
  (setq buffer-read-only nil)
  (erase-buffer)
  (acl2-doc-print-topic (cdr entry))	; entry is (cons position tuple)
  (setq buffer-read-only t)
  (goto-char (nth 0 entry))
  (let ((name (car (cdr entry)))
	(manual-name (if (eq (acl2-doc-state-top-name) 'ACL2)
			 "ACL2 User's"
		       "acl2+books combined")))
    (push name *acl2-doc-all-topics-rev*)
    (if (eq (acl2-doc-state-top-name) name)
	(message "At the top node of the %s manual"
		 manual-name)
      (message "Topic: %s (%s manual)" name manual-name))))

(defun acl2-doc-display (name)

;;; Name should be a symbol.  We display the topic and adjust the
;;; history and return history.  Do not use this for the "l" or "r"
;;; commands; use acl2-doc-display-basic instead, which does not mess
;;; with those history variables.

  (let ((tuple (assoc name (acl2-doc-state-alist))))
    (cond (tuple (switch-to-acl2-doc-buffer)
                 (let ((new-entry (cons 0 tuple)))
                   (if *acl2-doc-history*
                       (let ((old-entry (pop *acl2-doc-history*)))
                         (push (cons (point) (cdr old-entry))
                               *acl2-doc-history*)))
                   (push new-entry *acl2-doc-history*)
		   (setq *acl2-doc-return* nil)
                   (acl2-doc-display-basic new-entry)))
          (t (error "Not found: %s" name)))))

(defun acl2-doc-topic-at-point ()

;;; This function returns nil if the s-expression at point isn't a
;;; symbol.  Otherwise, it returns that symbol in upper case, except
;;; that it removes the leading and trailing bracket for [...].

  (let ((sym (sexp-at-point))
	(go t)
	(arrayp nil))
    (while go
      (cond ((and (consp sym)
		  (equal (length sym) 2)
		  (member (car sym)
			  '(\` quote)))
	     (setq sym (car (cdr sym))))
	    (t (setq go nil))))

;;; Deal with array case.

    (cond
     ((null sym)

;;; We have found that (sexp-at-point) returns nil when standing in
;;; text that ends in a square bracket followed by a period, e.g.,
;;; "[loop-stopper]."  So we try again.

      (setq sym
	    (save-excursion
	      (if (< (point) (point-max))
		  (forward-char 1))	; in case we are at "["
	      (let* ((saved-point (point))
		     (start (and (re-search-backward "[^]]*[[]" nil t)
				 (match-beginning 0))))
		(and start
		     (let ((end (and (re-search-forward "[^ ]*]" nil t)
				     (match-end 0))))
		       (and end
			    (<= saved-point end)
			    (goto-char (1+ start))
			    (read (current-buffer))))))))
      (when sym
	(setq arrayp t)))
     ((arrayp sym) ;; [...]
      (setq sym (and (not (equal sym []))
		     (aref sym 0)))
      (when sym
	(setq arrayp t))))

;;; Now we have sym and arrayp.

    (cond (arrayp ;; [...]
	   (let ((tmp (and (symbolp sym)
			   (intern (upcase (symbol-name sym))))))
	     (cond ((assoc tmp (acl2-doc-state-alist))
		    tmp)
		   (t 'BROKEN-LINK))))
	  ((not (and sym (symbolp sym)))
	   nil)
	  (t
	   (let* ((name (symbol-name sym))
		  (max-orig (1- (length name)))
		  (max max-orig)
		  (name (cond ((equal (aref name 0) ?:)
			       (setq max (1- max))
			       (substring name 1))
			      (t name)))
		  (go t))
	     (while (and go (< 1 max))
	       (cond ((member (aref name max)
			      '(?. ?\' ?:))
		      (setq max (1- max)))
		     (t (setq go nil))))
	     (intern (upcase (cond ((equal max max-orig)
				    name)
				   (t (substring name 0 (1+ max)))))))))))

(defun acl2-doc-completing-read (prompt silent-error-p)
  (let* ((completion-ignore-case t)
         (default (acl2-doc-topic-at-point))
         (default (and (or (eq default 'BROKEN-LINK) ; optimization
			   (assoc default (acl2-doc-state-alist)))
                       default))
         (value-read (completing-read
                      (if default
                          (format "%s (default %s): " prompt default)
                        (format "%s: " prompt))
                      (acl2-doc-state-alist)
                      nil nil nil nil
                      default)))
    (list (cond ((equal value-read default) ;; i.e., (symbolp value-read)
                 default)
                ((and (not silent-error-p)
                      (equal value-read ""))
                 (error "No default topic name found at point"))
                (t (intern (upcase value-read)))))))

(defun acl2-doc-go (name)

  "Go to the specified topic; performs completion."

  (interactive (acl2-doc-completing-read "Go to topic" nil))
  (acl2-doc-display name))

(defun acl2-doc-go! ()

  "Go to the topic occurring at the cursor position."

  (interactive)
  (let ((name (acl2-doc-topic-at-point)))
    (cond (name (acl2-doc-display name))
	  (t (error "Cursor is not on a name")))))

(defun acl2-doc-top ()
  "Go to the top topic."
  (interactive)
  (acl2-doc-go (acl2-doc-state-top-name))
  (let ((manual-name (if (eq (acl2-doc-state-top-name) 'ACL2)
			 "ACL2 User's"
		       "acl2+books combined")))
    (message "At the top node of the %s manual; type h for help"
	     manual-name)))

(defun acl2-doc (&optional clear)

  "Go to the ACL2-Doc browser; prefix argument clears state.
See the documentation topic for ACL2-Doc for more
information, either by starting ACL2-Doc and typing `h'
\(help), by viewing the ACL2-DOC topic in a web browser, or by
typing `:doc acl2-doc' in the ACL2 read-eval-print loop.

\\{acl2-doc-mode-map}"

  (interactive "P")
  (cond (clear
	 (acl2-doc-reset nil)
	 (acl2-doc-top))
        (*acl2-doc-history*
         (acl2-doc-display-basic (car *acl2-doc-history*)))
        (t
	 (acl2-doc-maybe-reset)
         (acl2-doc-top))))

(defun acl2-doc-last ()
  "Go to the last topic visited."
  (interactive)
  (cond ((cdr *acl2-doc-history*)
         (push (pop *acl2-doc-history*)
	       *acl2-doc-return*)
         (acl2-doc-display-basic (car *acl2-doc-history*)))
        (t (error "No last page visited"))))

(defun acl2-doc-return ()
  "Return to the last topic visited, popping the stack of
visited topics."
  (interactive)
  (cond (*acl2-doc-return*
	 (let ((entry (pop *acl2-doc-return*)))
	   (push entry *acl2-doc-history*)
	   (acl2-doc-display-basic entry)))
        (t (error "Nothing to return to"))))

(defun acl2-doc-read-line ()

; Return the current line, and go to the end of it.

  (forward-line 0)
  (let ((beg (point)))
    (end-of-line)
    (buffer-substring beg (point))))

(defun acl2-doc-up ()

  "Go to the parent of the current topic."

  (interactive)
  (switch-to-acl2-doc-buffer)
  (let ((first-parent
         (save-excursion
           (goto-char (point-min))
           (and (search-forward "Parent list: (" nil t)
		(acl2-doc-topic-at-point)))))
    (cond ((and (eq first-parent 'TOP)
		(eq (nth 0 *acl2-doc-state*) 'ACL2)
		(save-excursion
		  (goto-char (point-min))
		  (and (search-forward "Parent list: (TOP " nil t)
		       (setq first-parent (acl2-doc-topic-at-point)))))
	   (acl2-doc-display first-parent))
	  ((null first-parent)
	   (cond ((save-excursion
		    (goto-char (point-min))
		    (forward-line 1)
		    (member (acl2-doc-read-line)
			    '("Parent list: NIL"
			      "Parent list: ()")))
		  (error "Already at the root node of the manual"))
		 (t (error "Internal ACL2-Doc error in acl2-doc-up.
Please report this error to the ACL2 implementors."))))
	  (t (acl2-doc-display first-parent)))))

(defun acl2-doc-update-top-history-entry ()
  (cond ((null *acl2-doc-history*)
	 (error "Empty history!"))
	(t (with-current-buffer
	       *acl2-doc-buffer-name* ; error if this was killed!
	     (setq *acl2-doc-history*
		   (cons (cons (point) (cdr (car *acl2-doc-history*)))
			 (cdr *acl2-doc-history*)))))))

(defun acl2-doc-quit ()

  "Quit the ACL2-Doc browser."

  (interactive)
  (if (not (equal (buffer-name) *acl2-doc-buffer-name*))
      (error
       "Return to %s buffer (e.g., using C-t g) before running acl2-doc-quit"
       *acl2-doc-buffer-name*))
  (acl2-doc-update-top-history-entry)
  (quit-window))

(defun acl2-doc-initialize (&optional toggle)

  "Restart the ACL2-Doc browser, clearing its state.  With
prefix argument, toggle between the ACL2 User's Manual (the
default) and the acl2+books combined manual.  For the
latter, it will be necessary first to create file
books/system/doc/rendered-doc-combined.lsp; see :DOC
acl2-doc."

  (interactive "P")
  (acl2-doc-reset
   (and toggle
	(acl2-doc-state-initialized-p)
	(if (eq (acl2-doc-state-top-name) 'ACL2) 'TOP 'ACL2)))
  (acl2-doc-top))

(defun acl2-doc-index-buffer ()
  (or (get-buffer *acl2-doc-index-buffer-name*)
      (let ((buf (get-buffer-create *acl2-doc-index-buffer-name*))
            (alist (acl2-doc-state-alist)))
	(with-current-buffer
	    buf
	  (when *acl2-doc-directory* ; probabl always true
	    (setq default-directory *acl2-doc-directory*))
          (while alist
            (insert (format "%s\n" (car (pop alist)))))
	  (acl2-doc-mode)
	  (set-buffer-modified-p nil)
	  (setq buffer-read-only t))
	buf)))

(defun acl2-doc-index (name)

  "Go to the specified topic or else one containing it as a
substring; performs completion.  If the empty string is
supplied, then go to the index buffer.  Note that the index
buffer is in ACL2-Doc mode; thus, in particular, you can
type <RETURN> while standing on a topic in order to go
directly to that topic."

  (interactive (acl2-doc-completing-read
                "Find topic (then use \",\" for more) "
                t))
  (let ((buf (acl2-doc-index-buffer)))
    (cond
     ((equal (symbol-name name) "")
      (switch-to-buffer *acl2-doc-index-buffer-name*)
      (goto-char (point-min)))
     (t
      (let ((found-p (assoc name (acl2-doc-state-alist))))
	(setq *acl2-doc-index-name-found-p* (consp found-p))
	(setq *acl2-doc-index-name* (symbol-name name))
	(cond
	 (found-p (with-current-buffer
		      buf
		    (goto-char (point-min)))
		  (acl2-doc-display name))
	 (t (let ((topic
		   (with-current-buffer
		       buf
		     (goto-char (point-min))
		     (cond ((search-forward (symbol-name name) nil t)
			    (intern (acl2-doc-read-line)))
			   (t (setq *acl2-doc-index-name* nil)
			      (error "No matching topic found"))))))
	      (acl2-doc-display topic)))))))))

(defun acl2-doc-index-next ()

  "Find the next topic containing, as a substring, the topic
from the previous `i' command."

  (interactive)
  (let ((buf (get-buffer *acl2-doc-index-buffer-name*)))
    (when (null buf)
      (error "Need to initiate index search"))
    (let ((topic (with-current-buffer
		     buf
		   (and (search-forward *acl2-doc-index-name* nil t)
			(acl2-doc-read-line)))))
      (cond (topic
	     (cond ((and *acl2-doc-index-name-found-p*
			 (equal topic *acl2-doc-index-name*))
		    (setq *acl2-doc-index-name-found-p* nil)
		    (acl2-doc-index-next))
		   (t (acl2-doc-display (intern topic)))))
	    (t (with-current-buffer
		   buf
		 (goto-char (point-min)))
	       (error
		"No more matches; try again to start from the beginning"))))))

(defun acl2-doc-search-buffer ()
;;; Return the search buffer, which contains all :doc topics, creating it first
;;; (with those topics inserted) if necessary.
  (or (get-buffer *acl2-doc-search-buffer-name*)
      (let ((buf (get-buffer-create *acl2-doc-search-buffer-name*))
            (alist (acl2-doc-state-alist)))
	(with-current-buffer
	    buf
          (while alist
	    (insert "\n")
	    (insert *acl2-doc-search-separator*)
	    (insert "\n")
	    (acl2-doc-print-topic (pop alist)))
	  (setq buffer-read-only t))
	buf)))

(defun acl2-doc-search-aux (str regexp-p)
  (when (equal str "")
    (error "Input a search string, or type \"n\" to continue previous search"))
  (let* ((buf (acl2-doc-search-buffer))
	 (continue-p (equal regexp-p :continue))
	 (str (cond
	       ((not continue-p) str)
	       (t (or *acl2-doc-search-string*
		      (error "There is no previous search to continue")))))
	 (regexp-p (if continue-p
		       *acl2-doc-search-regexp-p*
		     regexp-p))
	 (pair
	  (with-current-buffer
	      buf
	    (when (not continue-p)
	      (goto-char (point-min)))
	    (cond
	     ((if regexp-p
		  (re-search-forward str nil t)
		(search-forward str nil t))
	      (save-excursion
		(let ((point-found (match-end 0)))
		  (search-backward *acl2-doc-search-separator*)
		  (forward-line 1)
		  (let ((point-start (point)))
		    (cons (1+ (- point-found point-start)) ; (point-min) = 1
			  (let ((beg (+ point-start 7)))   ;"Topic: "
			    (end-of-line)
			    (buffer-substring beg (point))))))))
	     (t nil)))))
    (cond (pair
	   ;; The first two assignments are redundant if continue-p is true.
	   (setq *acl2-doc-search-string* str)
	   (setq *acl2-doc-search-regexp-p* regexp-p)
	   (acl2-doc-display (intern (cdr pair)))
	   (goto-char (car pair))
	   (acl2-doc-update-top-history-entry))
	  (continue-p (with-current-buffer
			  buf
			(goto-char (point-min)))
		      (error "Try again for wrapped search"))
	  (t (error "Not found: %s" str)))))

(defun acl2-doc-search (str)

  "Search forward from the top of the manual for the input
string.  If the search succeeds, then go to that topic with
the cursor put immediately after the found text, with the
topic name displayed in the minibuffer."

  (interactive "sSearch: ")
  (acl2-doc-search-aux str nil))

(defun acl2-doc-re-search (str)

  "Perform a regular expression search, forward from the top
of the manual, for the input string.  If the search
succeeds, then go to that topic with the cursor put
immediately after the found text, with the topic name
displayed in the minibuffer."

  (interactive "sRegular Expression Search: ")
  (acl2-doc-search-aux str t))

(defun acl2-doc-search-next ()

  "Find the next occurrence for the most recent search or regular
expression search."

  (interactive)
  (acl2-doc-search-aux nil :continue))

(defun acl2-doc-tab ()

  "Visit the next link after the cursor on the current page,
searching from the top if no link is below the cursor."

  (interactive)
  (switch-to-acl2-doc-buffer)
  (cond ((or (re-search-forward "[[][^ ]+]" nil t)
	     (progn (goto-char (point-min))
		    (re-search-forward "[[][^ ]+]" nil t)))
	 (search-backward "[")
	 (forward-char 1))
	(t (error "There are no links on this page."))))

(defun strip-cadrs (x)
  (let ((ans nil))
    (while x
      (push (cadr (car x)) ans)
      (setq x (cdr x)))
    (reverse ans)))

(defun acl2-doc-history-buffer ()
;;; Return the history buffer, creating it first if necessary.
  (or (get-buffer *acl2-doc-history-buffer-name*)
      (let ((buf (get-buffer-create *acl2-doc-history-buffer-name*))
            (alist (acl2-doc-state-alist)))
	(with-current-buffer
	    buf
          (while alist
	    (insert "\n")
	    (insert *acl2-doc-search-separator*)
	    (insert "\n")
	    (acl2-doc-print-topic (pop alist)))
	  (setq buffer-read-only t))
	buf)))

(defun acl2-doc-history ()

  "Visit a buffer that displays the names of all visited
topics in order, newest at the bottom.  That buffer is in
acl2-doc mode; thus the usual acl2-doc commands may be used.
In particular, you can visit a displayed topic name by
putting your cursor on it and typing <RETURN>."

  (interactive)
  (let* ((buf0 (get-buffer *acl2-doc-history-buffer-name*))
	 (buf (or buf0
		  (get-buffer-create *acl2-doc-history-buffer-name*)))
	 (all (reverse *acl2-doc-all-topics-rev*)))
    (switch-to-buffer *acl2-doc-history-buffer-name*)
    (acl2-doc-mode)
    (cond (buf0
	   (setq buffer-read-only nil)
	   (delete-region (point-min) (point-max))))
    (insert "List of all visited topics in order, newest at the bottom:\n")
    (insert "=========================================================\n")
    (while all
      (insert (format "%s" (pop all)))
      (insert "\n"))

;;; We could bind x to *acl2-doc-history* and execute the commented-out form just
;;; below, after printing a separator such as the one above.  If someone asks for
;;; this, we should think about printing the topics in *acl2-doc-return* as well,
;;; and maybe even display a single list if we can figure out a reasonable way to
;;; do so while indicating "last" and "return" information.

;;; (while x
;;;   (insert (format "%s" (cadr (pop x))))
;;;    (insert "\n"))

    (setq buffer-read-only t)
    (set-buffer-modified-p nil)
    (goto-char (point-max))
    (recenter -1)
    (message "List of all visited topics in order, newest at the bottom")))

(defun acl2-doc-help ()

  "Go to the ACL2-DOC topic to read about how to use the
ACL2-Doc browser."

  (interactive)
  (acl2-doc-go 'ACL2-DOC))

(defun control-x-a-a-deprecated ()
  (interactive)
  (error "Use Control-t g to start the ACL2-Doc browser."))

(defun control-x-a-A-deprecated ()
  (interactive)
  (error
   "Use Control-t g to start the ACL2-Doc browser and then
I if you want to initialize."))

(defun control-t-G-deprecated ()
  (interactive)
  (error "Use Control-t . to go to a browser topic."))

(when (not (boundp 'ctl-t-keymap))

; Warning: Keep this in sync with the introduction of ctl-t-keymap in
; emacs-acl2.el.

; Note that ctl-t-keymap will already be defined if this file is loaded
; from emacs-acl2.el.  But if not, then we define it here.

; This trick probably came from Bob Boyer, to define a new keymap; so now
; control-t is the first character of a complex command.
  (defvar ctl-t-keymap)
  (setq ctl-t-keymap (make-sparse-keymap))
  (define-key (current-global-map) "\C-T" ctl-t-keymap)

; Control-t t now transposes characters, instead of the former control-t.
  (define-key ctl-t-keymap "\C-T" 'transpose-chars)
  (define-key ctl-t-keymap "\C-t" 'transpose-chars)
  )

(define-key global-map "\C-tg" 'acl2-doc)
; We originally bound \C-tG and \C-t\C-G to acl2-doc-go! and
; acl2-doc-go, respectively.  But it seems more intuitive just to use
; \C-t. (in analogy to meta-.).  We can probably eliminate the two
; deprecated keys, along with (of course) the definition of
; control-t-G-deprecated, after January 2014.
(define-key global-map "\C-t." 'acl2-doc-go)
(define-key global-map "\C-tG" 'control-t-G-deprecated)
(define-key global-map "\C-t\C-G" 'control-t-G-deprecated)

; An early version of ACL2-Doc (from late 2013) used \C-Xaa to get to
; the browser instead of \C-tg.  We bind that key (and a related one,
; \C-XaA), if not already bound, as a courtesy to early adopters of
; ACL2-Doc.  After the release of v6-4 we should probably eliminate
; these forms as well as the definitions of the two "-deprecated"
; functions.
(when (not (key-binding "\C-Xaa"))
  (define-key global-map "\C-Xaa" 'control-x-a-a-deprecated))
(when (not (key-binding "\C-XaA"))
  (define-key global-map "\C-XaA" 'control-x-a-A-deprecated))

(define-key acl2-doc-mode-map "g" 'acl2-doc-go)
(define-key acl2-doc-mode-map "\C-M" 'acl2-doc-go!)
(define-key acl2-doc-mode-map "i" 'acl2-doc-index)
(define-key acl2-doc-mode-map "," 'acl2-doc-index-next)
(define-key acl2-doc-mode-map "I" 'acl2-doc-initialize)
(define-key acl2-doc-mode-map "h" 'acl2-doc-help)
(define-key acl2-doc-mode-map "l" 'acl2-doc-last)
(define-key acl2-doc-mode-map "n" 'acl2-doc-search-next)
(define-key acl2-doc-mode-map "r" 'acl2-doc-return)
(define-key acl2-doc-mode-map "s" 'acl2-doc-search)
(define-key acl2-doc-mode-map "S" 'acl2-doc-re-search)
(define-key acl2-doc-mode-map "t" 'acl2-doc-top)
(define-key acl2-doc-mode-map "u" 'acl2-doc-up)
(define-key acl2-doc-mode-map "q" 'acl2-doc-quit)
(define-key acl2-doc-mode-map " " 'scroll-up)
(define-key acl2-doc-mode-map "D" 'acl2-doc-rendered-combined-download)
(define-key acl2-doc-mode-map "\t" 'acl2-doc-tab)
(define-key acl2-doc-mode-map "H" 'acl2-doc-history)
