; ACL2 Version 8.6 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2024, Regents of the University of Texas

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

; Enhancements for multiple windows (added August 2021) were
; initially contributed by Mayank Manjrekar.

; This file contains code for browsing ACL2 community book
; system/doc/acl2-doc.lisp, which contains the ACL2 system
; documentation.

; The first two forms are copied from emacs-acl2.el.  Keep them in
; sync with the definitions there.

(defvar *acl2-sources-dir*)

(defvar *acl2-doc-show-extra*
; WARNING: Don't use defv (below) for this.  We don't want to
; reinitialize it after downloading an updated manual.
  "\nNOTE: Type D to download the latest version.")

; Attempt to set *acl2-sources-dir*.
; WARNING: If you change this form, then also change the same form in
; emacs-acl2.el.
(if (and (not (boundp '*acl2-sources-dir*))
         (file-name-absolute-p load-file-name))
    (let ((pattern ; emacs/ and books/emacs/ differ here
           (if (string-match "[\\]" load-file-name)
               "\[^\\]+\\*$"
             "/[^/]+/*$"))
          (dir (file-name-directory load-file-name)))
      (let ((posn (string-match pattern dir)))
        (if posn
            (setq *acl2-sources-dir*
                  (substring dir 0 (1+ posn)))))))

(require 'etags) ; for "/" and "W" commands, e.g., tags-lazy-completion-table

; Essay on ACL2-doc Data Structures

; Here we briefly summarize some of the main data structures used
; below.

; *acl2-doc-state*: This variable, initialized in acl2-doc-reset, is a
; pair (top-topic-name tuple-list).  Top-topic-name is the name of
; the top topic of the manual.  Tuple-list is a list of tuples,
; created in acl2-doc-alist-create, read from the rendered.lsp file
; but slightly fixed up.  For example, if the manual is the acl2-only
; manual, then (car (car (cdr *acl2-doc-state*))) is:
;   (&ALLOW-OTHER-KEYS (POINTERS) "See [macro-args].")

; (acl2-doc-state-alist): Reset if necessary, then return
; (nth 1 *acl2-doc-state*), which is a list of tuples as described
; above.

; *acl2-doc-history*: a buffer-local list of pairs (cons point tuple),
; *where tuple is a member of (acl2-doc-state-alist) and point is the
; *position in the topic of that tuple.  This is updated in
; *acl2-doc-display.

; End of Essay on ACL2-doc Data Structures.

(defvar *acl2-doc-manual-alist* nil)
(defvar *acl2-doc-manual-name* ; key into *acl2-doc-manual-alist*
  'combined)
(defvar *acl2-doc-manual-name-previous* nil)
(defvar *acl2-doc-short-new-buffer-names* nil)

(defun acl2-doc-manual-alist-entry (pathname top printname url
                                             main-tags-file-name
                                             acl2-tags-file-name)
  (list pathname top printname url main-tags-file-name
        acl2-tags-file-name
        (concat (or (file-name-directory pathname) "") "acl2-doc-search")
        (concat (or (and url (file-name-directory url)) "") "acl2-doc-search.gz")))

(defun extend-acl2-doc-manual-alist (key pathname top
                                         &optional
                                         printname
                                         url
                                         main-tags-file-name
                                         acl2-tags-file-name)
  (when (and url
             (not (and (stringp url)
                       (let ((len (length url)))
                         (and (> len 3)
                              (equal (substring url (- len 3) len)
                                     ".gz"))))))
    (error "The URL specified for manual name %s does not end in \".gz\"."
           key))
  (let ((tuple (assoc key *acl2-doc-manual-alist*)))
    (cond
     (tuple
      (setcdr tuple ; avoid setf; see my-cl-position
              (acl2-doc-manual-alist-entry pathname top printname url
                                           main-tags-file-name
                                           acl2-tags-file-name))
      *acl2-doc-manual-alist*)
     (t (push (cons key (acl2-doc-manual-alist-entry pathname top printname url
                                                     main-tags-file-name
                                                     acl2-tags-file-name))
              *acl2-doc-manual-alist*)))))

(extend-acl2-doc-manual-alist
 'combined
 (concat *acl2-sources-dir*
         "books/system/doc/rendered-doc-combined.lsp")
 'TOP
 "ACL2+Books Manual"
 "https://www.cs.utexas.edu/users/moore/acl2/manuals/current/rendered-doc-combined.lsp.gz"
 (concat *acl2-sources-dir* "TAGS-acl2-doc")
 (concat *acl2-sources-dir* "TAGS"))

(extend-acl2-doc-manual-alist
 'acl2-only
 (concat *acl2-sources-dir* "doc.lisp")
 'TOP
 "ACL2 User's Manual"
 nil
 nil
 (concat *acl2-sources-dir* "TAGS"))

(defmacro defv (var form)
  `(progn (defvar ,var)
          (setq ,var ,form)))

(defmacro defv-local (var form)
  `(progn (defvar-local ,var ,form)
          (put ',var 'permanent-local t))) ; required for saving
                                           ; buffer-local values when
                                           ; major mode is changed

(defmacro acl2-doc-init-vars (first-time)
  `(progn
     (defv *acl2-doc-buffer-name* ; This is a constant.
       "acl2-doc")
     (defv *acl2-doc-index-buffer-name*
       "acl2-doc-index")
     (defv *acl2-doc-search-separator* "###---###---###---###---###")
     (defv *acl2-doc-search-buffer-name* "acl2-doc-search")
     (defv *acl2-doc-history-buffer-name* "acl2-doc-history")
     (defv *acl2-doc-all-topics-rev* nil)
     (defv *acl2-doc-state* nil)
     (defv *acl2-doc-children-ht* nil)
     (defv *acl2-doc-show-help-message* nil)
; Warning: Do not set *acl2-doc-show-extra* here (see comment in its
; introduction using defvar, above).
     (defv *acl2-doc-last-tags-file-name* nil)
     ,@(and first-time
            '((defv-local *acl2-doc-index-name* nil)
              (defv-local *acl2-doc-index-name-found-p* nil)
              (defv-local *acl2-doc-index-position* 1)
              (defv-local *acl2-doc-search-string* nil)
              (defv-local *acl2-doc-search-regexp-p* nil)
              (defv-local *acl2-doc-search-position* 1)
              (defv-local *acl2-doc-history* nil)
              (defv-local *acl2-doc-return* nil)
              (defv-local *acl2-doc-limit-topic* nil)
              (defv-local *acl2-doc-topics-ht* nil)))))

(acl2-doc-init-vars t)

; We define the following variable outside acl2-doc-init-vars, so that it is
; not smashed by invoking that macro after running acl2-doc-alist-create.
(defv *acl2-doc-directory* nil)

(defun my-cl-position (ch str)

;;; We include this simple variant of cl-position because it is not
;;; available in some versions of emacs (we have had a report of this
;;; problem for GNU Emacs 24.3.1 on redhat).  We could (require 'cl)
;;; or perhaps (require 'cl-lib), but some web pages suggest issues
;;; with using cl functions (as opposed to macros).  I don't want to
;;; think about any of that.

  (let ((continue t)
        (pos 0)
        (len (length str))
        (ans))
    (while (and continue (< pos len))
      (when (eql (aref str pos) ch)
        (setq ans pos)
        (setq continue nil))
      (setq pos (1+ pos)))
    ans))

(defun acl2-doc-fix-symbol (sym)

;;; Since Emacs Lisp doesn't seem to use |..| for escaping, we simply
;;; remove those vertical bars that seem to have been placed by Common
;;; Lisp.  NOTE: If this doesn't do the trick, consider modifying the
;;; definition of function rendered-name-acl2-doc in file
;;; books/system/doc/render-doc-base.lisp.

  (let* ((name (symbol-name sym))
         (pos (my-cl-position ?| name)))
    (cond ((null pos)                   ; common case
           sym)
          (t (let ((max (1- (length name))))
               (cond ((eql max -1)      ; impossible?
                      sym)
                     ((not (eql (aref name max) ?|))
                      sym)
                     ((eql pos 0)
                      (intern (substring name 1 max)))
                     ((and (> pos 1)
                           (eql (aref name (- pos 1)) ?:)
                           (eql (aref name (- pos 2)) ?:))
                      (intern (concat (substring name 0 pos)
                                      (substring name (1+ pos) max))))
                     (t sym)))))))

(defun acl2-doc-fix-entry (entry)
  (cons (acl2-doc-fix-symbol (car entry))
        (cons (let ((lst (cadr entry)))
                (if (eq lst 'NIL)
                    ()
                  (let (ans)
                    (while lst
                      (push (acl2-doc-fix-symbol (pop lst))
                            ans))
                    (nreverse ans))))
              (cddr entry))))

(defun acl2-doc-fix-alist (alist)

;;; We delete topics whose names start with a vertical bar.  Most of
;;; these are for the tours anyhow.  We also lose release notes topics
;;; for ACL2(r) from July 2011 and before, but that seems minor
;;; compared to the pain of dealing with these topics, since Emacs
;;; Lisp doesn't seem to use |..| for escaping.

  (let ((ans nil))
    (while alist
      (let ((entry (pop alist)))
        (push (acl2-doc-fix-entry entry) ans)))
    (reverse ans)))

(defun acl2-doc-large-file-warning-threshold ()

;;; As of April 2019, file books/system/doc/rendered-doc-combined.lsp is
;;; a bit over 100M bytes.  We take a guess here that modern platforms
;;; can handle somewhat more than this size, so we rather arbitrarily
;;; bump up the threshold for a warning, to provide a modest cushion for
;;; avoiding the warning.

  (max (or large-file-warning-threshold 0)
       120000000))

(defun acl2-doc-alist-create (rendered-pathname)
  (when (not (file-exists-p rendered-pathname))
    (error "File %s is missing!" rendered-pathname))
  (let* ((large-file-warning-threshold (acl2-doc-large-file-warning-threshold))
         (buf0 (find-buffer-visiting rendered-pathname))

; We could let buf = buf0 if buf0 is non-nil.  But if the file was changed
; after loading it into buf0, then we would be operating on a stale buffer.  So
; we ignore buf0 other than to decide whether to delete the buffer just before
; returning from this function.

         (buf (progn (when buf0 ; avoid undo warning
                       (kill-buffer buf0))
                     (message "Reading %s..."
                              rendered-pathname)
                     (find-file-noselect rendered-pathname))))
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

(defun acl2-doc-manual-entry (&optional manual-name)
  (let* ((manual-name (or manual-name *acl2-doc-manual-name*))
         (tuple (assoc manual-name *acl2-doc-manual-alist*)))
    (when (null tuple)
      (error "No manual exists in %s with name %s."
             '*acl2-doc-manual-alist*
             manual-name))
    (cdr tuple)))

(defun acl2-doc-manual-name ()
  *acl2-doc-manual-name*)

(defun acl2-doc-pathname (&optional must-exist)
  (let ((pathname (nth 0 (acl2-doc-manual-entry))))
    (cond
     ((null pathname)
      (error "No pathname was specified in %s for manual name %s."
             '*acl2-doc-manual-alist*
             *acl2-doc-manual-name*))
     ((and must-exist
           (not (file-exists-p pathname)))
      (error "The file %s (for manual name %s) does not exist."
             pathname
             (acl2-doc-manual-name)))
     (t pathname))))

(defun acl2-doc-top-name ()
  (nth 1 (acl2-doc-manual-entry)))

(defun acl2-doc-manual-printname ()
  (or (nth 2 (acl2-doc-manual-entry))
      (format "manual named `%s'"
              (acl2-doc-manual-name))))

(defun acl2-doc-url (&optional strict)
  (or (nth 3 (acl2-doc-manual-entry))
      (and strict
           (error "No URL was specified for manual name %s."
                  *acl2-doc-manual-name*))))

(defun acl2-doc-main-tags-file-name ()
  (nth 4 (acl2-doc-manual-entry)))

(defun acl2-doc-acl2-tags-file-name ()
  (nth 5 (acl2-doc-manual-entry)))

(defun acl2-doc-search-file-name ()
  (nth 6 (acl2-doc-manual-entry)))

(defun acl2-doc-search-url ()
  (nth 7 (acl2-doc-manual-entry)))

(defun acl2-doc-set-manual (manual-name)
; returns manual-name, except, error if manual-name names no manual
  (acl2-doc-manual-entry manual-name)
  (setq *acl2-doc-manual-name* manual-name))

(defun acl2-doc-state-initialized-p ()
  (not (null *acl2-doc-state*)))

(defun acl2-doc-gzipped-file (filename)
  (concat filename ".gz"))

(defun acl2-doc-download-aux-1 (file-url file-pathname)
  (let ((file-backup (concat file-pathname ".backup"))
        (file-gzipped (acl2-doc-gzipped-file file-pathname)))
    (cond ((file-exists-p file-pathname)
           (message "Renaming %s to %s"
                    file-pathname
                    file-backup)
           (rename-file file-pathname file-backup 0)))
    (message "Preparing to download URL\n%s\ninto file\n%s"
             file-url file-gzipped)
    (url-copy-file file-url file-gzipped)
    (cond ((file-exists-p file-gzipped)
           (cond
            ((eql 0 (nth 7
                         (file-attributes ; size
                          file-gzipped)))
             (delete-file file-gzipped)
             (error
              "Download/install failed (deleted zero-length file, %s)"
              file-gzipped))
            (t
             (shell-command-to-string
              (format "gunzip %s"
                      file-gzipped))
             (or (file-exists-p file-pathname)
                 (error "Gunzip failed")))))
          (t (error "Download/install failed")
             nil))))

(defvar acl2-doc-download-error "")

(defun acl2-doc-download-aux (url pathname)
  (condition-case err
      (acl2-doc-download-aux-1 url pathname)
    (error
     (progn
       (setq acl2-doc-download-error
             (format "You can copy URL %s
directly to file %s
and then apply gunzip to that file."
                     url
                     (acl2-doc-gzipped-file pathname)))
       (error "Download failed (message: %s).
The following message is saved in Emacs variable acl2-doc-download-error:
%s"
              (error-message-string err)
              acl2-doc-download-error)))))

(defun acl2-doc-download ()
  "Download the ``bleeding edge'' ACL2+Books Manual from the web;
then restart the ACL2-Doc browser to view that manual."
  (interactive)
  (acl2-doc-download-aux (acl2-doc-url t) (acl2-doc-pathname))

;;; The following call of acl2-doc-reset may appear to have the
;;; potential to cause a loop: acl2-doc-reset calls acl2-doc-fetch,
;;; which calls the present function.  However, acl2-doc-fetch is
;;; essentially a no-op in this case because of the file-exists-p
;;; check made in the first call above of acl2-doc-download-aux.

  (acl2-doc-reset (acl2-doc-manual-name))
  (acl2-doc-top)
  (acl2-doc-download-aux (acl2-doc-search-url) (acl2-doc-search-file-name)))

(defun manual-index-pathname ()
  (let* ((rendered (acl2-doc-pathname))
         (rendered-length (length rendered))
         (suffix "system/doc/rendered-doc-combined.lsp")
         (suffix-length (length suffix)))
;;; Sanity check (use (setq debug-on-error t) to see backtrace):
    (or (and (<= suffix-length rendered-length)
             (equal (substring rendered (- rendered-length suffix-length))
                    "system/doc/rendered-doc-combined.lsp"))
        (error "Implementation error in acl2-doc: unexpected suffix"))
    (concat
     (substring rendered 0 (- rendered-length suffix-length))
     "doc/manual/index.html")))

(defun acl2-doc-fetch ()
  (let* ((pathname (acl2-doc-pathname))
         (pathname-exists (file-exists-p pathname))
         (url (acl2-doc-url))
         (pathname-gz (and url (acl2-doc-gzipped-file pathname)))
         (manual-index-pathname (and url (manual-index-pathname))))
    (cond
     ((and pathname-exists
           (or (null url) ;; no download option
               (null manual-index-pathname) ; no writes dates to compare
               (file-newer-than-file-p pathname manual-index-pathname)
               (yes-or-no-p ; minibuffer display is better than y-or-n-p
                "Use outdated manual?  (Reply no for download option.) "))))
     ((and (and pathname-gz
                (file-exists-p pathname-gz))
           (y-or-n-p
            (format
             "Run gunzip on %s%s? "
             pathname-gz
             (if (and manual-index-pathname
                      (file-newer-than-file-p pathname
                                              manual-index-pathname))
                 ""
               ", even though you can download a newer version"))))
      (shell-command-to-string
       (format "gunzip %s"
               pathname-gz))
      (or (file-exists-p pathname)
          (error "Execution of gunzip seems to have failed!")))
     ((and url
           (y-or-n-p
            (format "Download %s and install as %s? "
                    url pathname)))
      (acl2-doc-download))
     ((or pathname-exists url)
      (error "Update of manual aborted"))
     (t (error
         "File %s not found, and\nno URL specified for the manual named %s"
         pathname *acl2-doc-manual-name*)))))

(defun acl2-doc-reset (manual-name)
  (let ((old-name (acl2-doc-manual-name)))
    (cond ((null manual-name)
           (setq manual-name old-name))
          ((not (eq old-name manual-name))
           (setq *acl2-doc-manual-name-previous* old-name)
           (acl2-doc-set-manual manual-name)))
    (acl2-doc-fetch)
    (let ((new-state (list (acl2-doc-top-name)
                           (acl2-doc-alist-create (acl2-doc-pathname t)))))
      (when (get-buffer *acl2-doc-index-buffer-name*)
        (kill-buffer *acl2-doc-index-buffer-name*))
      (when (get-buffer *acl2-doc-search-buffer-name*)
        (kill-buffer *acl2-doc-search-buffer-name*))
      (acl2-doc-kill-buffers t)
      (acl2-doc-init-vars nil)
      (setq *acl2-doc-state* new-state)
      t)))

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

; Based on http://ergoemacs.org/emacs/elisp_syntax_coloring.html:
(defvar acl2-doc-keywords
  '(("\\[\\([^ \t]*[^0-9 \t][^ \t]*\\)\\]"
     . 1)))

; Can be modified by user; set to the desired link color, or nil if none.
(defv *acl2-doc-link-color* "#0000FF") ; blue
(make-face 'acl2-doc-link-face)

(define-derived-mode acl2-doc-mode
  fundamental-mode
  "ACL2-Doc"
  "Major mode for acl2-doc buffer."

; By using lisp-mode-syntax-table, we arrange that the use of colon
; (:) doesn't break up an s-expression.  So for example,
; ACL2-PC::REWRITE is a single s-expression.  This matters because we
; define the function acl2-doc-topic-at-point in terms of
; backward-sexp.  Of course, we could instead evaluate the form
; (modify-syntax-entry ?: "w" acl2-doc-mode-syntax-table) but we start
; this way, in case other characters are missing and also because this
; approach might conceivably be useful for people who are navigating
; lisp forms in the acl2-doc buffer.

  :syntax-table (copy-syntax-table lisp-mode-syntax-table))

(add-hook 'acl2-doc-mode-hook
          (lambda ()
            (when *acl2-doc-link-color*
              (set-face-foreground 'acl2-doc-link-face *acl2-doc-link-color*)
              (setq font-lock-defaults '(acl2-doc-keywords t))
              (set (make-local-variable 'font-lock-keyword-face)
                   'acl2-doc-link-face))))

; Arrange that files ending in .acl2-doc come up in acl2-doc mode.
; See also the emacs documentation for auto-mode-alist.
(if (not (assoc "\\.acl2-doc\\'" auto-mode-alist))
    (push '("\\.acl2-doc\\'" . acl2-doc-mode) auto-mode-alist))

(defvar *acl2-doc-buffer-name-pattern* ; a constant
  (concat "^" *acl2-doc-buffer-name* "\\(<.+>\\|\\)$"))

(defun acl2-doc-buffer-p (buffer)
  (and (string-match-p *acl2-doc-buffer-name-pattern*
                       (buffer-name buffer))
       (with-current-buffer buffer
         (equal major-mode 'acl2-doc-mode))))

(defun current-acl2-buffer ()
  (let ((buf nil)
        (lst (buffer-list)))

;;; It is tempting to use (seq-find 'acl2-doc-buffer-p (buffer-list)), but
;;; seq-find is not defined in some older Emacs versions (e.g., 24.5.1).

    (while (and lst
                (null buf))
      (if (acl2-doc-buffer-p (car lst))
          (setq buf (car lst))
        (pop lst)))
    buf))

(defun switch-to-acl2-doc-buffer (&optional new-buffer-name)
  (if new-buffer-name
      (let ((buf (generate-new-buffer-name
                  (if *acl2-doc-short-new-buffer-names*
                      *acl2-doc-buffer-name*
                    (concat *acl2-doc-buffer-name*
                            "<"
                            (symbol-name new-buffer-name)
                            ">")))))
        (if pop-up-windows ; t by default; with nil, want single window
            (switch-to-buffer-other-window buf)
          (switch-to-buffer buf)))
    (let ((current-acl2-buffer (current-acl2-buffer)))
      (switch-to-buffer (if current-acl2-buffer
                            current-acl2-buffer
                          (generate-new-buffer-name *acl2-doc-buffer-name*)))))

;;; The next two forms need only be evaluated when the buffer is first
;;; created, but it is likely harmless to go ahead and evaluate them
;;; every time.

  (acl2-doc-mode)
  (when *acl2-doc-directory*
    (setq default-directory *acl2-doc-directory*))
  t)

(defun acl2-doc-kill-buffers (&optional do-not-ask)

  "Kill all background ACL2-Doc buffers.  If invoked in an
ACl2-Doc buffer, all ACl2-Doc buffers except the current one will
be killed.  If invoked in any other buffer, all ACL2-Doc buffers
will be killed.  With prefix argument, avoid a query that asks
for confirmation."

  (interactive)
  (when (or do-not-ask (y-or-n-p "Kill all other acl2-doc-buffers? "))

;;; It may be tempting to use seq-filter below, but that isn't defined
;;; in some older Emacs versions (e.g., 24.5.1).

    (let ((cur (current-buffer)))
      (dolist (buf (buffer-list))
        (when (and (acl2-doc-buffer-p buf)
                   (not (eq cur buf)))
          (kill-buffer buf))))))

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
                        (format ":DOC source: %s\n" (nth 3 tuple)))
                    (if (eq (acl2-doc-state-top-name) 'TOP)
                        ""
                      ":DOC source: ACL2 Sources\n"))
                  (nth 2 tuple)))
  (set-buffer-modified-p nil)
  (force-mode-line-update))

(defun acl2-doc-display-message (entry &optional extra)
  (let ((name (car (cdr entry)))
        (manual-name (acl2-doc-manual-printname))
        (help-msg (if *acl2-doc-show-help-message*
                      "; type h for help"
                    ""))
        (extra (or extra
                   *acl2-doc-show-extra*
                   "")))
    (setq *acl2-doc-show-help-message* nil)
    (setq *acl2-doc-show-extra* nil)
    (if (eq (acl2-doc-state-top-name) name)
        (message "At the top node of the %s%s%s"
                 manual-name help-msg extra)
      (message "Topic: %s (%s)%s%s" name manual-name help-msg extra))))

(defun acl2-doc-where ()
  (interactive)
  (cond ((consp *acl2-doc-history*)
         (acl2-doc-display-message (car *acl2-doc-history*)))
        (t (error "Empty history: No `where' to display!"))))

(defun xdoc-tag-alist-fancy-p (val)

;;; Keep this in sync with function xdoc-tag-alist-fancy-p in
;;; books/system/doc/display.lisp.

  (or (null val)
      (equal val "")
      (equal (upcase val) "FANCY")))

(defvar *acl2-manual-dir*
  (concat *acl2-sources-dir*
          "books/doc/manual/"))

(defvar *img-prefix*
  (byte-to-string 25))

(defvar *img-suffix*
  (byte-to-string 26))

(defun acl2-doc-handle-images (display-graphic-p)
  (save-excursion
    (goto-char (point-min))
    (let ((go t))
      (while go
        (let ((start (search-forward *img-prefix* nil t)))
          (cond
           (start
            (let* ((end (search-forward *img-suffix*))
                   (src (buffer-substring start (1- end))))
              (delete-region (1- start) end)
              (cond
               (display-graphic-p
                (insert-image
                 (create-image (concat *acl2-manual-dir* src)))
                (insert "\n"))
               (t (insert "{IMAGE}")))))
           (t (setq go nil))))))))

(defun acl2-doc-handle-color ()

;;; This function removes color indicators for Select Graphic Rendition (SGR)
;;; in the current buffer.  If we want color, then we should use
;;; ansi-color-apply-on-region to set color properties; if we want plain text
;;; without color then we should use ansi-color-filter-region, which anyhow is
;;; much more efficient than ansi-color-apply-on-region.

  (if (xdoc-tag-alist-fancy-p (getenv "ACL2_XDOC_TAGS"))
      (ansi-color-apply-on-region (point-min) (point-max))
    (ansi-color-filter-region (point-min) (point-max))))

(defun acl2-doc-display-basic (entry &optional extra no-handle-images)

;;; Entry is a history entry, hence of the form (point name parents
;;; string).

;;; The first form below is unnecessary if the caller is
;;; acl2-doc-display, but it's cheap.

  (switch-to-acl2-doc-buffer)
  (setq buffer-read-only nil)
  (erase-buffer)
  (acl2-doc-print-topic (cdr entry))  ; entry is (cons position tuple)
  (acl2-doc-handle-color)
  (when (not no-handle-images)
    (acl2-doc-handle-images (display-graphic-p))
    (setq buffer-read-only t))
  (goto-char (nth 0 entry))
  (push (car (cdr entry)) *acl2-doc-all-topics-rev*)
  (acl2-doc-display-message entry extra))

(defun acl2-doc-display (name &optional extra new-buffer no-handle-images)

;;; Name should be a symbol.  We display the topic and adjust the
;;; history and return history.  Do not use this for the "l" or "r"
;;; commands; use acl2-doc-display-basic instead, which does not mess
;;; with those history variables.

  (let ((tuple (assoc name (acl2-doc-state-alist))))
    (cond (tuple (switch-to-acl2-doc-buffer new-buffer)
                 (let ((new-entry (cons 0 tuple)))
                   (if *acl2-doc-history*
                       (let ((old-entry (pop *acl2-doc-history*)))
                         (push (cons (point) (cdr old-entry))
                               *acl2-doc-history*)))
                   (push new-entry *acl2-doc-history*)
                   (setq *acl2-doc-return* nil)
                   (acl2-doc-display-basic new-entry extra no-handle-images)))
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

;;; We have found that (sexp-at-point) returns nil when standing in text (in
;;; acl2-doc mode) that ends in a square bracket followed by a period, e.g.,
;;; "[loop-stopper]."  So we try again.

      (setq sym
            (save-excursion
              (if (< (point) (point-max))
                  (forward-char 1)) ; in case we are at "["
              (let* ((saved-point (point))
                     (start (if (looking-at "[[]")
                                (point)
                              (and (search-backward "[" nil t)
                                   (match-beginning 0)))))
                (and start
                     (let ((end (and (search-forward "]" nil t)
                                     (match-end 0))))
                       (and end
                            (<= saved-point end)
                            (goto-char (1+ start))
                            (not (search-forward " " end t))
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
                   ((numberp sym) ; e.g. from [1]
                    nil)
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

(defun acl2-doc-go-new-buffer (name)

  "Go to the specified topic in a new buffer; performs completion."

  (interactive (acl2-doc-completing-read "Go to topic (new buffer)" nil))
  (acl2-doc-display name nil name))

(defun acl2-doc-go-from-anywhere (name)

  "Go to the specified topic even if not within ACL2-Doc; performs completion."

  (interactive (with-syntax-table lisp-mode-syntax-table
                 (acl2-doc-completing-read "Go to topic" nil)))
  (when (not (acl2-doc-buffer-p (current-buffer)))
    (setq *acl2-doc-show-help-message* t))
  (acl2-doc-display name))

;;; Avoid warning in Emacs 25.
(defvar acl2-doc-find-tag-function
  'find-tag)

(defun acl2-doc-go!-aux (new-buffer-p)
  (let ((name (acl2-doc-topic-at-point)))
    (cond ((not name)
           (error "Cursor is not on a name"))
          ((assoc name (acl2-doc-state-alist))

;;; This code is a bit inefficient: the assoc above is done again by
;;; acl2-doc-display.  But I like the simplicity of this code.

           (when new-buffer-p (switch-to-acl2-doc-buffer name))
           (acl2-doc-display name))
          ((acl2-doc-tagp (symbol-name name))
           (when new-buffer-p
             (if pop-up-windows ; t by default; with nil, want single window
                 (switch-to-buffer-other-window nil t)
               (switch-to-buffer nil)))
           (acl2-doc-find-tag (acl2-doc-topic-to-tags-name name) nil t))
          (t
           (error "No topic name: %s" name)))))

(defun acl2-doc-go! ()

  "Go to the topic occurring at the cursor position.  In the case
of <NAME>, instead go to the source code definition of NAME for
the current manual (as for `/', but without a minibuffer query)."

  (interactive)
  (acl2-doc-go!-aux nil))

(defun acl2-doc-go!-new-buffer ()

  "Go to the topic occurring at the cursor position in a new
buffer.  In the case of <NAME>, instead go to the source code
definition of NAME for the current manual (as for `/', but
without a minibuffer query)."

  (interactive)
  (acl2-doc-go!-aux t))

(defun acl2-doc-top ()
  "Go to the top topic."
  (interactive)
  (setq *acl2-doc-show-help-message* t)
  (acl2-doc-go (acl2-doc-state-top-name)))

(defun acl2-doc (&optional clear)

  "Go to the ACL2-Doc browser; prefix argument clears state.
See the documentation topic for ACL2-Doc for more
information, either by starting ACL2-Doc and typing `h'
\(help), by viewing the ACL2-DOC topic in a web browser, or by
typing `:doc acl2-doc' in the ACL2 read-eval-print loop.

\\{acl2-doc-mode-map}"

  (interactive "P")
  (setq *acl2-doc-show-help-message* t)
  (cond (clear
         (acl2-doc-reset nil)
         (acl2-doc-top))
        (t
         (switch-to-acl2-doc-buffer)
         (cond (*acl2-doc-history*
                (acl2-doc-display-basic (car *acl2-doc-history*)))
               (t
                (acl2-doc-maybe-reset)
                (acl2-doc-top))))))

(defun acl2-doc-last ()
  "Go to the last topic visited in the current buffer.  This
   command is buffer-local."
  (interactive)
  (cond ((cdr *acl2-doc-history*)
         (push (pop *acl2-doc-history*)
               *acl2-doc-return*)
         (acl2-doc-display-basic (car *acl2-doc-history*)))
        (t (error "No last page visited"))))

(defun acl2-doc-return ()
  "Return to the last topic visited in the current buffer, popping
the stack of such topics.  This command is buffer-local."
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
    (cond ((null first-parent)
           (cond ((save-excursion
                    (goto-char (point-min))
                    (forward-line 1)
                    (member (acl2-doc-read-line)
                            '("Parent list: nil"
                              "Parent list: NIL"
                              "Parent list: ()")))
                  (error "Already at the root node of the manual"))
                 (t (error "Internal ACL2-Doc error in acl2-doc-up.
Please report this error to the ACL2 implementors."))))
          (t (acl2-doc-display first-parent)))))

(defun acl2-doc-update-top-history-entry (buf &optional no-error)
  (cond ((null *acl2-doc-history*)
         (if no-error
             nil
           (error "Empty history!")))
        (t (with-current-buffer
               buf
             (setq *acl2-doc-history*
                   (cons (cons (point) (cdr (car *acl2-doc-history*)))
                         (cdr *acl2-doc-history*)))))))

(defun acl2-doc-quit ()

  "Quit the current ACL2-Doc buffer."

  (interactive)
  (unless (eq major-mode 'acl2-doc-mode)
    (error "Currently not in an ACL2-Doc buffer; consider using 'M-x acl2-doc-kill-buffers'"))
  (when (acl2-doc-buffer-p (current-buffer))
    (acl2-doc-update-top-history-entry (current-buffer)))

;;; At one time we invoked (while (equal major-mode 'acl2-doc-mode)
;;; (quit-window)), so that we would continue to quit, including
;;; acl2-doc-history etc.  But a session that invoked emacs -nw from a
;;; terminal on the Mac, that seemed to put us into an infinite loop.
;;; It seems fine to quit just the current buffer.

  (quit-window))

(defun acl2-doc-initialize (&optional select)

  "Restart the ACL2-Doc browser, clearing its state.  With a
prefix argument, a query asks you to select the name of an
available manual, using completion.  See the section \"Selecting
a Manual\" in :doc acl2-doc for more information."

  (interactive "P")
  (acl2-doc-reset
   (and select
        (let* ((default
                 (cond (*acl2-doc-manual-name-previous*)
                       ((and (eq (acl2-doc-manual-name)
                                 (caar *acl2-doc-manual-alist*))
                             (consp (cdr *acl2-doc-manual-alist*)))
                        (car (cadr *acl2-doc-manual-alist*)))
                       ((or (caar *acl2-doc-manual-alist*) ; should be non-nil
                            (acl2-doc-manual-name)))))
               (s (completing-read
                   (format "Select manual (default %s): " default)
                   *acl2-doc-manual-alist*
                   nil nil nil nil
                   default)))
          (cond ((eq s default) default)
                (t (intern s))))))
  (acl2-doc-top))

; Start code for setting the limit topic.

;;; When *acl2-doc-limit-topic* is non-nil, it is the "limit topic": we want
;;; searches (including index operations) to be restricted to topics with a
;;; parent chain leading to the limit topic.  We'll call such topics
;;; "descendents".

;;; When *acl2-doc-topics-ht* is non-nil, this is a hash table mapping each
;;; descendent of *acl2-doc-limit-topic* to t.

;;; When *acl2-doc-children-ht* is non-nil, this variable is a hash table that
;;; maps each topic name to a hash table, which in turn maps children of that
;;; key to t.

(defun acl2-doc-topics-ht-1 (topic ht children-ht)

;;; We mark each node reachable from topic by a path following children-ht,
;;; stopping our exploration when we reach a node that is already marked.  A
;;; key idea is to avoid looping by marking the topic before exploring its
;;; children.

;;; It seems plausible that this algorithm marks in ht every node reachable
;;; from topic.  At some point maybe a proof will appear here.  Here we present
;;; an informal argument by induction on the length of a path from the
;;; top-level topic to a reachable node N.  For consider the first call of this
;;; function on N.  There is a call on some parent P, so by induction, P is
;;; marked; but the first mark of P will lead to a call of this function that
;;; marks N.

  (when (not (gethash topic ht)) ; otherwise we could loop
    (puthash topic t ht)
    (let ((topic-children-ht (gethash topic children-ht)))
      (when topic-children-ht
        (maphash (lambda (child val)
                   (when (null (gethash child ht))
                     (acl2-doc-topics-ht-1 child ht children-ht)))
                 topic-children-ht)))))

(defun acl2-doc-topics-ht-init (topic)
  (cond
   ((eq topic (acl2-doc-state-top-name)) ; no limitations
    (setq *acl2-doc-topics-ht* nil))
   (t ;; Set up initial *acl2-doc-children-ht*, mapping parents to children.
    (setq *acl2-doc-topics-ht* (make-hash-table :test 'eq))
    (when (null *acl2-doc-children-ht*)
      (setq *acl2-doc-children-ht* (make-hash-table :test 'eq)))
    ;; Map each parent to its children in *acl2-doc-children-ht*.
    (dolist (tup (acl2-doc-state-alist))
      (let ((topic (car tup))
            (parents (cadr tup)))
        (when (not (member parents '(NIL ())))
          (dolist (parent parents)
            (let ((ht (cond ((gethash parent *acl2-doc-children-ht*))
                            (t (let ((ht (make-hash-table :test 'eq)))
                                 (puthash parent
                                          ht
                                          *acl2-doc-children-ht*)
                                 ht)))))
              (puthash topic t ht))))))
    (acl2-doc-topics-ht-1 topic *acl2-doc-topics-ht* *acl2-doc-children-ht*)
    (puthash topic t *acl2-doc-topics-ht*)
    *acl2-doc-topics-ht*)))

(defun acl2-doc-set-limit-topic (do-it)
  (cond
   ((null do-it)
    (setq *acl2-doc-limit-topic* nil
          *acl2-doc-topics-ht* nil))
   (t
    (let ((name
           (car (acl2-doc-completing-read
                 "Search or index only under topic"
                 t))))
      (cond ((or (equal (symbol-name name) "")
                 (eq name *acl2-doc-limit-topic*))) ; nothing to do
            (t
             (let ((found-p (assoc name (acl2-doc-state-alist))))
               (cond (found-p (setq *acl2-doc-limit-topic* name)
                              (acl2-doc-topics-ht-init name))
                     (t (error "Unknown topic name: %s" name))))))))))

(defun acl2-doc-under-limit-topic-p (topic ht)

;;; Ht is the value of *acl2-doc-topics-ht* in the appropriate
;;; ACL2-Doc buffer.

  (or (null ht)
      (gethash topic ht)))

; End code for setting the limit topic.

(defun acl2-doc-index-buffer ()
  (or (get-buffer *acl2-doc-index-buffer-name*)
      (let ((buf (get-buffer-create *acl2-doc-index-buffer-name*))
            (alist (acl2-doc-state-alist)))
        (with-current-buffer
            buf
          (when *acl2-doc-directory* ; probably always true
            (setq default-directory *acl2-doc-directory*))
          (while alist
            (insert (format "%s\n" (car (pop alist)))))
          (acl2-doc-mode)
          (set-buffer-modified-p nil)
          (setq buffer-read-only t))
        buf)))

(defun acl2-doc-index-main (name)
  (interactive (acl2-doc-completing-read
                (format "Find topic%s (then type , for next match) "
                        (if *acl2-doc-limit-topic*
                            (format " under %s"
                                    *acl2-doc-limit-topic*)
                          ""))
                t))
  (let ((buf (acl2-doc-index-buffer))
        (ht *acl2-doc-topics-ht*)
        (limit-topic *acl2-doc-limit-topic*))
    (cond
     ((equal (symbol-name name) "")
      (switch-to-buffer *acl2-doc-index-buffer-name*)
      (goto-char (point-min)))
     (t
      (let ((found-p (and (acl2-doc-under-limit-topic-p name ht)
                          (assoc name (acl2-doc-state-alist))))
            topic
            point
            (count 0)
            (sname (symbol-name name)))
        (setq *acl2-doc-index-name-found-p* found-p) ; a cons
        (setq *acl2-doc-index-name* sname)
        (cond
         (found-p
          (with-current-buffer
              buf
            (goto-char (point-min))
            (while (search-forward sname nil t)
              (let ((sym (intern (acl2-doc-read-line))))
                (when (acl2-doc-under-limit-topic-p sym ht)
                  (setq count (1+ count)))))
            (goto-char (point-min)))
          (acl2-doc-display name
                            (format " (number of matches: %s)"
                                    count)))
         (t (with-current-buffer
                buf
              (goto-char (point-min))
              (while (search-forward sname nil t)
                (let ((sym (intern (acl2-doc-read-line))))
                  (when (acl2-doc-under-limit-topic-p sym ht)
                    (when (null topic)
                      (setq topic sym)
                      (setq point (point)))
                    (setq count (1+ count)))))
              (when point
                (goto-char point)))
            (cond (topic
                   (acl2-doc-display topic
                                     (format " (number of matches: %s)"
                                             count)))
                  (t (setq *acl2-doc-index-name* nil)
                     (error "No matching topic found%s"
                            (if limit-topic
                                (format " under %s" limit-topic)
                              "")))))))))))

(defun acl2-doc-index (&optional arg)

  "Go to the specified topic or else one containing it as a
substring; performs completion.  If the empty string is supplied,
then go to the index buffer.  Otherwise, with prefix argument,
consider only descendents of the topic supplied in response to a
prompt.  Note that the index buffer is in ACL2-Doc mode; thus, in
particular, you can type <RETURN> while standing on a topic in
order to go directly to that topic."

  (interactive "P")
  (acl2-doc-set-limit-topic arg)
  (let ((buf (acl2-doc-index-buffer)))
    (condition-case err
        (call-interactively 'acl2-doc-index-main)
      (t (setq *acl2-doc-index-position*
               (with-current-buffer buf (point)))
         (signal (car err) (cdr err))))
    (setq *acl2-doc-index-position*
        (with-current-buffer buf (point)))))

(defun acl2-doc-index-continue (previous-p)
  (let ((ht *acl2-doc-topics-ht*)
        (buf (get-buffer *acl2-doc-index-buffer-name*))
        (name *acl2-doc-index-name*)
        (limit-topic *acl2-doc-limit-topic*))
    (when (or (null buf) (null name))
      (error "Need to initiate index search"))
    (let* (topic
           (acl2-doc-index-sym
            (and *acl2-doc-index-name-found-p* ; optimization
                 (intern *acl2-doc-index-name*)))
           (found-p *acl2-doc-index-name-found-p*)
           (position *acl2-doc-index-position*))
      (with-current-buffer
          buf
        (goto-char position)
        (when previous-p

;;; If this is the first use of "," or "<" after "i", and the match was exact,
;;; then start the search backward in the index buffer from that match.
;;; (Otherwise we go forward from the current position, which is presumably the
;;; beginning of the index buffer.)

          (when (consp found-p)               ; start from the hit
            (when (equal (point) (point-min)) ; presumably true
              (search-forward (format "\n%s\n" name))
              (backward-char 1)         ; to previous line
              (setq found-p nil))))

;;; Note that subsequent uses of "," or "<" (after the same "i") are not the
;;; first.

        (setq found-p (and found-p t))
        (while (null topic)
          (cond ((cond (previous-p
                        (beginning-of-line)
                        (search-backward name nil t))
                       (t
                        (end-of-line)
                        (search-forward name nil t)))
                 (let ((sym (intern (acl2-doc-read-line))))
                   (when (acl2-doc-under-limit-topic-p sym ht)
                     (setq topic sym))))
                (t ;; set to failure indicator, 0
                 (setq topic 0))))
        (setq position (point)))
      (setq *acl2-doc-index-position* position)
      (setq *acl2-doc-index-name-found-p* found-p)
      (cond ((not (equal topic 0))      ; success
             (cond ((and found-p
                         (eq topic acl2-doc-index-sym))
                    (setq *acl2-doc-index-name-found-p* nil)
                    (acl2-doc-index-continue previous-p))
                   (t (acl2-doc-display topic))))
            (t (with-current-buffer
                   buf
                 (goto-char (if previous-p (point-max) (point-min)))
                 (setq position (point)))
               (setq *acl2-doc-index-position* position)
               (error
                "No more matches%s; repeat to re-start index search"
                (if limit-topic
                    (format " under %s" limit-topic)
                  "")))))))

(defun acl2-doc-index-next ()

  "Find the next topic containing, as a substring, the topic of
the most recent i command.  Note: if this is the first \",\" or
\"<\" after an exact match from \"i\", then start the topic
search alphabetically from the beginning, but avoid a second hit
on the original topic.  Also note that this command is
buffer-local; it will follow the most recent i command executed
in the current ACL2-Doc buffer."

  (interactive)
  (acl2-doc-index-continue nil))

(defun acl2-doc-index-previous ()

  "Find the previous topic containing, as a substring, the topic of
the most recent i command.  Note: if this is the first \",\" or \"<\"
after an exact match from \"i\", then start the topic search
alphabetically (backwards) from that exact match.  Also note that this
command is buffer-local like the \",\" command."

  (interactive)
  (acl2-doc-index-continue t))

(defun acl2-doc-search-buffer ()
;;; Return the search buffer, which contains all :doc topics, creating it first
;;; (with those topics inserted) if necessary.
  (or (get-buffer *acl2-doc-search-buffer-name*)
      (let ((acl2-doc-search-file-name (acl2-doc-search-file-name))
            (large-file-warning-threshold
             (acl2-doc-large-file-warning-threshold)))

; We assume that acl2-doc-search-file was written without Select Graphic
; Rendition (SGR) markings; see without-fancy-xdoc-tags and its use in
; books/xdoc/save-rendered.lisp.

        (and acl2-doc-search-file-name
             (file-exists-p acl2-doc-search-file-name)
             (find-file-noselect acl2-doc-search-file-name)))
      (let ((buf (get-buffer-create *acl2-doc-search-buffer-name*))
            (alist (acl2-doc-state-alist))
            (large-file-warning-threshold nil)
            (undo-outer-limit nil))
        (with-current-buffer
            buf
          (while alist
            (insert "\n")
            (insert *acl2-doc-search-separator*)
            (insert "\n")
            (acl2-doc-print-topic (pop alist)))

; Since we are writing the acl2-doc-search buffer, we need to remove
; Select Graphic Rendition (SGR) markings.  We leave the images, however.

          (acl2-doc-handle-color)
          (setq buffer-read-only t))
        buf)))

(defun within-graphics ()
  (let ((saved-point (point)))
    (save-excursion
      (let ((start (cond ((search-backward "\n" nil t)
                          (forward-char 1)
                          (point))
                         (t (point-min)))))
        (goto-char saved-point)
        (cond ((search-backward *img-prefix* start t)

;;; We are on a line "... ^Y ... p ..." where p indicates the original
;;; point (the beginning of a found string) and ^Y indicates the
;;; furthest-right control-y preceding p.  We look for control-z
;;; inbetween the two, and when one isn't found, that's when we are
;;; within a control-y/control-z pair.

               (not (search-forward *img-suffix* saved-point t)))
              (t nil))))))

(defun acl2-doc-search-aux-1 (continue-p str regexp-p)

; Returns a pair (position . topic-symbol) if we find str in the current
; (index) buffer, else nil.

  (cond
   ((if (eq continue-p :previous)

;;; In order to avoid sticking on the same result when changing directions, we
;;; always leave the cursor at the end of the match.  This takes a bit of extra
;;; code when searching backwards.

        (cond (regexp-p
               (and (save-excursion
                      (backward-char 1)
                      (re-search-backward str nil t))
                    (progn (goto-char (match-end 0))
                           t)))
              (t
               (and (save-excursion
                      (backward-char 1)
                      (search-backward str nil t))
                    (progn (goto-char (match-end 0))
                           t))))
      (if regexp-p
          (re-search-forward str nil t)
        (search-forward str nil t)))
    (save-excursion
      (let ((point-found (match-end 0)))
        (search-backward *acl2-doc-search-separator*)
        (forward-line 1)
        (let ((point-start (point)))

;;; Why do we add 2 just below?  We add 1 because (point-min) = 1, and
;;; we add one more because acl2-doc-print-topic prints a blank line
;;; below the ":DOC source" line but the acl2-doc-search buffer is
;;; printed without that blank line.

          (cons (+ 2 (- point-found point-start))
                (let ((beg (+ point-start 7)))   ;;"Topic: "
                  (end-of-line)
                  (intern (buffer-substring beg (point)))))))))
   (t nil)))

(defun acl2-doc-search-aux (str regexp-p)
  (when (equal str "")
    (error "Input a search string, or type \"n\" to continue previous search"))
  (let* ((ht *acl2-doc-topics-ht*)
         (limit-topic *acl2-doc-limit-topic*)
         (buf (acl2-doc-search-buffer))
         (continue-p (and (or (eq regexp-p :next)
                              (eq regexp-p :previous))
                          regexp-p))
         (str (cond
               ((not continue-p) str)
               (t (or *acl2-doc-search-string*
                      (error "There is no previous search to continue")))))
         (regexp-p (if continue-p
                       *acl2-doc-search-regexp-p*
                     regexp-p))
         (pair nil)
         (position *acl2-doc-search-position*))
    (with-current-buffer
        buf
      (if continue-p
          (goto-char position)
        (goto-char (point-min)))
      (let (done)
        (while (not done)
          (let ((tmp (acl2-doc-search-aux-1 continue-p str regexp-p)))
            (cond ((null tmp)
                   (setq done t))
                  ((acl2-doc-under-limit-topic-p (cdr tmp) ht)
                   (if (not (within-graphics))
                       (setq pair tmp done t))))))
        (setq position (point))))
    (cond (pair
           ;; The first two assignments are redundant if continue-p is true.
           (setq *acl2-doc-search-string* str)
           (setq *acl2-doc-search-regexp-p* regexp-p)
           (setq *acl2-doc-search-position* position)

;;; At one time we could use the current buffer if it's the one
;;; containing the search string.  But we need to go to the
;;; appropriate character, (car pair), before we eliminate the
;;; Ctl-Y/Ctl-Z pairs.

           (acl2-doc-display (cdr pair) nil nil t)
           (goto-char (car pair))
           (acl2-doc-handle-images (display-graphic-p))
           (setq buffer-read-only t)
           (acl2-doc-update-top-history-entry (current-buffer)))
          (continue-p (setq *acl2-doc-search-position*
                            (with-current-buffer
                                buf
                              (goto-char (if (eq continue-p :previous)
                                             (point-max)
                                           (point-min)))))
                      (error
                       "No more matches%s; try again for wrapped search"
                       (if limit-topic
                           (format " under %s" limit-topic)
                         "")))
          (t (error "Not found: %s" str)))))

(defun acl2-doc-search-main (str)
  (interactive
   (list
    (read-from-minibuffer
     (format "Search%s (then type n for next match): "
             (if *acl2-doc-limit-topic*
                 (format " under %s"
                         *acl2-doc-limit-topic*)
               "")))))
  (acl2-doc-search-aux str nil))

(defun acl2-doc-search (&optional arg)

  "Search forward from the top of the manual for the input string.  If
the search succeeds, then go to that topic with the cursor put
immediately after the found text, with the topic name displayed in the
minibuffer.  With prefix argument, consider (also for subsequent \"n\"
and \"p\" commands) only descendents of the topic supplied in response
to a prompt."

  (interactive "P")
  (acl2-doc-set-limit-topic arg)
  (call-interactively 'acl2-doc-search-main))

(defun acl2-doc-re-search-main (str)
  (interactive
   (list
    (read-from-minibuffer
     (format "Regular Expression Search%s (then type n for next match): "
             (if *acl2-doc-limit-topic*
                 (format " under %s"
                         *acl2-doc-limit-topic*)
               "")))))
  (acl2-doc-search-aux str t))

(defun acl2-doc-re-search (str)

  "Perform a regular expression search, forward from the top of the
manual, for the input string.  If the search succeeds, then go to that
topic with the cursor put immediately after the found text, with the
topic name displayed in the minibuffer.  With prefix argument,
consider (also for subsequent \"n\" and \"p\" commands) only
descendents of the topic supplied in response to a prompt."

  (interactive "P")
  (acl2-doc-set-limit-topic str)
  (call-interactively 'acl2-doc-re-search-main))

(defun acl2-doc-search-next ()

  "Find the next occurrence for the most recent search or regular
expression search.  Note that this command is buffer-local; it
will follow the most recent search initiated in the current
buffer."

  (interactive)
  (acl2-doc-search-aux nil :next))

(defun acl2-doc-search-previous ()

  "Find the previous occurrence for the most recent search or regular
expression search.  Note: as for \"n\", the cursor will end up at the end
of the match, and this command is buffer-local."

  (interactive)
  (acl2-doc-search-aux nil :previous))

(defun acl2-doc-tab ()

  "Visit the next link after the cursor on the current page,
searching from the top if no link is below the cursor."

  (interactive)
  (switch-to-acl2-doc-buffer)
  (cond ((or (re-search-forward "[[][^ ]+]" nil t)
             (progn (goto-char (point-min))
                    (beep)
                    (message "Searching from the top...")
                    (re-search-forward "[[][^ ]+]" nil t)))
         (search-backward "[")
         (forward-char 1))
        (t (error "There are no links on this page."))))

(defun acl2-doc-tab-back ()

  "Visit the previous link before the cursor on the current page,
searching from the bottom if no link is below the cursor."

  (interactive)
  (switch-to-acl2-doc-buffer)
  (cond ((or (re-search-backward "[[][^ ]+]" nil t)
             (progn (goto-char (point-max))
                    (beep)
                    (message "Searching from the bottom...")
                    (re-search-backward "[[][^ ]+]" nil t)))
         (forward-char 1))
        (t (error "There are no links on this page."))))

(defun strip-cadrs (x)
  (let ((ans nil))
    (while x
      (push (cadr (car x)) ans)
      (setq x (cdr x)))
    (reverse ans)))

(defun acl2-doc-history ()

  "Visit a buffer that displays the names of all topics visited
(in any ACL2-Doc buffer) in order, newest at the bottom.  That
buffer is in acl2-doc mode; thus the usual acl2-doc commands may
be used.  In particular, you can visit a displayed topic name by
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

;;; We could bind x to *acl2-doc-history* and execute the commented-out form
;;; just below, after printing a separator such as the one above.  If someone
;;; asks for this, we should think about printing the topics in
;;; *acl2-doc-return* as well, and maybe even display a single list if we can
;;; figure out a reasonable way to do so while indicating "last" and "return"
;;; information.

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

(defun acl2-doc-summary ()

  "Go to the ACL2-DOC-SUMMARY topic for one-line summaries of
ACL2-Doc browser commands."

  (interactive)
  (acl2-doc-go 'ACL2-DOC-SUMMARY))

; Start implementations of acl2-doc-definition and
; acl2-doc-where-definition.

(defun acl2-doc-tagp (name)

;;; This function recognizes strings of the form "<...>".  For
;;; convenience, instead of returning t in the true case, it returns
;;; the length of name.

  (let ((len (length name)))
    (and (equal (aref name 0) ?<)
         (equal (aref name (1- len)) ?>)
         len)))

(defun acl2-doc-topic-to-tags-name (topic)
  (and topic
       (let* ((name0 (symbol-name topic))
              (len (acl2-doc-tagp name0))
              (name (cond (len (substring name0 1 (1- len)))
                          (t name0)))
              (colon-pos (my-cl-position ?: name)))
         (cond ((and colon-pos
                     (< (1+ colon-pos) (length name))
                     (equal (aref name (1+ colon-pos)) ?:))
                (substring name (+ 2 colon-pos) (length name)))
               (t name)))))

(defun acl2-doc-tags-name-at-point ()
  (let ((topic (acl2-doc-topic-at-point)))
    (acl2-doc-topic-to-tags-name topic)))

(defun acl2-doc-find-tag-next ()
  (let ((new-tags-file-name *acl2-doc-last-tags-file-name*)
        (old-tags-file-name tags-file-name))
    (unwind-protect
        (let ((tags-add-tables t)
              (tags-case-fold-search t)) ; the name may be upper-case
          (visit-tags-table new-tags-file-name)
          (funcall acl2-doc-find-tag-function nil t)

;;; We leave the buffer if and only if find-tag fails to cause an
;;; error, which is when we save the point much as we do with
;;; acl2-doc-quit.

          (if (acl2-doc-buffer-p (current-buffer))
              (acl2-doc-update-top-history-entry (current-buffer) t)))
      (if old-tags-file-name
          (visit-tags-table old-tags-file-name)))))

(defun acl2-doc-find-tag-topic (default)
  (completing-read
   (if default
       (format "Find tag (default %s): " default)
     (format "Find tag: "))
   (tags-lazy-completion-table)
   nil nil nil nil
   default))

(defun acl2-doc-find-tag (default acl2-only &optional use-default)
  (let ((new-tags-file-name (if acl2-only
                                (acl2-doc-acl2-tags-file-name)
                              (acl2-doc-main-tags-file-name)))
        (old-tags-file-name tags-file-name))
    (cond
     ((equal new-tags-file-name nil)
      (error "No tags table specified%s in %s"
             (if acl2-only " for ACL2 sources" "")
             (acl2-doc-manual-printname)))
     ((not (file-exists-p new-tags-file-name))
      (error "The tags table file %s does not exist.
See the online (XDOC) documentation for acl2-doc for how to build it."
             new-tags-file-name))
     ((not (file-readable-p new-tags-file-name))
      (error "The tags table file %s exists, but is not readable.
See the online (XDOC) documentation for acl2-doc for how to build it."
             new-tags-file-name))
     (t (unwind-protect
            (let ((tags-add-tables nil)
                  (tags-case-fold-search t)) ; the name may be upper-case
              (visit-tags-table new-tags-file-name)
              (funcall acl2-doc-find-tag-function
                       (if use-default
                           default
                         (acl2-doc-find-tag-topic default)))

;;; If there is no error, then remember what we have in case we want
;;; to find more matches.

              (setq *acl2-doc-last-tags-file-name* new-tags-file-name)

;;; We leave the buffer if and only if find-tag fails to cause an
;;; error, which is when we save the point much as we do with
;;; acl2-doc-quit.

              (acl2-doc-update-top-history-entry (current-buffer) t))
          (if old-tags-file-name
              (visit-tags-table old-tags-file-name)
            (tags-reset-tags-tables)))))))

(defun acl2-doc-definition (arg)

  "Find an ACL2 definition (in analogy to built-in Emacs command meta-.).
With numeric prefix argument, find the next matching definition;
otherwise, the user is prompted, where the default is the name at
the cursor, obtained after stripping off any enclosing square
brackets ([..]), angle brackets (<..>) as from srclink tags, and
package prefixes.  With control-u prefix argument, search only
ACL2 source definitions; otherwise, books are searched as well.
As with built-in Emacs command meta-. , exact matches are given
priority.  For more information, see the Section on \"Selecting a
Manual\" in the acl2-doc online XDOC-based documentation."

  (interactive "P")
  (if (and arg (not (equal arg '(4)))) ;; prefix arg, not control-u
      (acl2-doc-find-tag-next)
    (acl2-doc-find-tag (acl2-doc-tags-name-at-point) arg)))

(defun acl2-doc-where-definition (arg)

  "Find an ACL2 definition.  This is the same as
acl2-doc-definition (the acl2-doc `/' command, as well as
control-t /), except that the default comes from the name of the
current page's topic instead of the cursor position.  Searches
are continued identically when control-t / is given a numeric
prefix argument, regardless of whether the first command was /,
control-t /, or W; thus, a search started with W can be continued
with, for example, meta-3 control-t /."

  (interactive "P")
  (if (and arg (not (equal arg '(4)))) ;; prefix arg, not control-u
      (acl2-doc-find-tag-next)
    (acl2-doc-find-tag
     (acl2-doc-topic-to-tags-name (car (cdr (car *acl2-doc-history*))))
     arg)))

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
(define-key global-map "\C-t." 'acl2-doc-go-from-anywhere)
(define-key global-map "\C-t/" 'acl2-doc-definition)
(define-key acl2-doc-mode-map " " 'scroll-up)
(define-key acl2-doc-mode-map "," 'acl2-doc-index-next)
(define-key acl2-doc-mode-map "<" 'acl2-doc-index-previous)
(define-key acl2-doc-mode-map "D" 'acl2-doc-download)
(define-key acl2-doc-mode-map "H" 'acl2-doc-history)
(define-key acl2-doc-mode-map "I" 'acl2-doc-initialize)
(define-key acl2-doc-mode-map "S" 'acl2-doc-re-search)
(define-key acl2-doc-mode-map "\C-M" 'acl2-doc-go!)
(define-key acl2-doc-mode-map (kbd "S-<return>")
  'acl2-doc-go!-new-buffer)
(define-key acl2-doc-mode-map "K" 'acl2-doc-kill-buffers)
(define-key acl2-doc-mode-map "\t" 'acl2-doc-tab)
(define-key acl2-doc-mode-map "/" 'acl2-doc-definition)
(define-key acl2-doc-mode-map "g" 'acl2-doc-go)
(define-key acl2-doc-mode-map "G" 'acl2-doc-go-new-buffer)
(define-key acl2-doc-mode-map "h" 'acl2-doc-help)
(define-key acl2-doc-mode-map "?" 'acl2-doc-summary)
(define-key acl2-doc-mode-map "i" 'acl2-doc-index)
(define-key acl2-doc-mode-map "l" 'acl2-doc-last)
(define-key acl2-doc-mode-map "n" 'acl2-doc-search-next)
(define-key acl2-doc-mode-map "p" 'acl2-doc-search-previous)
(define-key acl2-doc-mode-map "q" 'acl2-doc-quit)
(define-key acl2-doc-mode-map "r" 'acl2-doc-return)
(define-key acl2-doc-mode-map "s" 'acl2-doc-search)
(define-key acl2-doc-mode-map "t" 'acl2-doc-top)
(define-key acl2-doc-mode-map "u" 'acl2-doc-up)
(define-key acl2-doc-mode-map "w" 'acl2-doc-where)
(define-key acl2-doc-mode-map "W" 'acl2-doc-where-definition)
(define-key acl2-doc-mode-map (kbd "<backtab>") 'acl2-doc-tab-back)
