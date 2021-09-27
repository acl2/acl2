; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This is an extension to emacs/acl2-doc.el that defines the key, U,
; to bring up a URL, or a local file "res/...", in a web browser.  It
; should only be loaded after emacs/acl2-doc.el is loaded.

; Of course, this won't work if you are running acl2-doc from inside
; an Emacs that is not window-based -- for example, if your Emacs is
; running from within the "screen" program.

; At some point this file might be incorporated into acl2-doc.el.
; Perhaps the "g" command will be enhanced at that point, so that if
; one is looking at a word that seems to represent a URL or a local
; "res/..." name, then an error message will suggest using "U"
; instead.  Or perhaps "g" will simply invoke "U" in that case.

; Requirements:

; You'll need Emacs variable browse-url-browser-function to be set to
; browse-url-PROGRAM, where PROGRAM brings up a browser.  For example,
; you could put the form (setq browse-url-browser-function (quote
; browse-url-firefox)) in your ~/.emacs file, which will set
; browse-url-browser-function to the value, browse-url-firefox.  But
; then the command, firefox, needs to be on your path.  One way to
; accomplish this is to arrange for Emacs variable exec-path to
; include, say, "~/bin", in the list value of Emacs variable exec-path
; -- e.g., by including into your .emacs file the form
;   (setq exec-path
;         (append (butlast exec-path 1) '("~/bin") (last exec-path)))
; -- and then have something like the following in ~/bin/firefox (this
; has worked on a Mac; a different command, perhaps just a call of
; "firefox" [rather than "open"], may work on Linux):

; #!/usr/bin/env bash
; open -a 'firefox' "$@"

(defun manual-dir ()
  (concat *acl2-doc-directory* "../../doc/manual"))

(defun acl2-doc-open-url ()
  (interactive)
  (let ((topic (acl2-doc-topic-at-point)))
    (if (not topic)
	(error "No topic at point."))
    (let* ((topic (downcase (symbol-name topic)))
	   (len (length topic)))
      (if (equal (aref topic (1- len)) ?})
	  (setq topic (substring topic 0 (1- len))))
      (let ((url (if (and (> len 4)
			  (equal (substring topic 0 4) "res/"))
		     (concat "file://" (manual-dir) "/" topic)
		   (if (and (> len 4)
			    (equal (substring topic 0 4) "http"))
		       topic
		     (error "No available topic at point.")))))
	(browse-url url)))))

(define-key acl2-doc-mode-map "U" 'acl2-doc-open-url)
