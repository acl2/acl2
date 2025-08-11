;;; -*- lexical-binding: t -*-
; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

; These utilities have been used as part of a process of converting to
; XDOC an HTML file that was already created using latex2html.  There
; is little documentation, but it may be helpful in future projects,
; in which case it may be straightforward to add documentation at that
; time.

; This file assumes that ctl-t-keymap has been defined, and might more
; generally assume that emacs-acl2.el has been loaded.

(defun within-tag (start-tag end-tag)
  (let ((saved-point (point)))
    (cond ((search-backward start-tag nil t)
           (let ((p (match-beginning 0)))
             (goto-char saved-point)
             (cond ((search-backward end-tag nil t)
                    (goto-char saved-point)
                    (< (match-end 0) p))
                   (t t))))
          (t nil))))

(defun html-end-paragraphs ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (search-forward "\n\n" nil t)
      (let ((p0 (match-beginning 0)))
        (when (not (or (within-tag "<ul>" "</ul>")
                       (within-tag "<ol>" "</ol>")
                       (within-tag "<dl>" "</dl>")
                       (within-tag "<pre>" "</pre>")))
          (goto-char p0)
          (insert "\n</p>")
;;; Move past newlines.
          (while (looking-at "\n")
            (forward-char 1)))))))

(defun html-fix-p-tag-within-lists ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (search-forward "<p>" nil t)
      (let ((p0 (match-end 0)))
        (when (or (within-tag "<ul>" "</ul>")
                  (within-tag "<ol>" "</ol>")
                  (within-tag "<dl>" "</dl>"))
; Deliberately omitted <pre> above.
          (goto-char (- p0 1))
          (insert "/"))))))

(defun html-fix-string (old new)
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (search-forward old nil t)
      (replace-match new nil t))))

(defun html-fix-strings ()
  (interactive)
  (html-fix-string "\\" "\\\\")
  (html-fix-string "\"" "\\\"")
  (html-fix-string "&ldots;" "&hellip;")
; Latex2html has translated \ptt{<<=} to <tt>&laquo;=</tt>.
  (html-fix-string "&laquo;=" "&lt;&lt;="))

(defun html-remove-comments ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (search-forward "<!--" nil t)
      (let ((beg (match-beginning 0)))
        (search-forward "-->")
; Avoid blank lines that could cause paragraph markers to be added.
        (while (looking-at "\n") (forward-char 1))
        (delete-region beg (point))))))

(defun html-balance-br ()
  (interactive)
  (html-fix-string "<br>" "<br/>"))

(defun html-error-on-bad-stuff ()
  (interactive)
  (let ((saved-point (point)))
    (goto-char (point-min))
    (cond
     ((search-forward "<sup>" nil t)
      (goto-char (match-beginning 0))
      (error "Need to deal with <sup> here."))
     ((search-forward "<!-- MATH" nil t)
      (goto-char (match-beginning 0))
      (error "Need to deal with MATH comment here."))
     ((search-forward ".svg" nil t)
      (goto-char (match-beginning 0))
      (error "Need to deal with image here."))
     ((search-forward "<br/>" nil t)
      (goto-char (match-beginning 0))
      (error "Found <br/>; need to deal with <br> tags manually."))
     (t (goto-char saved-point)))))

(defun html-convert-tt ()
  (interactive)
  (goto-char (point-min))
  (while (search-forward "<span  class=\"texttt\">" nil t)
    (let ((p1 (match-beginning 0))
          (p2 (match-end 0)))
      (search-forward "</span>")
      (let ((p3 (match-beginning 0))
            (p4 (match-end 0)))
        (goto-char p2)
        (cond
         ((search-forward "<span" p3 t)
          (goto-char (match-beginning 0))
          (error "Unable to handle nested span tags within texttt"))
         (t
          (delete-region p3 p4)
          (goto-char p3)
          (insert "</tt>")
          (delete-region p1 p2)
          (goto-char p1)
          (insert "<tt>")))))))

(defun html-remove-span-1 (point1 point2)

; Here point1 and point2 are start and end positions of "<span".

  (search-forward "</span>")
  (let ((point3 (match-beginning 0))
        (point4 (match-end 0)))
    (ignore point4)
    (goto-char point2)
    (cond ((search-forward "class=\"texttt\"" point3 t)) ; just continue
          ((search-forward "<span" point3 t)
           (goto-char point1)
           (error "Unable to handle nested span tags here"))
          ((not (or (search-forward "class=\"MATH\"" point3 t)
                    (search-forward "class=\"arabic\"" point3 t)))
           (goto-char point1)
           (error "Unknown class here!"))
          (t
           (goto-char point3)
           (kill-sexp)
           (goto-char point1)
           (kill-sexp)))))

(defun html-remove-span ()
  (interactive)
  (goto-char (point-min))
  (while (search-forward "<span" nil t)
    (html-remove-span-1 (match-beginning 0) (match-end 0))))

(defun html-fix-sub ()
  (interactive)
  (goto-char (point-min))
  (let ((saved-point (point)))
    (ignore saved-point)
    (while (re-search-forward "</i><sub>\\(.*\\)</sub>" nil t)
;;;                              0        1       2     3
      (let* ((p0 (match-beginning 0))
             (p1 (match-beginning 1)))
        (goto-char p1)
        (search-forward "</sub>")
        (let* ((p2 (match-beginning 0))
               (p3 (match-end 0))
               (subscript (buffer-substring p1 p2)))
          (goto-char p1)
          (when (search-forward "sub>" p2 t)
            (error "Nested subscripts found here; must fix manually"))
          (delete-region (+ p0 4) p3)
          (goto-char p0)
          (insert "_")
          (insert subscript))))))

(defun html-replace-string (from-string to-string start end)

; This is just a version of replace-string to use in a program, to
; avoid byte compiler warnings in some versions of Emacs.

  (save-excursion
    (goto-char start)
    (while (search-forward from-string end t)
      (replace-match to-string end t))))

(defun html-convert-code-to-tt-and-pre-to-code ()
  (interactive)
  (html-replace-string "<code>" "<tt>" (point-min) (point-max))
  (html-replace-string "</code>" "</tt>" (point-min) (point-max))
  (html-replace-string "<pre>" "<code>" (point-min) (point-max))
  (html-replace-string "</pre>" "</code>" (point-min) (point-max)))

(defun html-remove-monospace-for-tt ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (search-forward "<span style=\"font-family:monospace\">" nil t)
      (replace-match "<span  class=\"texttt\">"))))

(defun html-convert-tt-atsigns-to-code ()

;;; E.g., convert

;; <span  class="texttt">@@@
;; <em>Base&nbsp;Case:</em>
;; <br>(implies&nbsp;(not&nbsp;(consp&nbsp;x))
;; <br>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="MATH"><i>&psi;</i></span>)
;; <br>@@@
;; </span>

;;; to:

;; <code>
;; <em>Base Case:</em>
;; (implies (not (consp x))
;;          <span class="MATH"><i>&psi;</i></span>)
;; </code>

  (interactive)
  (goto-char (point-min))
  (while (search-forward "<span  class=\"texttt\">@@@" nil t)
    (let ((p0 (match-beginning 0))
          (p1 (match-end 0))
          (newline-br-atsigns-string "\n<br>@@@"))
      (search-forward newline-br-atsigns-string)
      (let ((p2 (+ 1 (match-beginning 0))))
        (html-replace-string "&nbsp;" " " p1 p2)
;;; Now recalculate end points.
        (goto-char p1)
        (search-forward newline-br-atsigns-string)
        (let ((p2 (+ 1 (match-beginning 0))))
          (html-replace-string "<br>" "" p1 p2)
;;; Now recalculate end points.
          (search-forward (concat newline-br-atsigns-string "\n</span>"))
          (replace-match "</code>")
          (goto-char p0)
          (delete-region p0 p1)
          (insert "<code>"))))))

(defun html-convert ()
  (interactive)
  (html-mode)
  (untabify (point-min) (point-max))
  (html-remove-comments)
  (html-error-on-bad-stuff)
  (html-convert-code-to-tt-and-pre-to-code)
  (html-convert-tt-atsigns-to-code)
  (html-balance-br)
  (html-remove-monospace-for-tt)

; It's probably much more common to have $..$ within a texttt
; environment than vice versa.  So we remove the "MATH" (and "arabic")
; stuff first, skipping over texttt.

  (html-remove-span)
  (html-end-paragraphs)
  (html-convert-tt)
  (html-fix-sub)
  (html-fix-p-tag-within-lists)
  (html-fix-strings)
  (indent-rigidly (point-min) (point-max) 1)
  (untabify (point-min) (point-max)))

(define-key ctl-t-keymap "h" 'html-convert)
(define-key ctl-t-keymap "m" 'html-remove-span)

; The following keyboard macro expects one to be on a line of the form
; nodexx.html
; for some "xx".  It switches to a (hopefully new) buffer, "nodexx",
; and inserts the contents of notes-version-6/nodexx.html.
; This probably isn't of general use but I found it useful and it
; might inspire development of a more general utility.

(fset 'node
   [?\C-a ?\C-f ?\C-f ?\C-  ?\C-e ?\M-w ?\C-x ?b ?\C-y backspace backspace backspace backspace backspace return ?\C-x ?i ?n ?o ?t ?e ?s ?- ?v ?e ?r ?s ?i ?o ?n ?- ?6 ?/ ?\C-y return ?\C-s ?< ?a ?  ?i ?d ?= ?\C-n ?\C-n ?\C-n ?\C-n ?\C-a ?\M-< ?\C-w ?\M-> ?\C-  ?\C-p ?\C-p ?\C-p ?\C-p ?\C-p ?\C-w])
