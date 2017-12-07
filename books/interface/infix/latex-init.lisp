; ACL2 Version 1.9

; Copyright (C) 1989-1996 Computational Logic, Inc. (CLI).  All rights reserved.

; Use of this software constitutes agreement with the terms of the
; license agreement, found in the file LICENSE.

;; Init file for infix.lisp in Latex mode.
;; Feb 20 1992, by MKSmith
;; This file depends on the LaTeX .sty file, "CLI.sty".
;; CLI.sty should be stored in *infix-directory*.

(in-package "user")

(format *terminal-io* "Loading the ainfix latex-init file.")

;; Mode should actually be set before this file is loaded.

(infix-settings :mode                   "latex"
		:extension              "tex"
		:op-location            'front
		:comment-format         'smith
		:format-!-in-comments   nil
		:eliminate-top-parens   t
		:eliminate-inner-parens nil
		:no-index-calls         nil )

(defparameter *rightmost-char-number* 100)
(defparameter *default-chars-wide* 100)
(defparameter *latex-indent-number-limit* 14)

(defparameter nqread-normal-clause-enders
  (append '(#\\ #\{) nqread-default-normal-clause-enders))


;; THE LATEX PRELUDE.

(defparameter *standard-prelude*
  (format nil "\\documentstyle[makeidx,~aCLI]{article}~%~
   \\makeindex~%~
   %\\setlength{\\oddsidemargin}{.5in}~%~
   %\\setlength{\\evensidemargin}{.5in}~%~
   %\\setlength{\\textwidth}{5.8in}~%~
   \\begin{document}~%~
   %\\setlength{\\parindent}{0pt}~%~
   %\\newcounter{bean}~%~
   %\\begin{list}{\\arabic{bean}.}~
   {\\usecounter{bean}~
   \\setlength{\\leftmargin}{0pt}~
   \\setlength{\\rightmargin}{0pt}~
   \\setlength{\\listparindent}{20pt}~
   \\setlength{\\parsep}{5pt}}~
   ~%%\\item[]~%~%" *infix-directory*))

(defparameter *standard-postlude*
 "%\\end{list}
\\printindex
\\end{document}
")

(defparameter *example-prelude*
  "\\documentstyle{article} \\begin{document}

Here is a summary of the conventional syntax (~a) in terms of the official syntax
of the Nqthm logic.

\\begin{enumerate}
\\item Variables are printed in italics, unless specified otherwise in the table below.

\\item Function application.  For any function symbol for which special
syntax is not given below, an application of the symbol is printed with
the usual notation; e.g., the term !v(fn x y z) is
printed as !t(fn x y z).  Note that the function symbol is printed in
Roman.  In the special case that !qc is a function symbol of no
arguments, i.e., it is a constant, the term !v(c) is printed merely as
!t(c), in small caps, with no trailing parentheses.  Because variables are printed in
italics, there is no confusion between the printing of variables and
constants.

\\item Other constants.
Quoted constants are printed in the ordinary syntax of the Nqthm logic,
in a `typewriter font.'  For example,
{\\tt '(a b c)} is still printed just that way.  \\verb+#b001+ is printed
as !t#b001, \\verb+#o765+ is printed as !t#o765, and \\verb+#xa9+ is printed as
!t#xa9, representing binary, octal and hexadecimal, respectively.")

(defparameter *example-table-size*  40)

(defparameter *begin-example-table* "~%~%\\begin{tabular}{|c|c|}\\hline~%~
 Nqthm Syntax & Conventional Syntax \\\\ \\hline \\hline")

(defparameter *end-example-table* "  \\hline \\end{tabular}
")

(defparameter *example-postlude* "\\end{document}")

;; BASIC BRACKETS AND THEIR QUOTED VERSION.

(defparameter *begin* "{")
(defparameter *end*   "}")

(defparameter *lbrace* "\{")
(defparameter *rbrace* "\}")

;; NEWLINE PARAMETERS

(defparameter *newline-in-env* "\\\\")
(defparameter *newline-in-text* "")

(defparameter *force-newline-in-env* "\\\\")
(defparameter *force-newline-in-text* "\\hfill \\break ")

;; ENVIRONMENT BEGIN-END PAIRS

(defparameter *begin-index* "\\index{")
(defparameter *end-index* "}")

(defparameter *begin-text-env* "")
(defparameter *end-text-env*  "")

(defparameter *begin-verbatim-env* "\\begin{verbatim}")
(defparameter *end-verbatim-env* "\\end{verbatim}")

(defparameter *begin-format-env* "\\begin{CLIverbatim}\\begin{rm}")
(defparameter *end-format-env* "\\end{rm}\\end{CLIverbatim}")

;; Depends on CLI.sty
(defparameter *begin-emphasis-env*  "\\begin{CLIverbatim}\\begin{it}")
(defparameter *end-emphasis-env*    "\\end{it}\\end{CLIverbatim}")

(defparameter *begin-section-env*  "\\section{")
(defparameter *end-section-env*    "}")

(defparameter *begin-subsection-env*  "\\subsection{")
(defparameter *end-subsection-env*    "}")

(defparameter *begin-tt-env* "{\\tt{")
(defparameter *end-tt-env*   "}}")

(defparameter *begin-string-env*  "{\\tt{")
(defparameter *end-string-env*    "}}")

(defparameter *begin-bold-env* "{\\bf{")
(defparameter *end-bold-env*   "}}")

(defparameter *begin-italic-env* "{\\it{")
(defparameter *end-italic-env*   "\\/}}")

(defparameter *begin-sc-env* "{\\sc{")
(defparameter *end-sc-env*   "}}")

;; This won't work.

(defparameter *begin-comment-env*  "%")
(defparameter *end-comment-env*    "
")

(defparameter *begin-enumerate-env* "\\begin{enumerate}")
(defparameter *end-enumerate-env* "\\end{enumerate}")
(defparameter *begin-item* "\\item ")
(defparameter *end-item* "")

(defparameter *mv-bracket-left* "$\\langle$")
(defparameter *mv-bracket-right* "$\\rangle$")

(defparameter *forall* "$\\forall\\;$")
(defparameter *exists* "$\\exists\\;$")


;; TABBING AND INDENTING ENVIRONMENT AND TAB OPERATIONS

;; I don't know how to do this in Latex.
(defparameter *begin-group-tabbing-env* "\\begin{tabbing}
")
(defparameter *begin-tabbing-env* "\\begin{tabbing}
")
(defparameter *end-tabbing-env* "\\end{tabbing}
")
(defparameter *new-tab-row* " \\\\")

;; Just in case some other mode defined it otherwise.
(defun new-tab-row (&optional followed-by-infix-print-term)
  (declare (ignore followed-by-infix-print-term))
  (pprinc *new-tab-row*))

(defparameter *tab* "\\>")
(defparameter *flush* "\\`")

(defparameter *column-separator* "&")

(defparameter *tab-list* nil)

(defparameter *set-margin* "\\=\\+")
(defparameter *pop-margin* "\\-")
(defparameter *set-tab*    "\\=")

(defparameter *default-op-tab-space* "$\\quad$ ")
(defparameter *indent-string* "$\\quad$ ")
(defparameter *default-indent* 2)

(defun get-op-width-string (op)
  (declare (ignore op))
  nil)

(defparameter *noindent* "\\noindent ")

;; Not properly defined yet.
(defun begin-normal-text () (line-return))
(defun end-normal-text () (line-return))

(defvar *tab-stack* nil)

(defun begin-tabbing ()

; Tabbing environments cannot be nested in Latex.

  (if (null *tab-stack*)
      (princ *begin-tabbing-env*))
  (setq *tab-stack* (cons *tab-list* *tab-stack*))
  (setq *tab-list* nil)

  (if (> *left-margin* 0)
      (progn (sloop for i from 1 to *left-margin* do (pprinc "M"))
	     (pprinc "\\=\\+\\kill")
	     (pwrite-char #\Newline)))
  (setq *infix-loc* *left-margin*))

(defun begin-group-tabbing ()

  (if (null *tab-stack*)
      (princ *begin-group-tabbing-env*))
  (setq *tab-stack* (cons *tab-list* *tab-stack*))
  (setq *tab-list* nil)

  (if (> *left-margin* 0)
      (progn (sloop for i from 1 to *left-margin* do (pprinc "M"))
	     (pprinc "\\=\\+\\kill")
	     (pwrite-char #\Newline)))
  (setq *infix-loc* *left-margin*))

(defun end-tabbing ()
  (cond ((null *tab-stack*))
	((null (cdr *tab-stack*))
	 (setq *tab-list* (car *tab-stack*))
	 (setq *tab-stack* nil)
	 (princ *end-tabbing-env*))
	(t (setq *tab-list* (car *tab-stack*))
	   (setq *tab-stack* (cdr *tab-stack*)))))

;; (defun begin-tabbing ()
;;
;; ; Tabbing environments cannot be nested in Latex.
;;
;;   (setq *tab-list* nil)
;;   (princ *begin-tabbing-env*)
;;   (if (> *left-margin* 0)
;;       (progn (sloop for i from 1 to *left-margin* do (pprinc "M"))
;; 	     (pprinc "\\=\\+\\kill")
;; 	     (pwrite-char #\Newline)))
;;   (setq *infix-loc* *left-margin*))
;;
;; (defun begin-group-tabbing ()
;;   (setq *tab-list* nil)
;;   (princ *begin-group-tabbing-env*)
;;   (if (> *left-margin* 0)
;;       (progn (sloop for i from 1 to *left-margin* do (pprinc "M"))
;; 	     (pprinc "\\=\\+\\kill")
;; 	     (pwrite-char #\Newline)))
;;   (setq *infix-loc* *left-margin*))
;;
;; (defun end-tabbing ()
;;   (princ *end-tabbing-env*))

(defun increase-margin ()
  (pprin1i *default-op-tab-space*)
  (set-margin))

(defun set-margin ()

; Generate instructions to set the current indentation.
; In latex we use tabs, which cause *tabto* to tab to this column in the future.
; `Punt' if we hit the limit, by throwing all the way out.

  (cond (*do-not-use-tabs* nil)
        (t (cond ((= *tabs-in* *latex-indent-number-limit*)
                  (throw 'taboverflow t)))
           (setq *tabs-in* (1+ *tabs-in*))
	   (adjust-margin-to-last-tab-first *tab-list*)
	   (pprinc *set-margin*)
	   (push (cons 'lm *infix-loc*) *tab-list*))))

(defun adjust-margin-to-last-tab-first (tl)
  (cond ((null tl))
	((eq (caar tl) 'tab)
	 (pprinc "\\+")
	 (adjust-margin-to-last-tab-first (cdr tl)))
	(t nil)))

(defun get-margin ()
  (get-margin2 *tab-list*))

(defun get-margin2 (tl)
  (let ((setting (car tl)))
    (cond ((null setting) *left-margin*)
	  ((eq (car setting) 'lm) (cdr setting))
	  (t (get-margin2 (cdr tl))))))

(defun begin-flushright ()
  (pprinc *flush*))

(defun end-flushright () nil)

(defun flushright (form)
  (begin-flushright)
  (pprinc form)
  (end-flushright))

(defun do-tab ()
  (cond (*do-not-use-tabs* (pprinc " "))
	((and *tab-list* (eq (caar *tab-list*) 'tab))
	 (pprinc *tab*))
	(t (pprinc " "))))

(defun set-tab (&optional op)

; Generate instructions to set a tab at the current location.
; `Punt' if we hit the limit, by throwing all the way out.

  (cond (*do-not-use-tabs* nil)
        (t (cond ((= *tabs-in* *latex-indent-number-limit*)
                  (throw 'taboverflow t)))
           (setq *tabs-in* (1+ *tabs-in*))
	   (cond ((and op (get-op-width-string op))
		  (pprinc (get-op-width-string op)))
		 (t (pprinc *default-op-tab-space*)))
           (push (cons 'tab *infix-loc*) *tab-list*)
           (pprinc *set-tab*))))

(defun pop-tab ()
  ;; We don't really remove tabs from the formatted env.
  ;; Just track them in Lisp.
  ;; Generate command to `tab to one tab less in'.
  ;; Do not pop tabs beyond left margin.
  (cond (*do-not-use-tabs* nil)
	((and *tab-list* (eq (caar *tab-list*) 'tab))
	 (setq *tabs-in* (1- *tabs-in*))
	 ;; We don't tell TeX to remove the tab.  This works because
	 ;; before we try to use tabi again, we will reset its value.
	 (pop *tab-list*))
	(t nil)))

(defun pop-margin ()
  ;; Generate command to `return to one margin less in'.
  ;; If there are tabs after the margin, they are popped as well.
  ;; NOTE:  The way this must work in Latex is that if there
  ;; are tabs they are just ignored.  If there is an LM
  ;; we pop it as well as any \+ that were done to move over tabs
  ;; to it.
  (cond (*do-not-use-tabs* nil)
	((null *tab-list*) nil)
	((and (eq (caar *tab-list*) 'tab)
	      (eq (caadr *tab-list*) 'lm))
	 (pop-tab)
	 (pop *tab-list*)
	 (setq *tabs-in* (1- *tabs-in*))
	 (pprinc *pop-margin*)
	 (adjust-margin-to-first-tab-last *tab-list*))
	((and *tab-list* (eq (caar *tab-list*) 'lm))
	 (setq *tabs-in* (1- *tabs-in*))
	 (pop *tab-list*)
	 (pprinc *pop-margin*)
	 (adjust-margin-to-first-tab-last *tab-list*))
	(t nil)))

(defun adjust-margin-to-first-tab-last (tl)
  (cond ((null tl))
	((eq (caar tl) 'tab)
	 (pprinc "\\-")
	 (adjust-margin-to-first-tab-last (cdr tl)))
	(t nil)))

;; (defun to-current-margin ()
;;   ;; Generates command for return to current indentation setting,
;;   ;; unless we are already there.
;;   (cond (*do-not-use-tabs* (pprinci " "))
;; 	((eql *infix-loc* (get-margin)))
;; 	(t (pprinc *new-tab-row*)
;; 	   (setq *infix-loc* (get-margin)))))

;; (defun newline-to-current-margin ()
;;   ;; Generates command for return to current indentation setting.'
;;   (cond (*do-not-use-tabs* (pprinci " "))
;; 	(t (pprinc *new-tab-row*)
;; 	   (setq *infix-loc* (get-margin)))))

;; (defun force-newline ()
;;   ;; Forces a newline in running text OR in a tabbing env.
;;   (if (null *tab-list*)
;;       (progn (pprinci "\\hfill \\break ")
;; 	     (pwrite-char #\Newline)
;; 	     (cond (*do-not-use-tabs*)
;; 		   (t (setq *infix-loc* (get-margin)))))
;;       (progn (cond (*do-not-use-tabs* (pprinci " "))
;; 		   (t (pprinc *new-tab-row*)
;; 		      (setq *infix-loc* (get-margin)))))))

;; FONTS

(defparameter *function-font* "\\rm")

(defun roman-font (term)
  (pprinc "{")
  (pprinc *function-font*)
  (pprinc "{")
  (print-atom term)
  (pprinc "}}"))


;; MATH ENV AND OPERATORS

(defparameter *neg-str* (format nil "$~a$"  "\\neg"))

(defparameter *math-format* "$~a$")
(defparameter *math-begin* "$")
(defparameter *math-end* "$")

(defparameter *math-thick-space* "\\;")
(defparameter *math-thin-space* "\\,")

(defparameter *subscript* "_")

(defparameter *begin-subscript* "\\(_{")
(defparameter *end-subscript* "}\\)")

;; MISC

(defparameter *newpage* "\\newpage")

(defparameter *comma-atsign* ",@")
(defparameter *caret* "\\char'136")	;; It is a tad subtle getting a caret printed.
(defparameter *tilde* "\\char'176")	;; It is a tad subtle getting a tilde printed.

(defparameter *dotted-pair-separator* " .\\ ")           ; I don't understand the \\
(defparameter *dotted-pair-separator-newline* ".\\ ")    ; ditto

(defparameter *no-tab-event-trailer* "~%~%\\addvspace{10pt}")
(defparameter *print-default-event-header* "~%\\noindent{\\sc Event}:   ")
(defparameter *print-default-lisp-header* "~%\\noindent{\\sc Lisp}:   ")

(defparameter *print-default-command-header*  "~%\\noindent~%")
(defparameter *no-tab-command-trailer* "~%~%\\addvspace{10pt}")




;; OTHER FUNCTIONS

(defparameter doc-special-chars (coerce "#$%&~_^\\{}" 'list))
(defparameter doc-other-chars   (coerce "<>|" 'list))
(defparameter doc-index-specials (coerce "@|!\"" 'list))

;; We didn't compile the following because the compiler declaration
;; in Sinfix, through a bug in AKCL, caused this routine to produce
;; spurious results.

;; The patch to akcl that is loaded in sinfix should fix this problem.
;; Other lisps shouldn't need it.
;; These use to be of the form (eval-when (load) (eval '<defn>))

(defun handle-special-chars (char)
  ;; USED BY PRINT-ATOM.  CHAR is local to print-atom.
  (cond ((eql char #\^)
	 (pprinc "\\verb|^|"))
	((eql char #\~)
	 (pprinc *tilde*)
	 (incf *infix-loc* 1))
	((member char doc-special-chars)
	 (pwrite-char #\\)
	 (pwrite-char (cond ((eq *print-case* :downcase)
			     (char-downcase char))
			    (t char))))
	((member char doc-other-chars)
	 (pwrite-char #\$)
	 (pwrite-char (cond ((eq *print-case* :downcase)
			     (char-downcase char))
			    (t char)))
	 (pwrite-char #\$))
	(t (pwrite-char (cond ((eq *print-case* :downcase)
			       (char-downcase char))
			      (t char))))))

(defun handle-special-chars-in-string (char)
  ;; USED BY PRINT-ATOM.  CHAR is local to print-atom.
  (cond ((eql char #\~)
	 (pprinc *tilde*)
	 (incf *infix-loc* 1))
	((member char doc-special-chars)
	 (incf *infix-loc* 1)
	 (pwrite-char #\\)
	 (pwrite-char char))
	((member char doc-other-chars)
	 (incf *infix-loc* 2)
	 (pwrite-char #\$)
	 (pwrite-char char)
	 (pwrite-char #\$))
	(t (pwrite-char char))))


;; PRINTING INDEX ENTRIES

; Who could ever have guessed that it would take this much code to print out a
; simple \index{foo} command for an arbitrary Nqthm function symbol foo.  There
; are so many special cases one can hardly believe one's eyes.

(defparameter index-subitem-length 30)

(defun index (x &optional subkind)

#|
Yuk city on quotations of weird characters.

See the latex guide to indexes,
tex3.0/TeX3.0/LaTeX/LaTeXmakeindex/doc/makeindex.tex.  The characters vertical
bar, @, and ! are used within index strings, and need to be quoted with a
single double quote mark.

Also, it looks like makeindex chokes on index entries of more than 64
characters, in the sense that after 64, things suddenly become subitems, which
is a good way to get screwed if there are weird characters in the first 64 that
need quoting or balancing.

|#

  (pprinc *begin-index*)
  (let ((str (if (stringp x) x (symbol-name x)))
        (num-chars 0)
        (inserted-excl nil))

    (if subkind
	(cond ((stringp subkind) (setq str (concatenate 'string str ", " subkind)))
	      ((symbolp subkind) (setq str (concatenate 'string str ", " (string subkind))))
	      (t nil)))

    (sloop with brace-count = 0
             for i below (length str)
             for char = (char (the string str) (the fixnum i))
             until (> num-chars *index-entry-max*)
             do
             (progn
               (cond ((and (> num-chars index-subitem-length)
                           (not inserted-excl)
                           (= brace-count 0))

; There is some sort of a bug in the Latex indexing machinery whereby if an
; entry has more than 64 characters, a `subitem' is automatically started.  But
; this may happen in a bad place, in terms of character quotation, so we force
; a subitem earlier, at our convenience.

                      (pwrite-char #\!)
                      (setq inserted-excl t)))

; It is a tad subtle getting a caret or tilde printed.

	       (cond ((eql char #\^)
                      (pprinc *caret*)
                      (incf num-chars 8))

		     ((eql char #\~)
                      (pprinc *tilde*)
                      (incf num-chars 8))

; If braces are not balanced, the index machinery will barf, so we keep track
; and try to help out later, if we can.

                     ((eql char #\{)
                      (incf brace-count 1)
                      (pwrite-char #\\)	;!!! This won't work in Scribe.
                      (pwrite-char char)
                      (incf num-chars 2))
                     ((eql char #\})
                      (decf brace-count 1)
                      (pwrite-char #\\)
                      (pwrite-char char)
                      (incf num-chars 2))

; There are the special characters like @ which have a special meaning just in
; Latex indexing, and they have to be quoted their own special way.

                     ((member char doc-index-specials)
                      (pwrite-char #\")
                      (pwrite-char char)
                      (incf num-chars 2))

; And of course, one has to watch our for such standard special TeX characters
; as $.

                     ((member char doc-special-chars)
                      (pwrite-char #\\)
                      (pwrite-char char)
                      (incf num-chars 2))

; If one tries to set an ordinary < or >, it won't work, and just quoting with
; backslash doesn't work either, so we sneak into math mode.

                     ((member char doc-other-chars)
                      (pwrite-char #\$)
                      (pwrite-char char)
                      (pwrite-char #\$)
                      (incf num-chars 3))
                     (t (pwrite-char (cond ((eq *print-case* :downcase)
                                            (char-downcase char))
                                           (t char)))
                        (incf num-chars 1)))
               (cond ((< brace-count 0)
                      (pformat *terminal-io*
                               "~% Error: The index entry for ~a will ~
                                fail because of the imbalance of set ~
                                braces.~%"
                               x))))
             finally
             (progn
                (cond ((> num-chars *index-entry-max*)
                       (pformat *terminal-io*
                                "~% Warning: Index entry for ~a truncated to ~a characters. ~%"
                                 x num-chars)
                       (pprinc "...")))
                (cond ((not (equal brace-count 0))
                       (cond ((> brace-count 0)
                              (sloop for i from 1 to brace-count do
                                       (pprinc "\\}"))))
                       (pformat *terminal-io*
                                "~%Warning:  Balancing set braces on ~
                                 ~a so Latex indexing will work.~%"
                                x))))))
  (pprinc *end*))

(defun skip-index-entries ()
  ;; We are looking at a backslash.  If this begins an index entry, in Tex
  ;; mode we need to skip to the end of the entry, because we may have added !'s.
  ;; In Scribe mode this function returns NIL.
  (let ((pos (file-position *standard-input*))
	(index '(#\i #\n #\d #\e #\x #\{))
	success
	c)
      (sloop for x on index
	       while (and x (char= (setq c (read-char *standard-input* nil a-very-rare-cons)) (car x)))
	       finally (cond ((null x)
			      (pprinc "\\index{")
			      (skip-to-brace)
			      (setq success t))))
      (cond ((not success)
	     ;; Back to read the char immediately following the #\.
	     (file-position *standard-input* pos)
	     nil)
	    (t t))))

(defun adjust-tabbing-env ()
  ;; We are looking at a backslash. In Tex mode we want to replace
  ;;   ....  \\
  ;;   \end{tabbing}
  ;; with
  ;;   ....
  ;;   \end{tabbing}
  ;; Worse and worse.  There is more than one such pattern.
  (let ((pos (file-position *standard-input*))
	(patterns '((#\\ #\newline #\\ #\- #\\ #\e #\n #\d #\{ #\t #\a #\b #\b #\i #\n #\g #\})
		   (#\\ #\newline #\\ #\e #\n #\d #\{ #\t #\a #\b #\b #\i #\n #\g #\})))
	success
	c)
    (sloop for pattern in patterns
	   while (not success)
	   do (progn
		(sloop for x on pattern
		       while (char= (setq c (read-char *standard-input* nil a-very-rare-cons)) (car x))
		       finally (cond ((null x)
				      (line-return)
				      (pprinc "\\end{tabbing}")
				      (setq success t))))
		(if (not success)
		    ;; Back to read the char immediately following the #\.
		    (file-position *standard-input* pos))))
    success))

(defun skip-to-brace ()
  ;; Skip to next non-quoted #\}.
  ;; We assume one exists.
  (sloop for c = (read-char *standard-input* nil a-very-rare-cons)
	   until (char= c #\})
	   do    (cond ((char= c #\\)
			;; Handle imbedded, quoted right braces.
			(pwrite-char c)
			(pwrite-char (read-char *standard-input* nil a-very-rare-cons)))
		       (t (pwrite-char c))))
  (pwrite-char #\}))

(defparameter acl2-char-subst-table
 '((#\~ #\\ #\c #\h #\a #\r #\' #\1 #\7 #\6 #\ )
   (#\^ #\\ #\c #\h #\a #\r #\' #\1 #\3 #\6 #\ )
   (#\# #\\ #\#)
   (#\& #\\ #\&)
   (#\$ #\\ #\$)
   (#\% #\\ #\%)
   (#\_ #\\ #\_)
   (#\\ #\\ #\\)
   (#\{ #\\ #\{)
   (#\} #\\ #\})
   (#\< #\$ #\< #\$)
   (#\> #\$ #\> #\$)
   (#\| #\$ #\| #\$)))


(defparameter acl2-markup-table
  '(("-"   . "---")
    ("B"   . "{\\bf ~sa}")
    ("BF"  . "~%\\begin{CLIverbatim}\\begin{rm}")
    ("BID" . "")		     ;begin implementation dependent
    ("BQ"  . "~%\\begin{quotation}")
    ("BV"  . "~%\\begin{verbatim}")
    ("C"   . "{\\tt ~sa}")	     ;originally @code, but we don't want `' in info file
    ("EF"  . "\\end{rm}\\end{CLIverbatim}~%")
    ("EID" . "")		     ;end implementation dependent
    ("EM"  . "{\\it ~sa}")           ;emphasis
    ("EQ"  . "~%\\end{quotation}~%") ;TexInfo needs leading line break to
				     ;avoid problems with @refill
    ("EV"  . "\\end{verbatim}~%")
    ("I"   . "{\\it ~sa}")
    ("ID"  . "~sa")		     ;implementation dependent
    ("IL"  . "~sa")
    ("ILC" . "{\\tt ~sa}")	     ;originally @code, but problem with info file
    ("L"   . "See ~sA")
    ("NL"  . "\\hfill \\break ")
    ("PAR" . "")		     ;paragraph mark, of no significance for latex
    ("PL"  . "see ~sA")		     ;used for parenthetical crossrefs
    ("SC"  . "{\\sc ~sa}")	     ;small caps
    ("ST"  . "{\\bf ~sa}")	     ;strong emphasis
    ("T"   . "{\\tt ~sa}")
    ("TERMINAL" . "")		     ; terminal only, ignore
    ))

