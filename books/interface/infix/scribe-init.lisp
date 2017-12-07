; ACL2 Version 1.9

; Copyright (C) 1989-1996 Computational Logic, Inc. (CLI).  All rights reserved.

; Use of this software constitutes agreement with the terms of the
; license agreement, found in the file LICENSE.


;; Init file for infix.lisp in Scribe mode.
;; Feb 20 1992, by MKSmith

;; In order to fix a bug in the AKCL interpreter's use of proclaim.
;; we depend on this file being compiled and loaded in an environment
;; in which infix.lisp has already been loaded.
;; #+akcl (load-base "akcl-patch.lisp")

(in-package "user")

(format *terminal-io* "Loading the ainfix scribe-init file.")



;; Mode should actually be set before this file is loaded.

(infix-settings :mode                   "scribe"
		:extension              "mss"
		:op-location            'front
		:comment-format         'smith
		:format-!-in-comments   nil
		:eliminate-top-parens   t
		:eliminate-inner-parens nil
		:no-index-calls         nil )


;; Increase this number to more accurately allow for proper output width.
(defparameter *rightmost-char-number* 100)
(defparameter *default-chars-wide* 100)
(defparameter *latex-indent-number-limit* 100)

(defparameter nqread-normal-clause-enders
  (append '(#\@) nqread-default-normal-clause-enders))

; THE SCRIBE PRELUDE.

(defparameter *standard-prelude*
  "@make(clinote)
@device(postscript)
@style(leftmargin 1.5 inch,linewidth 5.5 inch, indent 0,
       font clitimesroman, indexcase folded)

@enable(index)

@libraryfile(clisymbols)
@libraryfile(stable)

@comment{Kcrlf is used in @index[] to cause the form to ignore}
@comment{newlines after the indexing command.  Not what we want in the}
@comment{forms below.}

@Form(Kcrlf={})

@Modify(format,above 1.2lines,below 1.2 lines)
@define(st, use t, size -2)

@Define(block,Break Off,Nofill,Spaces Kept,BlankLines kept,Justification off,afterentry {@$})
@define(nop)

@pageheading(immediate,center={})
@pagefooting(immediate,center={@value(page)})

")

(defparameter *standard-postlude*
 "
")

(defparameter *example-prelude*
  (concatenate 'string *standard-prelude*
"
@standardtable(name BaseTbl, Columns 2, columnwidth 2.5 inch, allcolumns=center,
               float,  boxed, flushtop,
               above 1 line, below 1 line)

Here is a summary of the conventional syntax (~a) in terms of the official syntax
of the Acl2 logic.

@begin{enumerate}

Variables.  !tx, !ty, !tz, etc. are printed in italics.

Function application.  For any function symbol for which special
syntax is not given below, an application of the symbol is printed with
the usual notation; e.g., the term !v(fn x y z) is
printed as !t(fn x y z).  Note that the function symbol is printed in
Roman.  In the special case that !qc is a function symbol of no
arguments, i.e., it is a constant, the term !v(c) is printed merely as
!t(c), in small caps, with no trailing parentheses.  Because variables are printed in
italics, there is no confusion between the printing of variables and
constants.

Other constants.  !tt, !tf, and !tnil are printed in bold.
Quoted constants are printed in the ordinary syntax of the ACL2 logic,
in a `typewriter font.'  For example,
@t{'(a b c)} is still printed just that way.  @t{#b001} is printed
as !t#b001, @t{#o765} is printed as !t#o765, and @t{#xa9} is printed as
!t#xa9, representing binary, octal and hexadecimal, respectively.

"))

(defparameter *begin-example-table* "
@newpage()
@begin(BaseTbl)
@tableid(BaseTbl~d)
@tableHeading(Immediate, RowFormat BaseTblColumnHeadings,
              Line {ACL2 Syntax@\\Conventional Syntax})~%"
  "Needs an argument, integer, in order to give different tables different names.")

(defparameter *end-example-table* "@end(BaseTbl)

")

(defparameter *example-table-size*  32)

(defparameter *example-postlude* "")

;; BASIC BRACKETS AND THEIR QUOTED VERSION.

(defparameter *begin* "{")
(defparameter *end*   "}")

(defparameter *lbrace* "@nop<{>")
(defparameter *rbrace* "@nop<}>")

;; NEWLINE PARAMETERS

(defparameter *newline-in-env* "")
(defparameter *newline-in-text* "")

(defparameter *force-newline-in-env* "")
(defparameter *force-newline-in-text* "@*")


;; ENVIRONMENT BEGIN-END PAIRS

(defparameter *begin-index* "@index{")
(defparameter *end-index* "@index{")

(defparameter *begin-text-env* "@begin{text,above 1 line,below 1 line}")
(defparameter *end-text-env*  "@end{text}")

(defparameter *begin-verbatim-env* "@begin{verbatim}")
(defparameter *end-verbatim-env*  "@end{verbatim}")

(defparameter *begin-format-env*  "@begin{format}")
(defparameter *end-format-env*    "@end{format}")

(defparameter *begin-emphasis-env*  "@begin{format, FaceCode i}")
(defparameter *end-emphasis-env*    "@end{format}")

(defparameter *begin-comment-env*  "@begin{comment}")
(defparameter *end-comment-env*    "@end{comment}")

(defparameter *begin-section-env*  "@section{")
(defparameter *end-section-env*    "}")

(defparameter *begin-subsection-env*  "@subsection{")
(defparameter *end-subsection-env*    "}")

(defparameter *begin-tt-env* "@t{")
(defparameter *end-tt-env*   "}")

(defparameter *begin-string-env* "@st{")
(defparameter *end-string-env*   "}")

(defparameter *begin-bold-env* "@b{")
(defparameter *end-bold-env*   "}")

(defparameter *begin-italic-env* "@i{")
(defparameter *end-italic-env*   "}")

(defparameter *begin-sc-env* "@c{")
(defparameter *end-sc-env*   "}")

(defparameter *begin-enumerate-env* "@begin{enumerate}")
(defparameter *end-enumerate-env* "@end{enumerate}")
(defparameter *begin-item* "
@begin(multiple)
")
(defparameter *end-item* "
@end(multiple)
")

(defparameter *mv-bracket-left* "@langle")
(defparameter *mv-bracket-right* "@rangle")

(defparameter *forall* "@forall ")
(defparameter *exists* "@exists ")


;; TABBING ENVIRONMENT AND TAB OPERATIONS

(defparameter *begin-group-tabbing-env* "@begin{format,group}@tabclear{}")

(defparameter *begin-tabbing-env* "@begin{format}@tabclear{}")
(defparameter *end-tabbing-env* "@end{format}")

(defun new-tab-row (&optional followed-by-infix-print-term)
  (declare (ignore followed-by-infix-print-term))
  (pwrite-char #\Newline))

(defparameter *tab* "@\\")
(defparameter *flush* "@>")

(defparameter *column-separator* *tab*)

(defparameter *tab-list* nil)

(defparameter *set-margin* "@begin(block)")
(defparameter *set-tab*    "@^")
(defparameter *pop-margin* "@end(block)")

(defparameter *default-op-tab-space* "@math{@quad}@ @ @ ")
(defparameter *indent-string* "@math{@quad}")
(defparameter *default-indent* 4)

(defun get-op-width-string (op)
  (declare (ignore op))
  nil)

(defparameter *noindent* "")

; (defparameter *testmargin* nil)

(defun begin-tabbing ()

; Tabbing environments can be nested in Scribe.
; Use this fact with set-margin.

  (setq *tab-list* (cons '(begin-tabs) *tab-list*))
  ;; (if *testmargin* (format t "~%Begin tabbing : ~a~%" *tab-list*))
  (princ *begin-tabbing-env*)
  (setq *infix-loc* *left-margin*))

(defun begin-group-tabbing ()

; Tabbing environments can be nested in Scribe.
; Use this fact with set-margin.

  (setq *tab-list* nil)
  (princ *begin-group-tabbing-env*)
  (setq *infix-loc* *left-margin*))

(defun end-tabbing ()
  (sloop while (and *tab-list* (not (equal (caar *tab-list*) 'begin-tabs)))
	 do (setq *tab-list* (cdr *tab-list*)))
  (if *tab-list* (setq *tab-list* (cdr *tab-list*)))
  ;; (if *testmargin* (format t "~%End tabbing : ~a~%" *tab-list*))
  (princ *end-tabbing-env*))

(defun increase-margin ()
  (pprin1i *default-op-tab-space*)
  (set-margin))

(defun set-margin ()

; Generate instructions to set the current indentation.
; In latex we use tabs, which cause *tabto* to tab to this column in the future.
; `Punt' if we hit the limit, by throwing all the way out.

  (cond (*do-not-use-tabs* nil)
	;; Bump Latex limit way up for Scribe.
        (t (cond ((= *tabs-in* *latex-indent-number-limit*)
                  (throw 'taboverflow t)))
           (setq *tabs-in* (1+ *tabs-in*))
	   (pprinc *set-margin*)
	   (push (cons 'lm *infix-loc*) *tab-list*)
	   ;; (if *testmargin* (format t "~%Set margin : ~a~%" *tab-list*))
	   )))

(defun get-margin ()
  (get-margin2 *tab-list*))

(defun get-margin2 (tl)
  (let ((setting (car tl)))
    (cond ((null setting) *left-margin*)
	  ((eq (car setting) 'lm) (cdr setting))
	  (t (get-margin2 (cdr tl))))))

(defun begin-flushright ()
  (pprinc *flush*))

(defun end-flushright ()
  (pprinc *tab*))

(defun begin-normal-text ()
  (pprinc *begin-text-env*))

(defun end-normal-text ()
  (pprinc *end-text-env*))

(defun flushright (form)
  (begin-flushright)
  (pprinc form)
  (end-flushright))

(defun do-tab ()

; The *tab-list* is either NIL, ((LM loc) ...), or ((TAB loc) ...)
; Only tab if there is something to tab to.

  (cond (*do-not-use-tabs* (pprinc " "))
	((and *tab-list* (eq (caar *tab-list*) 'tab))
	 (pprinc *tab*))
	(t (pprinc " "))))

(defun set-tab (&optional op)

; Generate instructions to set a tab at the current location.
; `Punt' if we hit the limit, by throwing all the way out.

  (cond (*do-not-use-tabs* nil)
        (t (cond ((= *tabs-in* *latex-indent-number-limit*) ;Let Latex-Limit hold for Scribe also.
                  (throw 'taboverflow t)))
           (setq *tabs-in* (1+ *tabs-in*))
	   (cond ((and op (get-op-width-string op))
		  (pprinc (get-op-width-string op)))
		 (t (pprinc *default-op-tab-space*)))
           (push (cons 'tab *infix-loc*) *tab-list*)
	   ;; (if *testmargin* (format t "~%Setting tab : ~a~%" *tab-list*))
           (pprinc *set-tab*))))

(defun pop-tab ()
  ;; We don't really remove tabs from the formatted env.
  ;; Just track them in Lisp.
  ;; Generate command to `tab to one tab less in'.
  ;; Do not pop tabs beyond left margin or past the beginning of a tabbing env.
  (cond (*do-not-use-tabs* nil)
	((and *tab-list* (eq (caar *tab-list*) 'tab))
	 (setq *tabs-in* (1- *tabs-in*))
	 (pop *tab-list*)
	 ;; (if *testmargin* (format t "~%Popped tab : ~a~%" *tab-list*))
	 )
	(t nil)))

(defun pop-margin ()
  ;; Generate command to `return to one margin less in'.
  ;; For bookkeepping reasons we pop tabs after the margin.
  ;; (if *testmargin* (format t "~%Popping margin ...~%"))
  (cond (*do-not-use-tabs* nil)
	((and *tab-list* (eq (caar *tab-list*) 'tab))
	 (pop-tab)
	 (pop-margin))
	((and *tab-list* (eq (caar *tab-list*) 'lm))
	 (setq *tabs-in* (1- *tabs-in*))
	 (pop *tab-list*)
	 ;; (if *testmargin* (format t "~%Popped margin : ~a~%" *tab-list*))
	 (pprinc *pop-margin*))
	(t nil)))

;; (defun newline-to-current-margin ()
;;   ;; Generates command for return to current indentation setting.
;;   (cond (*do-not-use-tabs* (pprinci " "))
;; 	(t (pwrite-char #\Newline)
;; 	   (setq *infix-loc* (get-margin)))))

(defun to-current-margin ()
  ;; Generates command for return to current indentation setting,
  ;; unless we are already there.
  (cond (*do-not-use-tabs* (pprinci " "))
	((eql *infix-loc* (get-margin)))
	(t (newline))))

;; (defun force-newline ()
;;   ;; Forces a newline in running text.
;;   (pprinc "@*")
;;   (pwrite-char #\Newline)
;;   (cond (*do-not-use-tabs*
;; 	   (setq *infix-loc* *left-margin*))
;; 	(t (setq *infix-loc* (get-margin)))))

;; (defun force-newline ()
;;   ;; Forces a newline in running text OR in tabbing env.
;;   (if (null *tab-list*)
;;       (progn (pprinc "@*")
;; 	     (pwrite-char #\Newline)
;; 	     (cond (*do-not-use-tabs*
;; 		    (setq *infix-loc* *left-margin*))
;; 		   (t (setq *infix-loc* (get-margin)))))
;;       (cond (*do-not-use-tabs* (pprinci " "))
;; 	    (t (pwrite-char #\Newline)
;; 	       (setq *infix-loc* (get-margin))))))

(defun set-left-margin ()
  (cond ((< *infix-loc* *left-margin*)
	 (sloop for i from *infix-loc* to (- *left-margin* 1)
		  do (pwrite-char #\Space))
	 (pprinc "@$"))))


;; FONTS

(defparameter *function-font* "@r")	; Roman.  sc = small caps

(defun roman-font (term)
  (pprinc *function-font*)
  (pprinc "{")
  (print-atom term)
  (pprinc "}"))


;; MATH ENV AND OPERATORS

(defparameter *neg-str*  "@not")

(defparameter *math-format* "@math{~a}")
(defparameter *math-begin* "@math{")
(defparameter *math-end* "}")

;; These must be enclosed in a math env.  Tried using a @quad, but it is too thick.
(defparameter *math-thick-space* "@ ")
(defparameter *math-space* "##")         ; # is a thin space
(defparameter *math-thin-space* "#")

(defparameter *subscript* "@-")

(defparameter *begin-subscript* "@-{")
(defparameter *end-subscript* "}")

;; MISC.

(defparameter *newpage* "@newpage()")

(defparameter *comma-atsign* ",@@")
(defparameter *caret* "^")

(defparameter *dotted-pair-separator* " . ")
(defparameter *dotted-pair-separator-newline* ". ")

(defparameter *no-tab-event-trailer* "~%~%")
(defparameter *print-default-event-header* "~%@c{Event}:   ")
(defparameter *print-default-lisp-header* "~%@c{Lisp}:   ")

(defparameter *print-default-command-header*  "~%")
(defparameter *no-tab-command-trailer* "~%~%")

;; OTHER FUNCTIONS

;; Should both be `(#\@ @\}) but we handle them individually in the appropriate
;; spots in the two following functions.
(defparameter doc-special-chars nil)
(defparameter doc-index-specials nil)

(defparameter doc-other-chars   nil)

;; We didn't compile the following because the compiler declaration
;; in Sinfix, through a bug in AKCL, caused this routine to produce
;; spurious results.

;; The patch to akcl that is loaded in sinfix should fix this problem.
;; Other lisps shouldn't need it.
;; These use to be of the form (eval-when (load) (eval '<defn>))

(eval-when (load) (eval
'(defun handle-special-chars (char)
  ;; USED BY PRINT-ATOM.  CHAR is local to print-atom.
  ;; We don't use the global, DOC-SPECIAL-CHARS, since there are
  ;; only two, @ and }, and we do something different in each case.
  (cond ((char= char #\@) (pprinc "@@") (incf *infix-loc* 1))
	((char= char #\}) (pprinc *rbrace*) (incf *infix-loc* 1))

	;; Atoms printed in all lower case.

	(t (pwrite-char (if (eq *print-case* :downcase)
			    (char-downcase char)
			    char)))))
))

(eval-when (load) (eval
'(defun handle-special-chars-in-string (char)
  ;; USED BY PRINT-ATOM.  CHAR is local to print-atom.
  (cond ((char= char #\@) (pprinc "@@")	 (incf *infix-loc* 1))
	((char= char #\}) (pprinc *rbrace*) (incf *infix-loc* 1))
	(t (pwrite-char char))))
))

;; PRINTING INDEX ENTRIES

;; We don't bother to count braces in Scribe, we just quote them.

(defun index (x &optional subkind)
  (pprinc *begin-index*)
  (let ((str (if (stringp x) x (symbol-name x)))
        (num-chars 0)
        ;(inserted-excl nil)
	)

    (if subkind
	(cond ((stringp subkind) (setq str (concatenate 'string str ", " subkind)))
	      ((symbolp subkind) (setq str (concatenate 'string str ", " (string subkind))))
	      (t nil)))

    (sloop for i below (length str)
             for char = (char (the string str) (the fixnum i))
             until (> num-chars *index-entry-max*)

	     ;; Quote special Scribe characters as @ & }.

             do (cond ((char= char #\@) (pprinc "@@") (incf num-chars 2))
		      ((char= char #\}) (pprinc *rbrace*) (incf num-chars 2))

		      (t (pwrite-char (if (eq *print-case* :downcase)
					  (char-downcase char)
					  char))
			 (incf num-chars 1)))
             finally (cond ((> num-chars *index-entry-max*)
			    (pformat *terminal-io*
				     "~% Warning: Index entry for ~a truncated to ~a characters. ~%"
				     x num-chars)
			    (pprinc "...")))
	     ))
  (pprinc *end*))

(defun skip-index-entries ()
  ;; We are looking at a backslash. In Tex mode we need to skip to the end
  ;; of the entry, because we may add !'s.  In Scribe mode this is just NIL.
  nil)

(defun adjust-tabbing-env ()
  ;; We are looking at a backslash. In Tex mode we may need to check for
  ;; some special cases.
  ;; In Scribe mode this is just NIL.
  nil)

(defparameter acl2-char-subst-table
 '((#\@ #\@ #\@)))

(defparameter acl2-markup-table
  '(("-"   .   "@emdash{}")
    ("B"   .   "@b{~sa}")
    ("BF"  .   "~%@begin{format}")
    ("BID" .   "")		      ;begin implementation dependent
    ("BQ"  .   "~%@begin{quotation}")
    ("BV"  .   "~%@begin{verbatim}")
    ("C"   .   "@t{~sa}")	      ;originally @code, but we don't want `' in info file
    ("EF"  .   "@end{format}~%")
    ("EID" .   "")		      ;end implementation dependent
    ("EM"  .   "@i{~sa}")	      ;emphasis
    ("EQ"  .   "~%@end{quotation}~%") ;TexInfo needs leading line break to
				      ;avoid problems with @refill
    ("EV"  .   "@end{verbatim}~%")
    ("I"   .   "@i{~sa}")
    ("ID"  .   "~sa")		      ;implementation dependent
    ("IL"  .   "~sa")
    ("ILC" .  "@t{~sa}")	      ;originally @code, but we don't want `' in info file
    ("L"   .  "See ~sA")
    ("NL"  .  "@*~%")
    ("PAR" .  "")		      ;paragraph mark, of no significance for scribe
    ("PL"  .  "see ~sA")	      ;used for parenthetical crossrefs
    ("SC"  .  "@c{~sa}")	      ;small caps
    ("ST"  .  "@b{~sa}")	      ;strong emphasis
    ("T"   .  "@t{~sa}")
    ("TERMINAL" . "")		      ; terminal only, ignore
    ))


