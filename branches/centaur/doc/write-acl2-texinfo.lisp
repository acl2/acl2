; ACL2 Version 6.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 was produced by modifying ACL2 Version 1.9, Copyright
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


; Texinfo driver for ACL2 documentation.  Sample usage:
; (write-texinfo-file "acl2-doc") or even
; (write-texinfo-file)

; Art Flatau and Matt Kaufmann.

; This file defines the macro write-texinfo-file, which writes a texinfo file.
; It takes all the documentation strings that are available via the ACL2 :DOC
; command and creates the texinfo file.  An earlier version written by Art
; Flatau created an info file directly.

; A subtelty:  How do are links printed in info?  That is, how is @xref{foo}
; interpreted in the info setting?  It is literally printed as "*Note foo::"
; in the info files, BUT in Lucid emacs there is a variable, Info-footnote-tag,
; that allows "Note" to be replaced by another string.  By default,
; Info-footnote-tag is "See".  HOWEVER, emacs 19 does not seem to have this
; capability.  Now in the printed version a "See" is introduced; therefore, we
; would like to have "See" in the info version.  We do *not* want to use the
; present facility to print "See", because then the printed version will say
; "See See"!  So, we will simply print out the @xref, and let texinfo turn that
; into *Note, and assume that either the user uses Lucid emacs (which changes
; *Note to *See) or uses emacs 19 (and the human reads "*Note" as "See" or
; "see" in the text).  It is easy enough to use tags-query-replace to create a
; version of the info files that replaces "*Note" by "See *Note"; this in fact
; gives a pretty good emacs 19 solution.

; One other subtlety:  This code assumes that when references to topics
; containing the special characters @, {, and } are used in ~l[..], then there
; is a comma or period after the right brace.  There should also _not_ be such
; a punctuation mark after ~pl, but it's probably rather harmless to have it
; (the result probably being one extra punctuation mark).  In fact the
; documenation for texinfo makes such punctuation requirements absolute, but
; when the referenced topic does not contain special characters, we seem to be
; able to relax that restriction completely.

(in-package "ACL2-USER")

;; We need to be in :program mode, as we have not tried to reason
;; about functions in this file.

(acl2::set-state-ok t)
(acl2::program)

; We want to link in the dpANS documentation to the info documentation.

(defconst *gcl-info-top* "/cli/project/gcl/info/gcl.info")

;; First some macros so we don't have to have acl2:: all over the place.

; (defmacro true-listp (x)
;   `(acl2::true-listp ,x))

; (defmacro pprogn (&rest lst) (cons 'acl2::pprogn lst))

; (defmacro princ$ (x channel state-state)
;   `(acl2::princ$ ,x ,channel ,state-state))

; (defmacro newline (channel state-state)
;   `(acl2::newline ,channel ,state-state))

; (defmacro strip-cars (x) `(acl2::strip-cars ,x))

; (defmacro assoc-equal (x alist) `(acl2::assoc-equal ,x ,alist))

; Now for some additional utilities.

(defconst *texinfo-doc-char-subst-table*
  '((#\@ #\@ #\@)
    (#\{ #\@ #\{)
    (#\} #\@ #\}))
  "Table for substituting characters for texinfo.")

; Replace `|' by `:' to get a version of this that creates truly nice tex
; output.

(defun texinfo-string-node-name (pkg-name name tex-only-flg)

; Node names in texinfo had better not contain #\@.  So, we do not use
; acl2::apply-char-subst-table here.  If we need to escape some characters,
; we'll do that elsewhere, e.g. in printing menus and sections.

  (cond
   ((equal pkg-name "KEYWORD")
    (if tex-only-flg
        (concatenate 'string "{\tt\char'72}" name)
      (concatenate 'string ":" name)))
   (pkg-name
    (concatenate 'string pkg-name "||" name))
   (t name)))

(defun upcase-substring1 (str lower weak-upper ans)

; Returns substring of str between lower and weak-upper, inclusive, for ans=nil.

  (cond
   ((< weak-upper lower)
    (coerce ans 'string))
   (t (upcase-substring1 str lower (1- weak-upper)
                         (cons (char-upcase (char str weak-upper)) ans)))))

(defun upcase-substring (str lower upper)
  (upcase-substring1 str lower (1- upper) nil))

(defun texinfo-parse-string (x)
  (let* ((len (length x))
         (posn (acl2::posn-char-stringp #\: x (1- (length x)))))
    (cond
     ((null posn) (mv nil x))
     ((= posn 0)
      (mv "KEYWORD" (upcase-substring x 1 len)))
     (t (mv (upcase-substring x 0
                              (if (eql (char x (1- posn)) #\:)
                                  (1- posn)
                                posn))
            (upcase-substring x
                              (+ 1 posn)
                              len))))))

(defun texinfo-node-name (x spack tex-only-flg)
  (cond
   ((stringp x)
    (if (equal x "Top")
        x
      (mv-let (pkg n)
              (texinfo-parse-string x)
              (cond
               ((or (not (equal (acl2::symbol-package-name spack) pkg))
                    (equal pkg "KEYWORD"))
                (texinfo-string-node-name pkg n tex-only-flg))
               (t (texinfo-string-node-name nil n tex-only-flg))))))
   ((symbolp x)
    (let ((name (symbol-name x))
          (pkg-name (acl2::symbol-package-name x)))
      (cond
       ((or (equal pkg-name "KEYWORD")
            (not (eq (acl2::intern-in-package-of-symbol name spack)
                     x)))
        (texinfo-string-node-name pkg-name name tex-only-flg))
       (t (texinfo-string-node-name nil name tex-only-flg)))))
   (t (acl2::er acl2::hard 'texinfo-node-name
                "Apparent attempt to document topic that is neither a string ~
                 nor a symbol, ~p0"
                x))))

(defun texinfo-node-name-lst (lst spack tex-only-flg)
  (if lst
      (cons (texinfo-node-name (car lst) spack tex-only-flg)
            (texinfo-node-name-lst (cdr lst) spack tex-only-flg))
    nil))

(defun doc-alist1 (raw-doc-alist spack tex-only-flg ans)
  (cond
   ((null raw-doc-alist) (reverse ans))
   (t (doc-alist1 (cdr raw-doc-alist)
                  spack
                  tex-only-flg
                  (cons (list* (texinfo-node-name (caar raw-doc-alist)
                                                  spack
                                                  tex-only-flg)
                               (texinfo-node-name (cadar raw-doc-alist)
                                                  spack
                                                  tex-only-flg)
                               (texinfo-node-name-lst (caddar raw-doc-alist)
                                                      spack
                                                      tex-only-flg)
                               (cdddar raw-doc-alist))
                        ans)))))

(defun filter-topics1 (topics doc-alist acc)

; At one time we exploited the "fact" that if every topic's section appears
; earlier in doc-alist than it does, in order to guarantee that we include the
; entire cone underneath a topic.  But this "fact" isn't true, e.g., for
; arrays and aref1.

  (cond
   ((null doc-alist)
    (reverse acc))
   ((acl2::member-equal (cadar doc-alist) topics)
    ;; then, section exists
    (filter-topics1 topics (cdr doc-alist) (cons (car doc-alist) acc)))
   ((acl2::member-equal (caar doc-alist) topics)
    ;; otherwise, the current topic should be viewed as a section
    (filter-topics1 topics
                    (cdr doc-alist)
                    (cons (list* (caar doc-alist)
                                 (caar doc-alist)
                                 (cddar doc-alist))
                          acc)))
   (t (filter-topics1 topics (cdr doc-alist) acc))))

(defun extend-with-immediate-subtopics (topics doc-alist)
  (cond
   ((null doc-alist) topics)
   ((acl2::member-equal (caar doc-alist) topics)
    (extend-with-immediate-subtopics topics (cdr doc-alist)))
   ((acl2::member-equal (cadar doc-alist) topics)
    (extend-with-immediate-subtopics (cons (caar doc-alist) topics)
                                     (cdr doc-alist)))
   (t (extend-with-immediate-subtopics topics (cdr doc-alist)))))

(defun all-subtopics (topics doc-alist)
  (let ((extended-topics (extend-with-immediate-subtopics topics doc-alist)))
    (if (equal extended-topics topics)
        topics
      (all-subtopics extended-topics doc-alist))))

(defun filter-topics (topics doc-alist)
  (if (null topics)
      doc-alist
    (filter-topics1 (all-subtopics topics doc-alist) doc-alist nil)))

(defun doc-alist (spack tex-only-flg topics state)
   (doc-alist1 (filter-topics
                topics
                (acl2::global-val 'acl2::documentation-alist (acl2::w state)))
               spack
               tex-only-flg
               nil))

(defconst *top-node*
  '("Top" nil nil ""))

; First we print a prelude in the file, then we go down the list of documented
; symbols (a la what :docs ** does) and print the documentation (similar to
; what PRINT-DOC does).

(defconst *prelude-string*
  "\\input texinfo    @c -*-texinfo-*-
@comment %**start of header (This is for running Texinfo on a region.)

@setfilename ~sf
@settitle ~sv
@paragraphindent 0
@comment %**end of header (This is for running Texinfo on a region.)

@iftex
@finalout
@parindent 0mm
@end iftex

@ifinfo
This is documentation for ~sv@*
Copyright @copyright{} 2013  University of Texas at Austin

This program is free software; you can redistribute it and/or modify@*
it under the terms of Version 2 of the GNU General Public License as@*
published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,@*
but WITHOUT ANY WARRANTY; without even the implied warranty of@*
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the@*
GNU General Public License for more details.

You should have received a copy of the GNU General Public License@*
along with this program; if not, write to the Free Software@*
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

Written by:  Matt Kaufmann and J Strother Moore@*
Department of Computer Sciences@*
University of Texas at Austin@*
Austin, TX 78712-1188 U.S.A.

INFO-DIR-SECTION Math@*
START-INFO-DIR-ENTRY@*
* acl2: (acl2-doc-emacs). Applicative Common Lisp@*
END-INFO-DIR-ENTRY
@end ifinfo

@setchapternewpage odd
@titlepage
@sp 11
@center @titlefont{ACL2}
@sp 2
@center by Matt Kaufmann and J Strother Moore

@sp 2
@center ~sv
@sp 2
@center ~sm ~fy
@page
@vskip 0pt plus 1filll
Copyright @copyright{} 2013  University of Texas at Austin
Distributed under the terms of the GNU General Public License.
@sp 2
This is documentation for ~sv @*
@sp 2
Published by University of Texas at Austin.


Department of Computer Sciences @*
University of Texas at Austin @*
Austin, TX 78712-1188 U.S.A. @*
@end titlepage

@page

@iftex

NOTE: The ACL2 documentation is in hypertext form.  It is best read
with an appropriate browser and is available in both HTML and Emacs
Texinfo formats.  See the file doc/README.  If you are using the
documentation as an introduction to ACL2, start with the chapter
entitled ``ACL2-TUTORIAL''.

This is a Postscript version of the hypertext document.  While
somewhat awkward to use since the links are ``dead'', it may serve as
a reference manual.  In this Postscript version, links to other nodes
will be implicitly indicated with the mark ^.  For example, you may
see books (BOOKS^) --- this indicates that there is documentation
present on BOOKS.  The table of contents, as well as the index, will
show you where to find the node named ``BOOKS''.

Some links are followed by the sign ``<>''.  This is our way of
denoting the ``Warning Sign'' used in the HTML version of the guided
tours.  Such links lead from material that is on a guided tour into
material that is not on a guided tour.  If you are trying to follow a
guided tour with this Postscript version of the documentation, we
advise you not to follow such links.  The guided tours are best read
with an appropriate hypertext browser.

@page
@end iftex

@node Top, , , (DIR)

@ifinfo
This manual documents ~sv.
@end ifinfo
"
  "FMT string for prelude:
v = version, m = month, d = day of month, y = year and f = file-name")

(defconst *section-types*
  '("chapter" "section" "subsection" "subsubsection")
  "List of sections types used by texinfo.")

(defconst *texinfo-doc-markup-table*

  '(("-" nil ."---")
    ("B" nil ."@b{~st}")
    ("BF" nil ."~%@example") ;We'd prefer @format, but it doesn't
;                              seem to work for info
    ("BID" nil .    "") ;begin implementation dependent
    ("BQ" nil ."~%@quotation")
    ("BV" nil ."~%@example")
    ("C" nil ."@t{~st}") ;originally @code, but we don't want `' in info file
    ("EF" nil ."@end example~%")
    ("EID" nil .    "") ;end implementation dependent
    ("EM" nil ."@emph{~st}") ;emphasis
    ("EQ" nil ."~%@end quotation~%") ;we need leading line break to
;                                     avoid problems with @refill
    ("EV" nil ."@end example~%")
    ("GIF" nil .    "")      ;gif file (currently only for HTML)
    ("I" nil ."@i{~st}")
    ("ID" nil .    "") ;implementation dependent
    ("IL" t ."~st")
    ("ILC" t .    "@t{~st}") ;originally @code, but we don't want `' in
;                              info file
    ("L" t ."@xref{~sL}") ;used to start a sentence with a crossref
    ("NL" nil ."@*~%")
    ("PAR" nil .    "") ;paragraph mark, of no significance for texinfo
    ("PL" t ."@pxref{~sL}") ;used for parenthetical crossrefs
    ("SC" nil ."@sc{~st}") ;small caps
    ("ST" nil ."@strong{~st}") ;strong emphasis
    ("T" nil ."@t{~st}")
    ("TERMINAL" nil . "") ; terminal only, ignore
    ("WARN" nil . "<>")
    ("CLICK-HERE" t . "@xref{~sL}")
    ("PCLICK-HERE" t . "@pxref{~sL}")
    ("FLY" t . "Next on the Flying Tour: @pxref{~sL}")
    ("LARGE-FLY" t . "Next on the Flying Tour: @pxref{~sL}")
    ("WALK" t . "Next on the Walking Tour: @pxref{~sL}")
    ("LARGE-WALK" t . "Next on the Walking Tour: @pxref{~sL}")
    ("URL" nil ."@uref{~st}")
    )
  "Table for use in printing documentation strings, when printing to
a TeXinfo file to be used to create an info file.  See also
*tex-doc-markup-table* and *non-lucid-texinfo-doc-markup-table*.")

(defconst *tex-doc-markup-table*

  '(("-" nil ."---")
    ("B" nil ."@b{~st}")
    ("BF" nil ."~%@format")
    ("BID" nil .    "")      ;begin implementation dependent
    ("BQ" nil ."~%@quotation")
    ("BV" nil ."~%@example")
    ("C" nil ."@t{~st}") ;originally @code, but we don't want `' in info file
    ("EF" nil ."@end format~%")
    ("EID" nil .    "")      ;end implementation dependent
    ("EM" nil ."@emph{~st}") ;emphasis
    ("EQ" nil ."~%@end quotation~%") ;we need leading line break to avoid problems with @refill
    ("EV" nil ."@end example~%")
    ("GIF" nil .    "")      ;gif file (currently only for HTML)
    ("I" nil ."@i{~st}")
    ("ID" nil .     "")       ;implementation dependent
    ("IL" t ."~st (~sp^)")
    ("ILC" t .    "@t{~st} (~sp^)") ;originally @code, but we don't want `' in info file
    ("L" t ."See @ref{~sL}") ;used to start a sentence with a crossref
    ("NL" nil ."@*~%")
    ("PAR" nil .    "") ;paragraph mark, of no significance for texinfo
    ("PL" t ."@pxref{~sL}") ;used for parenthetical crossrefs
    ("SC" nil ."@sc{~st}") ;small caps
    ("ST" nil ."@strong{~st}") ;strong emphasis
    ("T" nil ."@t{~st}")
    ("TERMINAL" nil . "") ; terminal only, ignore
    ("WARN" nil . "<>")
    ("CLICK-HERE" t . "See @ref{~sL}")
    ("PCLICK-HERE" t . "@pxref{~sL}")
    ("FLY" t . "Next on the Flying Tour:  @pxref{~sL}")
    ("LARGE-FLY" t . "Next on the Flying Tour:  @pxref{~sL}")
    ("LARGE-WALK" t . "Next on the Walking Tour:  @pxref{~sL}")
    ("WALK" t . "Next on the Walking Tour:  @pxref{~sL}")
    ("URL" nil ."@t{~st}")
    )
  "Table for use in printing documentation strings, when printing to
a TeX file.  See also *texinfo-doc-markup-table* and
*non-lucid-texinfo-doc-markup-table*.  We highlight invisible links
by suffixing them with ^.")

(defconst *non-lucid-texinfo-doc-markup-table*

  '(("-" nil ."---")
    ("B" nil ."@b{~st}")
    ("BF" nil ."~%@example") ;We'd prefer @format, but it doesn't seem to work for info
    ("BID" nil .    "")      ;begin implementation dependent
    ("BQ" nil ."~%@quotation")
    ("BV" nil ."~%@example")
    ("C" nil ."@t{~st}") ;originally @code, but we don't want `' in info file
    ("EF" nil ."@end example~%")
    ("EID" nil .    "")      ;end implementation dependent
    ("EM" nil ."@emph{~st}") ;emphasis
    ("EQ" nil ."~%@end quotation~%") ;we need leading line break to avoid problems with @refill
    ("EV" nil ."@end example~%")
    ("GIF" nil .    "")      ;gif file (currently only for HTML)
    ("I" nil ."@i{~st}")
    ("ID" nil .    "")       ;implementation dependent
    ("IL" t ."~st")
    ("ILC" t .    "@t{~st}") ;originally @code, but we don't want `' in info file
    ("L" t ."See @ref{~sL}") ;used to start a sentence with a crossref
    ("NL" nil ."@*~%")
    ("PAR" nil .    "") ;paragraph mark, of no significance for texinfo
    ("PL" t ."see @pxref{~sL}") ;used for parenthetical crossrefs
    ("SC" nil ."@sc{~st}") ;small caps
    ("ST" nil ."@strong{~st}") ;strong emphasis
    ("T" nil ."@t{~st}")
    ("TERMINAL" nil . "") ; terminal only, ignore
    ("WARN" nil . "<>")
    ("CLICK-HERE" t . "See @ref{~sL}")
    ("PCLICK-HERE" t . "see @pxref{~sL}")
    ("LARGE-FLY" t . "Next on the Flying Tour:  @pxref{~sL}")
    ("FLY" t . "Next on the Flying Tour:  @pxref{~sL}")
    ("LARGE-WALK" t . "Next on the Walking Tour:  @pxref{~sL}")
    ("WALK" t . "Next on the Walking Tour:  @pxref{~sL}")
    ("URL" nil ."@uref{~st}")
    )
  "Table for use in printing documentation strings, when printing to
a TeXinfo file to be used to create an info file.  See also
*tex-doc-markup-table* and *texinfo-doc-markup-table*.")

(defun texinfo-doc-markup-table (state)
  (acl2::f-get-global 'texinfo-doc-markup-table state))

(defun write-prelude (info-file channel state)
  "Writes the prelude to CHANNEL."
  (mv-let (n state)
	  (acl2::read-idate state)
	  (let* ((date-list (acl2::decode-idate n))
		 (month (nth (1- (car (cddddr date-list)))
			     '("January" "February" "March" "April" "May"
			       "June" "July" "August" "September" "October"
			       "November" "December")))
		 (yr (+ 1900 (cadr (cddddr date-list)))))
	    (pprogn
	     (mv-let (col state)
		     (acl2::fmt1 *prelude-string*
				 (list (cons #\v
                                             (acl2::f-get-global
                                              'acl2::acl2-version
                                              state))
				       (cons #\d (cadddr date-list))
				       (cons #\m month)
				       (cons #\y yr)
				       (cons #\f info-file))
				 0
				 channel
				 state
				 nil)
		     (declare (ignore col))
		     (newline channel state))
	     (newline channel state)))))

(defun apply-texinfo-subst-table (name)
  (acl2::apply-char-subst-table
   name *texinfo-doc-char-subst-table* nil))

(defconst *texinfo-doc-link-subst-table*
  '((#\@ #\a #\t #\s #\i #\g #\n)
    (#\{ #\l #\e  #\f  #\t  #\b  #\r  #\a  #\c  #\e)
    (#\}  #\r  #\i  #\g  #\h  #\t  #\b  #\r  #\a  #\c  #\e))
  "Table for substituting characters into linknames for texinfo.")

(defun bad-chars-p (name)
  (let ((len (1- (length name))))
    (or (acl2::member-char-stringp #\@ name len)
        (acl2::member-char-stringp #\{ name len)
        (acl2::member-char-stringp #\} name len))))

(defun apply-texinfo-link-subst-table (name)
  (acl2::apply-char-subst-table
   name *texinfo-doc-link-subst-table* nil))

(defun get-link-string (name)
  (if (equal name "Top")
      "Top"
    (acl2::apply-char-subst-table
     name *texinfo-doc-link-subst-table* nil)))

(defun write-header (current next previous up section-type tex-only-flg channel state)
  "Writes node header information for node CURRENT, Next: NEXT, Previous: PREVIOUS, Up: UP"
  (pprogn
   ;; The first form is here to correct an apparent bug in
   ;; texinfo-format-buffer, in both emacs 19.22 and Lucid Emacs 19.10, which
   ;; comes up when a doc string ends with "~l[...]." on a line by itself.
   (if tex-only-flg
       state
     (pprogn (princ$ "@*" channel state)
             (newline channel state)))
   (princ$ "@node " channel state)
   (princ$ (get-link-string (car current)) channel state)
   (if next
       (pprogn (princ$ ", " channel state)
               (princ$ (get-link-string (car next)) channel state))
     (princ$ ", " channel state))
   (if previous
       (pprogn (princ$ ", " channel state)
               (princ$ (get-link-string (car previous)) channel state))
     (princ$ ", " channel state))
   (if up
       (pprogn (princ$ ", " channel state)
               (princ$ (get-link-string (car up)) channel state))
     (princ$ ", " channel state))
   (newline channel state)
   (princ$ "@comment  node-name, next, previous, up"
           channel state)
   (newline channel state)
   (if section-type
       (let ((name (apply-texinfo-subst-table (car current))))
         (pprogn (newline channel state)
                 (princ$ "@iftex" channel state)
                 (newline channel state)
                 (princ$ "@" channel state)
                 (princ$ section-type channel state)
                 (princ$ " " channel state)
                 (princ$ name channel state)
                 (newline channel state)
                 (princ$ "@end iftex" channel state)
                 (newline channel state)
                 (princ$ "@cindex " channel state)
                 (princ$ name channel state)
                 (newline channel state)))
     state)))

(defun write-menu-header (tex-only-flg channel state)
  (pprogn (newline channel state)
          (if tex-only-flg
              (princ$ "@format" channel state)
            (princ$ "@menu" channel state))
	  (newline channel state)))

(defun write-doc-menu-item (name str channel state)
  (pprogn (princ$ "* " channel state)
          (princ$ (get-link-string name) channel state)
	  (princ$ ":: " channel state)
          (if (bad-chars-p name)
              (pprogn (princ$ "(" channel state)
                      (princ$ (apply-texinfo-subst-table name) channel state)
                      (princ$ ") " channel state))
            state)
	  (acl2::print-doc-string-part 0 str ""
                                       (texinfo-doc-markup-table state)
                                       *texinfo-doc-char-subst-table*
                                       (acl2::doc-fmt-alist state)
                                       channel
                                       name
                                       nil
                                       nil  ; undocumented-file
                                       nil  ; vp
                                       state)))

(defun write-doc-menu1 (lst doc-alist tex-only-flg channel state)
  ;; lst is a list of names
  (cond ((null lst) state)
	(t (pprogn
	    (write-doc-menu-item (car lst)
				 (cadddr (assoc-equal (car lst) doc-alist))
                                 channel state)
	    (if tex-only-flg
                state
              (newline channel state))
	    (write-doc-menu1 (cdr lst) doc-alist tex-only-flg channel state)))))

(defun write-doc-menu-aux (doc-tuple doc-alist tex-only-flg channel state)
  "Writes a menu with entries from the list LST of names."
  (cond ((null (caddr doc-tuple)) state)
	(t (let* ((main-subitems
                   (strip-cars (cddddr doc-tuple)))
                  (other-menu-items
                   (acl2::merge-sort-alpha-<
                    (if main-subitems
                        (acl2::set-difference-equal
                         (caddr doc-tuple)
                         main-subitems)
                      (caddr doc-tuple)))))
             (pprogn (write-menu-header tex-only-flg channel state)
                     (write-doc-menu1
                      main-subitems doc-alist tex-only-flg channel state)
                     (cond
                      (other-menu-items
                       (pprogn
                        (newline channel state)
                        (princ$ "Related topics other than immediate subtopics:"
                                channel state)
                        (newline channel state)
                        (write-doc-menu1
                         other-menu-items doc-alist tex-only-flg channel state)))
                      (t state))
                     (if tex-only-flg
                         (princ$ "@end format" channel state)
                       (princ$ "@end menu" channel state))
                     (newline channel state) (newline channel state))))))

(defun write-doc-menu (doc-tuple doc-alist tex-only-flg channel state)
  (pprogn (write-doc-menu-aux doc-tuple doc-alist nil channel state)
          (if tex-only-flg
              (write-doc-menu-aux doc-tuple doc-alist t channel state)
            state)))

(defun write-a-doc-section (doc-tuple next previous up section-type
				      doc-alist tex-only-flg channel state)

; In fact doc-tuple may really be a doc-tree, but that's ok.

  (pprogn
   (write-header
    doc-tuple next previous up section-type tex-only-flg channel state)
   (princ$ "@format" channel state)
   (newline channel state)
   (princ$ (apply-texinfo-subst-table (car doc-tuple)) channel state)
   (princ$ "@t{    }" channel state)
   (acl2::print-doc-string-part 0 (cadddr doc-tuple)
                                ""
                                (texinfo-doc-markup-table state)
                                *texinfo-doc-char-subst-table*
                                (acl2::doc-fmt-alist state)
                                channel
                                (car doc-tuple)
                                nil
                                nil  ; undocumented-file
                                nil  ; vp
                                state)
   (princ$ "@end format" channel state)
   (newline channel state)
   (acl2::print-doc-string-part 1 (cadddr doc-tuple) ""
                                (texinfo-doc-markup-table state)
                                *texinfo-doc-char-subst-table*
                                (acl2::doc-fmt-alist state)
                                channel
                                (car doc-tuple)
                                nil
                                nil  ; undocumented-file
                                nil  ; vp
                                state)
   (newline channel state)
   (write-doc-menu doc-tuple doc-alist tex-only-flg channel state)
   (acl2::print-doc-string-part 2 (cadddr doc-tuple) ""
                                (texinfo-doc-markup-table state)
                                *texinfo-doc-char-subst-table*
                                (acl2::doc-fmt-alist state)
                                channel
                                (car doc-tuple)
                                t
                                nil  ; undocumented-file
                                nil  ; vp
                                state)
   (newline channel state)))

(mutual-recursion

(defun write-doc-tree-lst (doc-trees previous up section-types
                                     doc-alist tex-only-flg channel state)
  (cond ((null doc-trees) state)
	(t (pprogn (write-doc-tree (car doc-trees)
                                   (cadr doc-trees)
                                   previous
                                   up
                                   section-types
                                   doc-alist
                                   tex-only-flg
                                   channel
                                   state)
                   (write-doc-tree-lst (cdr doc-trees)
                                       (car doc-trees)
                                       up section-types doc-alist
                                       tex-only-flg channel state)))))

(defun write-doc-tree (doc-tree next previous up section-types
                                doc-alist tex-only-flg channel state)

;; (doc-tuple next previous up section-type channel state)

  (pprogn (write-a-doc-section doc-tree
                               next
                               previous
                               up
                               (car section-types)
                               doc-alist
                               tex-only-flg
                               channel
                               state)
          (write-doc-tree-lst (cddddr doc-tree)
                              doc-tree
                              doc-tree
                              (cdr section-types)
                              doc-alist
                              tex-only-flg
                              channel
                              state)))

)

(defun write-texinfo-file1 (doc-trees info-file doc-alist tex-only-flg channel state)
  (pprogn (write-prelude info-file channel state)
          (pprogn
           (write-menu-header nil channel state)
           (newline channel state)
           (write-doc-menu1 (strip-cars doc-trees)
                            doc-alist nil channel state)
           (princ$ "* Index:: An item for each documented ACL2 item."
                   channel state)
           (newline channel state)
           (princ$ "@end menu" channel state)
           (newline channel state))
          (newline channel state)
	  (write-doc-tree-lst doc-trees
                              *top-node*
                              *top-node*
                              *section-types*
                              doc-alist tex-only-flg channel state)
	  (newline channel state)
          ;; See comment in write-header
          (if tex-only-flg
              state
            (pprogn (princ$ "@*" channel state)
                    (newline channel state)))
          (princ$ "@node  Index, , , Top" channel state)
	  (newline channel state)
	  (princ$"@comment node-name, next,previous, up" channel state)
	  (newline channel state)
	  (princ$ "@unnumbered Index" channel state)
	  (newline channel state) (newline channel state)
	  (princ$ "@printindex cp" channel state)
	  (newline channel state)
	  (princ$ "@contents" channel state)
	  (newline channel state)
	  (princ$ "@bye" channel state)
	  (newline channel state)))

; Recall that a doc tuple of of the form
; (node-name section-name menu-items doc-string).
; A doc tree is a node of a similar form, extended by children
; (node-name section-name menu-items doc-string . children)
; where each member of children is a doc tree.  In fact section-name
; is the parent:  so, if the node-name in a doc tuple is the same as
; its section-name, we replace the section-name with "Top".
; The top-level doc tree is
; ("Top" nil <top-level-section-names> "The top level node."
;  . <top-level-section-nodes>)

(defun extend-assoc-equal (key val alist)
  (cond ((null alist) (list (cons key (list val))))
        ((equal key (caar alist))
         (cons (cons key (cons val (cdar alist)))
               (cdr alist)))
        (t (cons (car alist) (extend-assoc-equal key val (cdr alist))))))

(defun section-alist (doc-alist ans)

; Associates each section name with the doc-tuples in its section.

  (cond
   ((null doc-alist) ans)
   (t (let ((doc-tuple (car doc-alist)))
        (section-alist
         (cdr doc-alist)
         (extend-assoc-equal (cadr doc-tuple)
                             doc-tuple
                             ans))))))

(defun find-node-val (val alist acc)

; Returns (cons entry rest-alist), where val is a member-equal of (strip-cars
; (cdr entry)), entry is a member-equal of alist, and rest-alist is the result
; of deleting the first occurrence of entry from alist.  Except, if there is no
; such entry, then nil is returned.  Called with acc = NIL.

  (cond
   ((null alist) nil)
   ((assoc-equal val (cdar alist))
    (cons (car alist)
          (revappend acc (cdr alist))))
   (t
    (find-node-val val (cdr alist) (cons (car alist) acc)))))

(defun sort-section-alist (section-alist ans)

; When we see an entry (section . doc-tuples), we want to be sure that section
; appears in ans before we add it, unless section is "Top".  That way, we are
; sure that every section key in ans appears as a doc-tuple later in ans.

; If the "graph" is circular in section-alist, this will not terminate!

  (cond
   ((null section-alist) ans)
   (t
    (let ((new-section-alist
           (find-node-val (caar section-alist)
                          (cdr section-alist)
                          (list (car section-alist)))))
      (if new-section-alist
          (sort-section-alist new-section-alist ans)
        (sort-section-alist (cdr section-alist)
                            (cons (car section-alist) ans)))))))

(defun append0 (x y)
  (if (null y)
      x
    (append x y)))

(defun build-doc-tree-lst (doc-tuples section-alist)

; Here, if a doc-tuple represents a section, then that section should already
; be associated with a list of doc-trees in section-alist.

  (cond
   ((null doc-tuples)
    nil)
   (t (cons (append0 (car doc-tuples)
                     (cdr (assoc-equal (caar doc-tuples) section-alist)))
            (build-doc-tree-lst (cdr doc-tuples) section-alist)))))

(defun merge-car-alpha-< (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((acl2::alpha-< (car (car l1)) (car (car l2)))
         (cons (car l1) (merge-car-alpha-< (cdr l1) l2)))
        (t (cons (car l2) (merge-car-alpha-< l1 (cdr l2))))))

(defun merge-sort-car-alpha-< (l)
  (cond ((null (cdr l)) l)
        (t (merge-car-alpha-< (merge-sort-car-alpha-< (acl2::evens l))
                              (merge-sort-car-alpha-< (acl2::odds l))))))

(defun expand-section-alist (section-alist acc)

; Replaces each doc tuple in section-alist with a doc tree.  We assume that
; section-alist is sorted "bottom up", i.e., each section's doc tuple appears
; later in section-alist than does its entry.  The resulting expanded section
; alist is returned in reverse order, so that "Top" is at the front.  We
; sort the newly-appended children alphabetically.

  (cond
   ((null section-alist) acc)
   (t (expand-section-alist
       (cdr section-alist)
       (cons (cons (caar section-alist)
                   (build-doc-tree-lst
                    (merge-sort-car-alpha-< (cdar section-alist))
                    acc))
             acc)))))

(defun insert-top-in-doc-alist (doc-alist ans)
  (cond
   ((null doc-alist)
    (reverse ans))
   ((equal (caar doc-alist) (cadar doc-alist))
    (insert-top-in-doc-alist
     (cdr doc-alist)
     (cons (list* (caar doc-alist) "Top" (cddar doc-alist))
           ans)))
   (t (insert-top-in-doc-alist (cdr doc-alist)
                               (cons (car doc-alist) ans)))))

(defun top-doc-trees (doc-alist)

; The idea, as I recall (documenting this way after the code was written) is
; that we take (cdr (car ...)) in order to obtain the sections immediately
; under "Top", where the entry for "Top" appears first.

  (cdr (car (expand-section-alist
             (sort-section-alist
              (section-alist
               (insert-top-in-doc-alist doc-alist nil)
               nil)
              nil)
             nil))))

(defun texinfo-fmt-alist (doc-alist spack acc)
  (cond
   ((null doc-alist) acc)
   (t (texinfo-fmt-alist
       (cdr doc-alist)
       spack
       (let ((raw-name (texinfo-node-name (caar doc-alist) spack t)))
         (cons (list* raw-name
                      (cons #\T (string-upcase raw-name)) ;presumably already upper case
                      (cond
                       ((bad-chars-p raw-name)
                        (let ((link-name (apply-texinfo-link-subst-table
                                          raw-name)))
                          (list (cons #\l link-name)
                                (cons #\L
                                      (concatenate
                                       'string
                                       link-name
                                       ",,"
                                       (apply-texinfo-subst-table
                                        raw-name))))))
                       (t (list (cons #\l raw-name)
                                (cons #\L raw-name)))))
               acc))))))


(defmacro my-state-global-let* (bindings form)

; Like acl2::state-global-let*, but where form returns state.

  `(mv-let (erp val state)
           (acl2::state-global-let* ,bindings
                                    (pprogn ,form (acl2::value nil)))
           (declare (ignore erp val))
           state))

(defun write-texinfo-file-fn
  (texinfo-file info-file spack
                tex-only-flg tex-only-flg-supplied-p non-lucid-flg
                topics
                state)
  (pprogn
   (acl2::set-debugger-enable t)
   (acl2::f-put-global 'texinfo-doc-markup-table
                       (cond
                        (tex-only-flg *tex-doc-markup-table*)
                        (non-lucid-flg *non-lucid-texinfo-doc-markup-table*)
                        (t *texinfo-doc-markup-table*))
                       state)
   (acl2::fms "Writing texinfo file ~s0, default package ~p1.~%"
              (list (cons #\0 texinfo-file)
                    (cons #\1 (acl2::symbol-package-name spack)))
              (acl2::standard-co state) state nil)
   (my-state-global-let*
    ((acl2::bar-sep-p t) ; print :: as || in node names
     (acl2::write-for-read t)
     (acl2::fmt-soft-right-margin 100000 acl2::set-fmt-soft-right-margin)
     (acl2::fmt-hard-right-margin 200000 acl2::set-fmt-hard-right-margin)
     (acl2::doc-fmt-alist
      (texinfo-fmt-alist
       (acl2::global-val 'acl2::documentation-alist (acl2::w state))
       spack
       nil)))
    (let ((doc-alist (doc-alist spack tex-only-flg topics state)))
      (mv-let (channel state)
              (acl2::open-output-channel texinfo-file :character state)
              (write-texinfo-file1
               (top-doc-trees doc-alist)
               info-file
               doc-alist tex-only-flg channel state))))
   (acl2::fms "Done.~%" nil
              (acl2::standard-co state) state nil)
   (if (not tex-only-flg)
       (acl2::fms "In emacs, use meta-x texinfo-format-buffer on file ~s0 to ~
                   create info file ~s1.~%"
                  (list (cons #\0 texinfo-file)
                        (cons #\1 info-file))
                  (acl2::standard-co state) state nil)
     state)
   (if (or tex-only-flg
           (not tex-only-flg-supplied-p))
       (acl2::fms "At the shell, invoke~%~%texi2dvi ~s0~%~%to create .dvi file.~%"
                  (list (cons #\0 texinfo-file))
                  (acl2::standard-co state) state nil)
     state)
   (acl2::value :invisible)))

(defmacro acl2::write-texinfo-file (&key (dir-string '"")
                                         (file '"acl2-doc")
                                         (sym 'acl2::rewrite)
                                         (pkg '"ACL2")
                                         (tex-only-flg 'nil tex-only-flg-supplied-p)
                                         (non-lucid-flg 'nil)
                                         (topics 'nil))
  (if (and tex-only-flg non-lucid-flg)
      '(acl2::er acl2::soft
                 "It makes no sense to supply non-nil values for both ~
                  tex-only-flg and non-lucid-flg.")
    (list 'if
          `(equal (acl2::symbol-package-name ',sym) ,pkg)
          (list 'write-texinfo-file-fn
                (acl2::concatenate 'string
                                   dir-string
                                   file
                                   (if tex-only-flg
                                       ".tex"
                                     ".texinfo"))
                (acl2::string-append file ".info")
                (list 'quote sym)
                tex-only-flg
                tex-only-flg-supplied-p
                non-lucid-flg
                topics
                'state)
          `(acl2::er acl2::soft 'acl2::write-texinfo-file
                     "The second argument of WRITE-TEXINFO-FILE needs to be in ~
                      the package specified in the third argument (default:  ~
                      \"ACL2\").  However, the symbol ~p0 is in package ~p1, ~
                      not in package ~p2."
                     ',sym
                     (acl2::symbol-package-name ',sym)
                     ,pkg))))

(defmacro acl2::write-tex-file (&key
                                (dir-string '"")
                                (file '"acl2-doc")
                                (sym 'acl2::rewrite)
                                (pkg '"ACL2")
                                (topics 'nil))
  `(acl2::write-texinfo-file :dir-string ,dir-string
                             :file ,file
                             :sym ,sym
                             :pkg ,pkg
                             :tex-only-flg t
                             :topics ,topics))

