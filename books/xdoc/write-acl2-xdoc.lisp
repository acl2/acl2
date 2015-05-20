; Conversion from ACL2 :DOC into XDOC Format
; Copyright (C) 2014, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; This file is based on doc/write-acl2-html.lisp, and serves to produce an xdoc
; list (see books/xdoc/top.lisp) from (global-val 'documentation-alist (w
; state)).  Thanks to Jared Davis for his assistance in developing this file.

(in-package "ACL2-USER")

(acl2::set-state-ok t)

(acl2::program)

; The idea of node names:  first apply the character substitution table, then
; deal with the colon.

(defconst *xdoc-doc-char-subst-table*
  '((#\& #\& #\a #\m #\p #\;)
    (#\< #\& #\l #\t #\;)
    (#\> #\& #\g #\t #\;)
    (#\@ #\@ #\@))
  "Table with entries (char . char-list) for substituting characters.")

(defconst *xdoc-doc-markup-table*
  '(("-" nil .    "&mdash;")
    ("B" nil .  "<b>~st</b>")
    ("BF" nil .  "~%<code>")
    ("BID" nil .    "")      ;begin implementation dependent
    ("BPAR" nil .  "<p>")

; XDOC question: Is <blockquote> supported?  I generate it just below.

; A: it isn't supported, but I'll add support for it.

    ("BQ" nil .  "</p>~%<blockquote><p>")
    ("BV" nil .  "~%<code>")
    ("C" nil .  "<tt>~st</tt>")
    ("EF" nil .  "</code>~%")
    ("EID" nil .    "")      ;end implementation dependent
    ("EM" nil .  "<i>~st</i>") ;emphasis
    ("EPAR" nil .  "</p>")
    ("EQ" nil .  "</p></blockquote>~%<p>")
    ("EV" nil .  "</code>~%")

; XDOC question: Is <img> supported?  
;  Yes but not documented.  <icon src='...'> is for inline images,
;  <img src='...'> is for larger, centered images

    ("GIF" nil . "<icon src='~st' />") ;gif files; e.g., ~gif[\"foo.gif\" align=top]
;    ("GIF" nil . "[image]") ;gif files; e.g., ~gif[\"foo.gif\" align=top]

    ("I" nil .  "<i>~st</i>")
    ("ID" nil .    "")       ;implementation dependent

; The ACL2 documentation prints out ~ilc[] links in fixed-width font all the
; time, but I sort of dislike that and would rather just print them in the same
; font.  So I arbitrarily choose to treat ~il and ~ilc the same.

    ("IL" t .  "<see topic=\"@(url ~sc)\">~st</see>")
    ("ILC" t .  "<see topic=\"@(url ~sc)\">~st</see>")
    ("L" t .  "See @(see ~sc)")
    ("NL" nil .  "<br/>~%")
    ("PAR" nil .  "<p/>~%~%")
    ("PL" t .  "see @(see ~sc)")
    ("SC" nil .  "~sT")
    ("ST" nil .  "<b>~st</b>") ;strong emphasis
    ("T" nil .  "<tt>~st</tt>")
    ("TERMINAL" nil . "") ; terminal only, ignore

    ("WARN" nil . "<see topic='ACL2____A_02Tiny_02Warning_02Sign'><icon src='twarning.gif'/></see>")
;    ("WARN" nil . "[image]")

; Jared note: these don't seem quite right.
;    ("CLICK-HERE" t .  "Click <a href=\"~sc\">here</a>")
;    ("PCLICK-HERE" t .  "click <a href=\"~sc\">here</a>")
    ("CLICK-HERE" t .  "Click <see topic=\"@(url ~sc)\">here</see>")
    ("PCLICK-HERE" t .  "click <see topic=\"@(url ~sc)\">here</see>")

    ("FLY" t .  "<see topic=\"@(url ~sc)\"><icon src='flying.gif'/></see>")
    ("LARGE-FLY" t .  "<see topic=\"@(url ~sc)\"><icon src='large-flying.gif'/></see>")
    ("WALK" t .  "<see topic=\"@(url ~sc)\"><icon src='walking.gif'/></see>")
    ("LARGE-WALK" t .  "<see topic=\"@(url ~sc)\"><icon src='large-walking.gif'/></see>")

;    ("FLY" t .  "[image]")
;    ("LARGE-FLY" t .  "[image]")
;    ("WALK" t .  "[image]")
;    ("LARGE-WALK" t .  "[image]")

; XDOC question: Does this handling of "URL" seem OK?  I think it's
; appropriate, rather than @(url ...), since it's not for symbols; but I'm not
; sure.

; A: I think it's probably okay.

    ("URL" nil .  "<a href=\"~st\">~st</a>")
    )
  "Table for use in printing documentation strings, when printing to
an xdoc file.  See :DOC markup")

(defconst *xdoc-vp* ; see print-doc-string-part1
  '(("BV" "BF") . ("EV" "EF")))

(defconst *xdoc-undocumented-topic*
  ;; Keep in sync with import-acl2doc.lisp
  "acl2::broken-link")

(defun jared-string-upcase-first (x)
  ;; Upper-case the first letter of a string, if it's lower-case.
  ;; Most one-liners in the acl2 documentation have lower-case descriptions.
  ;; I prefer upper-case for xdoc.
  (let ((len (length x)))
    (if (and (< 0 len)
             (standard-char-p (char x 0))
             (not (equal (char-upcase (char x 0))
                         (char x 0))))
        (concatenate 'string
                     (coerce (list (char-upcase (char x 0))) 'string)
                     (subseq x 1 nil))
      x)))
