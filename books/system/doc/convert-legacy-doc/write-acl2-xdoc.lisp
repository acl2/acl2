; This book is derived from ACL2 community book:
; xdoc/write-acl2-xdoc.lisp

; Conversion from ACL2 :DOC into XDOC Format
; Copyright (C) 2011-2014  Regents of the University of Texas
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
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "Table with entries (char . char-list) for substituting characters."
|#)

(defconst *xdoc-doc-markup-table*
  '(("-" nil .    "&mdash;")
    ("B" nil .  "<b>~st</b>")

    ("BID" nil .    "")      ;begin implementation dependent
    ("BPAR" nil .  "~%~%<p>")

; XDOC question: Is <blockquote> supported?  I generate it just below.

; A: it isn't supported, but I'll add support for it.

    ("BF" nil .  "</p>~%~%<code>")
    ("BQ" nil .  "</p>~%~%<blockquote><p>")
    ("BV" nil .  "</p>~%~%<code>")

    ("EF" nil .  "</code>~%~%<p>")
    ("EV" nil .  "</code>~%~%<p>")

    ("C" nil .  "<tt>~st</tt>")
    ("EID" nil .    "")      ;end implementation dependent
    ("EM" nil .  "<i>~st</i>") ;emphasis
    ("EPAR" nil .  "</p>")
    ("EQ" nil .  "</p></blockquote>~%~%<p>")


; XDOC question: Is <img> suppor]ted?  I generate it just below, but I'm not
; sure I do it right.

; A: hrmn.  not supported right now.  I'm just going to put in [image] until
; I add support for it.

    ("GIF" nil . "<img src='~st' />") ;gif files; e.g., ~gif[\"foo.gif\" align=top]
;    ("GIF" nil . "[image]") ;gif files; e.g., ~gif[\"foo.gif\" align=top]

    ("I" nil .  "<i>~st</i>")
    ("ID" nil .    "")       ;implementation dependent

; The ACL2 documentation prints out ~ilc[] links in fixed-width font all the
; time, but I sort of dislike that and would rather just print them in the same
; font.  So I arbitrarily choose to treat ~il and ~ilc the same.

    ("IL" t .  "<see topic='@(url ~sc)'>~st</see>")

    ;; Temporary hack: annotate see tag with code attribute, so we can identify
    ;; them more easily in export-acl2doc.lisp
    ("ILC" t .  "<see topic='@(url ~sc)' use-tsee='yes'>~st</see>")
    ("L" t .  "See <see topic='@(url ~sc)'>~st</see>")
    ("PL" t .  "see <see topic='@(url ~sc)'>~st</see>")

    ("NL" nil .  "<br/>~%")
    ("PAR" nil .  "<p/>~%~%")

    ("SC" nil .  "~sT")
    ("ST" nil .  "<b>~st</b>") ;strong emphasis
    ("T" nil .  "<tt>~st</tt>")
    ("TERMINAL" nil . "") ; terminal only, ignore

; XDOC question: Again, is <img> supported?  I generate it just below, but I'm
; not sure I do it right, especially since it's within <a>.  There's the same
; issue for "FLY", "WALK", and "LARGE WALK".
; XDOC question: Is it OK to refer to an image?  I guess twarning.gif will need
; to be around.

; A: replacing images with [image] for now, I'll add support somehow.

    ("WARN" nil . "<see topic='ACL2____A_02Tiny_02Warning_02Sign'><img src='twarning.gif'/></see>")
;    ("WARN" nil . "[image]")

; Jared note: these don't seem quite right.
;    ("CLICK-HERE" t .  "Click <a href=\"~sc\">here</a>")
;    ("PCLICK-HERE" t .  "click <a href=\"~sc\">here</a>")
    ("CLICK-HERE" t .  "Click <see topic='@(url ~sc)'>here</see>")
    ("PCLICK-HERE" t .  "click <see topic='@(url ~sc)'>here</see>")

    ("FLY" t .  "<see topic='@(url ~sc)'><img src='flying.gif'/></see>")
    ("LARGE-FLY" t .  "<see topic='@(url ~sc)'><img src='large-flying.gif'/></see>")
    ("WALK" t .  "<see topic='@(url ~sc)'><img src='walking.gif'/></see>")
    ("LARGE-WALK" t .  "<see topic='@(url ~sc)'><img src='large-walking.gif'/></see>")

;    ("FLY" t .  "[image]")
;    ("LARGE-FLY" t .  "[image]")
;    ("WALK" t .  "[image]")
;    ("LARGE-WALK" t .  "[image]")

; XDOC question: Does this handling of "URL" seem OK?  I think it's
; appropriate, rather than @(url ...), since it's not for symbols; but I'm not
; sure.

; A: I think it's probably okay.

    ("URL" nil .  "<a href='~st'>~st</a>")
    )
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "Table for use in printing documentation strings, when printing to
an xdoc file.  See :DOC markup"
|#)

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

; Utility for accessing element of xdoc-alist:

(defun xdoc-entry-fn (name xdoc-alist)
  (cond ((endp xdoc-alist) nil)
        ((equal name (cdr (assoc-eq :name (car xdoc-alist))))
         (car xdoc-alist))
        (t (xdoc-entry-fn name (cdr xdoc-alist)))))

(defmacro acl2::xdoc-entry (name)
  `(xdoc-entry-fn ',name
                  (acl2::f-get-global 'acl2::xdoc-alist
                                      state)))
