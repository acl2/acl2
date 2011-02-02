; Conversion from ACL2 :DOC into XDOC Format
; Copyright (C) 2011  University of Texas at Austin

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

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
  '(("-" nil .    "--")
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

; XDOC question: Is <img> supported?  I generate it just below, but I'm not
; sure I do it right.

; A: hrmn.  not supported right now.  I'm just going to put in [image] until
; I add support for it.

;    ("GIF" nil . "<img src=~st></img>") ;gif files; e.g., ~gif[\"foo.gif\" align=top]
    ("GIF" nil . "[image]") ;gif files; e.g., ~gif[\"foo.gif\" align=top]

    ("I" nil .  "<i>~st</i>")
    ("ID" nil .    "")       ;implementation dependent
    ("IL" t .  "@(see ~sc)")
    ("ILC" t .  "<tt>@(see ~sc)</tt>")
    ("L" t .  "See @(see ~sc)")
    ("NL" nil .  "<br/>~%")
    ("PAR" nil .  "<p/>~%~%")
    ("PL" t .  "see @(see ~sc)")
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

;    ("WARN" nil . "<a href=\"A_Tiny_Warning_Sign.html\"><img src=twarning.gif></img></a>")
    ("WARN" nil . "[image]")

; Jared note: these don't seem quite right.
;    ("CLICK-HERE" t .  "Click <a href=\"~sc\">here</a>")
;    ("PCLICK-HERE" t .  "click <a href=\"~sc\">here</a>")
    ("CLICK-HERE" t .  "Click <see topic=\"@(url ~sc)\">here</see>")
    ("PCLICK-HERE" t .  "click <see topic=\"@(url ~sc)\">here</see>")

;    ("FLY" t .  "<a href=\"~sc\"><img src=flying.gif></img></a>")
;    ("LARGE-FLY" t .  "<a href=\"~sc\"><img src=large-flying.gif></img></a>")
;    ("WALK" t .  "<a href=\"~sc\"><img src=walking.gif></img></a>")
;    ("LARGE-WALK" t .  "<a href=\"~sc\"><img src=large-walking.gif></img></a>")

    ("FLY" t .  "[image]")
    ("LARGE-FLY" t .  "[image]")
    ("WALK" t .  "[image]")
    ("LARGE-WALK" t .  "[image]")

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

(defun write-a-doc-section (doc-tuple doc-fmt-alist channel state)

; We return an xdoc database entry based on doc-tuple.

  (let ((name (if (stringp (nth 0 doc-tuple))
                  (intern (nth 0 doc-tuple) "ACL2")
                (nth 0 doc-tuple)))
        (parent (nth 1 doc-tuple))
; See comment below about (nth 2 doc-tuple).
        (doc-string (nth 3 doc-tuple)))
    (acl2::er-let*

; XDOC change: We avoid writing the header, which would be something like
; <h1>TOPIC-FOO</h1>.  Note that we no longer give special treatment to "Pages
; Written Especially for the Tours" in that non-existent header or in the
; short string (defined just below).

     ((short
       (pprogn
        (acl2::print-doc-string-part
         0 doc-string

; Jared question: what's the purpose of the following?  It seems to insert
; <code></code> blocks after newlines in the short string... this seems really
; weird...?
; It looks like this is inherited from the html writer.  I'm going to just
; try taking it out.

         "" ; was "<code>   </code>"
         *xdoc-doc-markup-table* *xdoc-doc-char-subst-table* doc-fmt-alist
         channel name t *xdoc-undocumented-topic* nil state)
        (get-output-stream-string$ channel state nil)))

; XDOC change: A block of code including a call (print-name-as-link ...)
; normally prints the "Major Section" information that we see on html pages,
; but I'll assume that the xdoc system will manage that sort of thing itself.

      (long
       (mv-let
         (ln state)
         (acl2::print-doc-string-part-mv
          1 doc-string "" *xdoc-doc-markup-table* *xdoc-doc-char-subst-table*
          doc-fmt-alist channel (car doc-tuple) :par
          *xdoc-undocumented-topic* *xdoc-vp* state)

; XDOC change: We omit a call (write-doc-menu ...), assuming that the xdoc
; system will take care of menus.  But note that our menus include citations
; which will thus probably be missing from the xdoc documentation unless we
; take extra measures.  The list of children together with topics collected
; from :cite and :cited-by fields is found in (nth 2 doc-tuple).

         (pprogn
          (acl2::print-doc-string-part
           2 doc-string "" *xdoc-doc-markup-table* *xdoc-doc-char-subst-table*
           doc-fmt-alist channel (car doc-tuple) ln *xdoc-undocumented-topic*
           *xdoc-vp* state)
          (get-output-stream-string$ channel state nil)))))

; XDOC change: unlike the HTML pages, we avoid laying down images that link to
; the documentation's main page and index.

;    (write-trailer xdoc-file index-file channel state)

     (acl2::value
      (list (cons :name name)
            (cons :parents (list parent))
            (cons :base-pkg
                  (if (equal (symbol-package-name name) "ACL2-PC")
                      name
                    'acl2::rewrite))
            (cons :short (jared-string-upcase-first short))
            (cons :long long))))))

(defun xdoc-fmt-alist (doc-alist acc)
  (cond
   ((null doc-alist)
    acc)
   (t (xdoc-fmt-alist
       (cdr doc-alist)
       (cons (let* ((s (caar doc-alist)))
               (list
                (cond ((stringp s) s)
                      (t (let ((name (symbol-name s)))
                           (cond ((eq s (intern$ name "ACL2"))
                                  name)
                                 (t (concatenate 'string
                                                 (symbol-package-name s)
                                                 "::"
                                                 name))))))
                (cons #\p s)
                (cons #\c s)))
             acc)))))

(defun xdoc-alist1 (doc-alist fmt-alist channel state acc)
  (cond ((endp doc-alist) (acl2::value acc))
        (t (acl2::er-let*
            ((entry (write-a-doc-section (car doc-alist) fmt-alist channel
                                         state)))
            (xdoc-alist1 (cdr doc-alist) fmt-alist channel state
                         (cons entry acc))))))

(defun filter-doc-alist (skip-topics doc-alist)
  (if (atom doc-alist)
      nil
    (let* ((doc-tuple (car doc-alist))
           (name (if (stringp (nth 0 doc-tuple))
                     (intern (nth 0 doc-tuple) "ACL2")
                   (nth 0 doc-tuple))))
      (if (member name skip-topics)
          (filter-doc-alist skip-topics (cdr doc-alist))
        (cons doc-tuple
              (filter-doc-alist skip-topics (cdr doc-alist)))))))

(defun write-xdoc-alist-fn (write-p return-p skip-topics state)
  (acl2::state-global-let*
   ((acl2::fmt-hard-right-margin 500)
    (acl2::fmt-soft-right-margin 480))
   (let ((doc-alist (global-val 'acl2::documentation-alist
                                (acl2::w state))))
     (mv-let
      (channel state)
      (open-output-channel :string :object state)
      (acl2::er-let*
       ((result (xdoc-alist1 (filter-doc-alist skip-topics doc-alist)
                             (xdoc-fmt-alist doc-alist nil)
                             channel state nil)))
       (pprogn (close-output-channel channel state)
               (cond (write-p (acl2::f-put-global 'acl2::xdoc-alist
                                                  result
                                                  state))
                     (t state))
               (acl2::value (and return-p result))))))))

(defmacro acl2::write-xdoc-alist (&key (write-p 't)
                                       (return-p 'nil)
                                       (skip-topics 'nil))
  `(write-xdoc-alist-fn ,write-p ,return-p ,skip-topics state))

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
