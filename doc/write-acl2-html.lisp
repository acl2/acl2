; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 was produced by modifying ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTES-2-0.

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
; email:       Kaufmann@aus.edsr.eds.com   and Moore@cs.utexas.edu
; Department of Computer Sciences
; University of Texas at Austin
; Austin, TX 78712-1188 U.S.A.

; Modified 3/2001 for Version_2.6 by Michael N. Bogomolny, to generate
; a distinct HTML file for each doc topic, in support of his search engine.
; Updated 11/2002 for Version_2.7 by Michael N. Bogomolny, to fix a bug
; related to deeply nested doc topics.

; Html driver for ACL2 documentation.  Sample usage:
; (write-html-file "acl2-doc") or even (write-html-file).

; NOTE:  This could perhaps be improved by putting "next" and "previous" links
; by the "Parent topic" link.

; This file defines the macro write-html-file, which writes an html file.
; It takes all the documentation strings that are available via the ACL2 :DOC
; command and creates the html file.

; Suppose you get an error like this:

#||
  ACL2 p!>(write-html-file :topics '(STR::STR) :pkg "STR")

  Writing html file acl2-doc.html, default package "STR".


  HARD ACL2 ERROR in FMT-VAR:  Unbound Fmt Variable.  The tilde directive at location 13 in the fmt string below uses the variable #\c.  But this variable is not bound in the association list, ((#\p . "SUBSTR") (#\s . "SUBSTR") (#\t . "substr") (#\T . "SUBSTR")), supplied with the fmt string.

  "see <a href=\"~sc\">~st</a>"
||#

; What this kind of error typically means is that there was a link (~l or ~pl
; or ~il) in a :doc string to SUBSTR, yet SUBSTR wasn't documented.  With a
; grep you can perhaps figure out what's wrong, e.g., perhaps ~l[substr] was
; supposed to be ~l[substrp].

(in-package "ACL2-USER")

(acl2::set-state-ok t)

(acl2::program)

; The idea of node names:  first apply the character substitution table, then
; deal with the colon.

(defconst *html-doc-char-subst-table*
  '((#\& #\& #\a #\m #\p #\;)
    (#\< #\& #\l #\t #\;)
    (#\> #\& #\g #\t #\;))
  "Table with entries (char . char-list) for substituting characters.")

(defconst *html-doc-char-subst-table-for-anchors*
  (cons '(#\Space #\-)
        *html-doc-char-subst-table*)
  "Table with entries (char . char-list) for substituting characters; also ~
   for use with anchors.")

(defconst *filename-char-subst-table*
  '((#\/ #\_ #\s #\l #\a #\s #\h #\_)
    (#\\ #\_ #\b #\a #\c #\k #\s #\l #\a #\s #\h #\_)
    (#\& #\_ #\a #\m #\p #\e #\r #\s #\a #\n #\d #\_)
    (#\Space #\_)
    (#\: #\_ #\c #\o #\l #\o #\n #\_)
    (#\< #\_ #\l #\t #\_)
    (#\> #\_ #\g #\t #\_)
    (#\* #\_ #\s #\t #\a #\r #\_)
    (#\? #\_ #\q #\m #\_)
    (#\@ #\_ #\a #\t #\_)
    (#\! #\_ #\b #\a #\n #\g #\_)
    (#\( #\_ #\l #\p #\a #\r #\e #\n #\_)
    (#\) #\_ #\r #\p #\a #\r #\e #\n #\_)
    (#\_ #\_ #\u #\n #\d #\e #\r #\s #\c #\o #\r #\e #\_))
  "Table with entries (char . char-list) for substituting characters in ~
   filenames.")

(defconst *html-vp* ; see print-doc-string-part1
  '(("BV" "BF") . ("EV" "EF")))

(defun html-string-node-name (pkg-name name)
  (cond
   ((equal pkg-name "KEYWORD")
    (concatenate 'string ":" name))
   (pkg-name
    (concatenate 'string pkg-name "::" name))
   (t name)))

(defun substring (str lower upper)
  (acl2::subseq str lower upper))

(defun html-parse-string (x)

; Returns, for x a symbol-name "PKG:NAME" or "PKG::NAME" the pair (mv "PKG"
; "NAME"), where if PKG is "" then the "PKG" returned is "KEYWORD".

  (let* ((len (length x))
         (posn (position #\: x)))
    (cond
     ((null posn) (mv nil x))
     ((eql posn 0)
      (mv "KEYWORD" (substring x 1 len)))
     (t (mv (substring x 0 posn)
            (substring x
                       (if (eql (char x (+ 1 posn)) #\:)
                           (+ 2 posn)
                         (+ 1 posn))
                       len))))))

(defun html-node-name (x spack)

; If x is a string, we simply return x.

; If x is a symbol then spack is a symbol.  If the symbol-package-names of x
; and agree and are not the keyword package, then we return the symbol-name of
; x.  Otherwise we prepend to that name the symbol-package-name of x followed
; by "::", except that we only prepend ":" if that symbol-package-name is
; "KEYWORD".

  (cond
   ((stringp x)
    x)
   ((symbolp x)
    (let ((name (symbol-name x))
          (pkg-name (acl2::symbol-package-name x)))
      (cond
       ((or (equal pkg-name "KEYWORD")
            (not (eq (acl2::intern-in-package-of-symbol name spack)
                     x)))
        (html-string-node-name pkg-name name))
       (t (html-string-node-name nil name)))))
   (t (acl2::er acl2::hard 'html-node-name
                "Apparent attempt to document topic that is neither a string ~
                 nor a symbol, ~p0."
                x))))

(defun html-node-name-lst (lst spack)
  (if lst
      (cons (html-node-name (car lst) spack)
            (html-node-name-lst (cdr lst) spack))
    nil))

(defun doc-alist1 (raw-doc-alist spack ans)

; Raw-doc-alist is a doc-alist, i.e., a list with entries of the form (name
; section-symbol cites doc).  This function returns a corresponding list with
; entries for which name, section-symbol, and the elements of cites have been
; converted by applying html-node-name.

  (cond
   ((null raw-doc-alist) (reverse ans))
   (t (doc-alist1 (cdr raw-doc-alist)
                  spack
                  (cons (list* (html-node-name (caar raw-doc-alist)
                                               spack)
                               (html-node-name (cadar raw-doc-alist)
                                               spack)
                               (html-node-name-lst (caddar raw-doc-alist)
                                                   spack)
                               (cdddar raw-doc-alist))
                        ans)))))

(defun filter-topics1 (topics doc-alist acc)

; At one time we exploited the "fact" that if every topic's section appears
; earlier in doc-alist than it does, in order to guarantee that we include the
; entire cone underneath a topic.  But this "fact" isn't true, e.g., for
; arrays and aref1.

; This function is presumably a no-op when writing out the full ACL2
; documentation.  But for a subtree of that documentation, or perhaps user-book
; documentation, this function "installs" new top-level sections.  See a
; further comment on this issue in filter-topics.

; !! Should this deal with cites field?

  (cond
   ((null doc-alist)
    (reverse acc))
   ((acl2::member-equal (cadar doc-alist) topics) ; section exists
    (filter-topics1 topics (cdr doc-alist) (cons (car doc-alist) acc)))
   ((acl2::member-equal (caar doc-alist) topics)

; The section does not exist, so the current topic should be viewed as a
; section.

    (filter-topics1 topics
                    (cdr doc-alist)
                    (cons (list* (caar doc-alist)
                                 (caar doc-alist)
                                 (cddar doc-alist))
                          acc)))
   (t (filter-topics1 topics (cdr doc-alist) acc))))

(defun extend-with-immediate-subtopics (topics doc-alist changedp)

; !! Should this deal with cites field?

  (cond
   ((null doc-alist) (mv topics changedp))
   ((acl2::member-equal (caar doc-alist) topics)
    (extend-with-immediate-subtopics topics (cdr doc-alist) changedp))
   ((acl2::member-equal (cadar doc-alist) topics)
    (extend-with-immediate-subtopics (cons (caar doc-alist) topics)
                                     (cdr doc-alist)
                                     t))
   (t (extend-with-immediate-subtopics topics (cdr doc-alist) changedp))))

(defun all-subtopics (topics doc-alist)
  (mv-let (extended-topics changedp)
          (extend-with-immediate-subtopics topics doc-alist nil)
          (if changedp
              (all-subtopics extended-topics doc-alist)
            topics)))

(defun filter-topics (topics doc-alist)

; This function is presumably a no-op when writing out a full documentation
; tree.  But when topics specifies a subtree of that documentation, this
; function "installs" new top-level sections by replacing the section-symbol of
; an entry (name section-symbol cites doc) with name when that section-symbol
; isn't in the transitive downward closure of topics with respect to
; doc-alist.

  (if (null topics)
      doc-alist
    (filter-topics1 (all-subtopics topics doc-alist) doc-alist nil)))

(defun doc-alist (spack topics state)

; Recall that state-global 'documentation-alist is a list with entries of the
; form (name section-symbol cites doc).  This function returns a corresponding
; list with entries for which name, section-symbol, and the elements of cites
; have been converted by applying html-node-name with the indicated spack
; argument, a symbol which symbol-package-name is considered the current
; package for purposes of whether a symbol naming a documentation topic needs a
; package prefix.

   (doc-alist1 (filter-topics
                topics
                (acl2::global-val 'acl2::documentation-alist (acl2::w state)))
               spack
               nil))

(defun version-subdirectory (acl2-version)

; From "ACL2 Version 1.9" we compute "v1-9".  More generally, 
; from "ACL2 Version xxx.yyy/zzz..." we compute "vxxx-yyySzzz..."

  (let* ((expected-initial-str "ACL2 Version ")
         (k (1- (length expected-initial-str))))
    (cond
     ((not (acl2::terminal-substringp acl2-version
                                      expected-initial-str k k))
      (acl2::er acl2::hard 'version-subdirectory
          "State global 'acl2::acl2-version is not of the expected form!"))
     (t (coerce
         (cons #\v
               (coerce
                (acl2::apply-char-subst-table1
                 (cdr (nthcdr k (coerce acl2-version 'list)))
                 nil
                 '((#\. #\-) (#\/ #\S)))
                'list))
         'string)))))

(defconst *html-doc-markup-table*
  '(("-" nil .    "--")
    ("B" nil .  "<b>~st</b>")
    ("BF" nil .  "~%<pre>")
    ("BID" nil .    "")      ;begin implementation dependent
    ("BPAR" nil .  "<p>")
    ("BQ" nil .  "</p>~%<blockquote><p>")
    ("BV" nil .  "~%<pre>")
    ("C" nil .  "<code>~st</code>")
    ("EF" nil .  "</pre>~%")
    ("EID" nil .    "")      ;end implementation dependent
    ("EM" nil .  "<em>~st</em>") ;emphasis
    ("EPAR" nil .  "</p>")
    ("EQ" nil .  "</p></blockquote>~%<p>")
    ("EV" nil .  "</pre>~%")
    ("GIF" nil . "<img src=~st>") ;gif files; e.g., ~gif[\"foo.gif\" align=top]
    ("I" nil .  "<i>~st</i>")
    ("ID" nil .    "")       ;implementation dependent
    ;("IL" t .  "<a href=\"~sc#~sp\">~st</a>")
    ;("ILC" t .  "<code><a href=\"~sc#~sp\">~st</a></code>")
    ;("L" t .  "See <a href=\"~sc#~sp\">~st</a>")
    ("IL" t .  "<a href=\"~sc\">~st</a>")
    ("ILC" t .  "<code><a href=\"~sc\">~st</a></code>")
    ("L" t .  "See <a href=\"~sc\">~st</a>")
    ("NL" nil .  "<br/>~%")
    ("PAR" nil .  "<p/>~%~%")
    ;("PL" t .  "see <a href=\"~sc#~sp\">~st</a>")
    ("PL" t .  "see <a href=\"~sc\">~st</a>")
    ("SC" nil .  "~sT")
    ("ST" nil .  "<strong>~st</strong>") ;strong emphasis
    ("T" nil .  "<tt>~st</tt>")
    ("TERMINAL" nil . "") ; terminal only, ignore
    ("WARN" nil . "<a href=\"~sw\"><img src=twarning.gif></a>")
    ;("CLICK-HERE" t .  "Click <a href=\"~sc#~sp\">here</a>")
    ;("PCLICK-HERE" t .  "click <a href=\"~sc#~sp\">here</a>")
    ("CLICK-HERE" t .  "Click <a href=\"~sc\">here</a>")
    ("PCLICK-HERE" t .  "click <a href=\"~sc\">here</a>")
    ;("FLY" t .  "<a href=\"~sc#~sp\"><img src=flying.gif></a>")
    ;("WALK" t .  "<a href=\"~sc#~sp\"><img src=walking.gif></a>")
    ("FLY" t .  "<a href=\"~sc\"><img src=flying.gif></a>")
    ("LARGE-FLY" t .  "<a href=\"~sc\"><img src=large-flying.gif></a>")
    ("WALK" t .  "<a href=\"~sc\"><img src=walking.gif></a>")
    ("LARGE-WALK" t .  "<a href=\"~sc\"><img src=large-walking.gif></a>")
    ("URL" nil .  "<a href=\"~st\">~st</a>")
    )
  "Table for use in printing documentation strings, when printing to
an html file.  See :DOC markup")

(defun apply-html-subst-table (name anchorp)
  (acl2::apply-char-subst-table
   name
   (if anchorp
       *html-doc-char-subst-table-for-anchors*
     *html-doc-char-subst-table*)
   nil))

(defun apply-filename-subst-table (name)
  (acl2::apply-char-subst-table
   name
   *filename-char-subst-table*
   nil))

(defun write-header (current-name title level channel state)
  (declare (ignore current-name))
  (pprogn (princ$ "<h" channel state)
          (princ$ level channel state)
          (princ$ ">" channel state)
          
          ;(princ$ "<a name = \"" channel state)
          ;(princ$ (apply-html-subst-table current-name t) channel state)
          ;(princ$ "\">" channel state)
          (princ$ (apply-html-subst-table title nil) channel state)
          ;(princ$ "</a>" channel state)
          
          (princ$ "</h" channel state)
          (princ$ level channel state)
          (princ$ ">" channel state)))

(defun write-trailer (html-file index-file channel state)
  (pprogn
   (princ$ "<br><br><br><a href=\"" channel state)
   (princ$ html-file channel state)
   (princ$ "\"><img src=\"llogo.gif\"></a>" channel state)
   (cond ((null index-file) ; then channel is to the index file
          state)
         (t (pprogn
             (princ$ " <a href=\"" channel state)
             (princ$ index-file channel state)
             (princ$ "\"><img src=\"index.gif\"></a>" channel state))))
   (newline channel state)
;   (princ$ "<br><hr><br>" channel state)
; Each of the strings below contains 12 <br>'s, so we're putting out 72 <br>'s
;   (princ$ "<br><br><br><br><br><br><br><br><br><br><br><br>" channel state)
;   (princ$ "<br><br><br><br><br><br><br><br><br><br><br><br>" channel state)
;   (princ$ "<br><br><br><br><br><br><br><br><br><br><br><br>" channel state)
;   (princ$ "<br><br><br><br><br><br><br><br><br><br><br><br>" channel state)
;   (princ$ "<br><br><br><br><br><br><br><br><br><br><br><br>" channel state)
;   (princ$ "<br><br><br><br><br><br><br><br><br><br><br><br>" channel state)
;   (newline channel state)
   (princ$ "</body>" channel state)
   (newline channel state)
   (princ$ "</html>" channel state)
   (newline channel state)))

(defun get-html-filename (name doc-fmt-alist html-file)
  (if (equal name "MAJOR-TOPICS")
      html-file
    (or (cdr (assoc #\c (cdr (assoc-equal name doc-fmt-alist))))
        "nonexistent-acl2-doc-file.html")))

(defun doc-url (name spack html-file undocumented-file state)
  (if (equal name "MAJOR-TOPICS")
      html-file
    (let* ((str (html-node-name name spack))
           (temp (assoc-equal str (acl2::doc-fmt-alist state))))
      (cond
       (temp (acl2::concatenate 'string
                                (cdr (assoc #\c (cdr temp)))
                                ;"#"
                                ;(apply-html-subst-table str t)))
                                ))
       (undocumented-file)
       (t (acl2::er acl2::hard 'doc-url
                    "Nonexistent documentation topic, ~p0 (i.e., ~p1)"
                    name str))))))

(defun doc-url-lst (vars lst spack html-file undocumented-file state)
  (cond
   ((null lst) nil)
   (t (cons (cons (car vars)
                  (doc-url (car lst) spack html-file undocumented-file state))
            (doc-url-lst (cdr vars) (cdr lst) spack html-file undocumented-file
                         state)))))

(defun print-name-as-link
  (name doc-fmt-alist html-file major-topics-file channel state)
  (let ((subst-name (apply-html-subst-table name nil)))
    (if (equal subst-name "MAJOR-TOPICS")
        (pprogn (princ$ "<a href=\"" channel state)
                (princ$ major-topics-file channel state)
                (princ$ "\">" channel state)
                (princ$ "ACL2 Documentation" channel state)
                (princ$ "</a>" channel state))
      (pprogn (princ$ "<a href=\"" channel state)
              (princ$ (get-html-filename name doc-fmt-alist html-file)
                      channel state)
              ;(princ$ "#" channel state)
              ;(princ$ (apply-html-subst-table name t) channel state)
              (princ$ "\">" channel state)
              (princ$ subst-name channel state)
              (princ$ "</a>" channel state)))))

(defun write-doc-menu-item
  (name str html-file major-topics-file enumerate-flg channel state
        undocumented-file)
  (let ((doc-fmt-alist (acl2::doc-fmt-alist state)))
    (pprogn (if enumerate-flg
                (princ$ "<li><h3>" channel state)
              (princ$ "<b>" channel state))
            (print-name-as-link name doc-fmt-alist html-file
                                major-topics-file channel state)
            (princ$ " -- " channel state)
            (acl2::print-doc-string-part 0 str "<br><code>  </code>"
                                         *html-doc-markup-table*
                                         *html-doc-char-subst-table*
                                         doc-fmt-alist
                                         channel
                                         name
                                         nil
                                         undocumented-file
                                         nil
                                         state)
            (if enumerate-flg
                (pprogn
                 (princ$ "</h3>" channel state)
                 (newline channel state)
                 (princ$ "</li>" channel state))
              (princ$ "</b><br><br>" channel state))
            (newline channel state))))

(defun write-doc-menu1
  (lst doc-alist html-file major-topics-file enumerate-flg toc-alist
       channel state undocumented-file)

; Lst is a list of names, each of which is a string.  If toc-alist is non-nil
; here it is the toc-alist, i.e., it contains pairs of the form ("letter"
; . "name"), where "name" is an element of lst.  When toc-alist is non-nil we
; do two unusual things.  First, we print the Letter before we see name,
; dividing the list into sections by letter.  Second, we print a local anchor
; around each letter so the index line at the top of the file can jump to the
; corresponding letter.

  (cond ((null lst) state)
        ((equal (car lst) (cdar toc-alist))
         

; We just entered the section of the index starting with (letter . name), where
; name is (car lst).  We print letter first.

         (pprogn
          (acl2::fms "<BR><BR><H1><A NAME=\"~sa\">~sa</A></H1>~%"
                     (list (cons #\a (caar toc-alist))) channel state nil)
          (write-doc-menu-item (car lst)
                               (cadddr (assoc-equal (car lst) doc-alist))
                               html-file
                               major-topics-file
                               enumerate-flg channel state undocumented-file)
          (newline channel state)
          (write-doc-menu1 (cdr lst) doc-alist html-file major-topics-file
                           enumerate-flg (cdr toc-alist) channel state
                           undocumented-file)))
        ((and (null (cdar toc-alist))
              (acl2::assoc-equal-cdr (car lst) toc-alist))

; The next name to be printed starts a new letter section, but not the next
; one in the toc-alist.  That means the next one in the toc alist is nil (which
; we check above simply to avoid the assoc-equal-cdr when it couldn't possibly
; be true).  We print an empty letter section for this entry.

         (pprogn
          (acl2::fms "<BR><BR><H1>~sa</H1>~%"
                     (list (cons #\a (caar toc-alist))) channel state nil)
          (newline channel state)
          (write-doc-menu1 lst doc-alist html-file major-topics-file
                           enumerate-flg (cdr toc-alist) channel state
                           undocumented-file)))
        (t (pprogn
            (write-doc-menu-item (car lst)
				 (cadddr (assoc-equal (car lst) doc-alist))
                                 html-file
                                 major-topics-file
                                 enumerate-flg channel state
                                 undocumented-file)
	    (newline channel state)
	    (write-doc-menu1 (cdr lst) doc-alist html-file major-topics-file
                             enumerate-flg toc-alist channel state
                             undocumented-file)))))

(defun append0 (x y)
  (if (null y)
      x
    (append x y)))

(defun write-doc-menu
  (doc-tuple doc-alist html-file major-topics-file enumerate-flg index-flg
             channel state undocumented-file)
  "Writes a menu with entries from the list LST of names."
  (cond ((null (caddr doc-tuple)) state)
	(t (let* ((main-subitems
                   (strip-cars (cddddr doc-tuple)))
                  (other-menu-items
                   (if main-subitems
                       (acl2::set-difference-equal
                        (caddr doc-tuple)
                        main-subitems)
                     (caddr doc-tuple))))
             (pprogn (newline channel state)
                     (princ$ "<H2>Some Related Topics</H2>" channel state)
                     (newline channel state)
                     (princ$ "<ul>" channel state)
                     (newline channel state)
                     (write-doc-menu1
                      (acl2::merge-sort-alpha-<
                       (append0 main-subitems other-menu-items))
                      doc-alist html-file major-topics-file
                      enumerate-flg index-flg channel state undocumented-file)
                     (princ$ "</ul>" channel state)
                     (newline channel state) (newline channel state))))))

(defun write-a-doc-section
  (doc-tuple parent-name level doc-alist html-file major-topics-file
             index-file channel state undocumented-file)

; In fact doc-tuple may really be a doc-tree, but that's ok.

  (let ((doc-fmt-alist (acl2::doc-fmt-alist state)))
    (pprogn
     (write-header (car doc-tuple)
                   (cond
                    ((equal parent-name
                            "Pages Written Especially for the Tours")
                     (acl2::get-one-liner-as-string (cadddr doc-tuple)))
                    (t (car doc-tuple)))
                   level channel state)
     (if (equal parent-name "Pages Written Especially for the Tours")
         state
       (acl2::print-doc-string-part 0 (cadddr doc-tuple)
                                    "<code>   </code>"
                                    *html-doc-markup-table*
                                    *html-doc-char-subst-table*
                                    doc-fmt-alist
                                    channel
                                    (car doc-tuple)
                                    t
                                    undocumented-file
                                    nil ; vp is relevant only for :par
                                    state))
     (if (equal parent-name "Pages Written Especially for the Tours")
         state
       (pprogn
        (princ$ "<pre>" channel state)
        (princ$ "Major Section:  " channel state)
        (print-name-as-link parent-name doc-fmt-alist html-file
                            major-topics-file
                            channel state)
        (newline channel state)
        (princ$ "</pre><p/>" channel state)))
     (newline channel state)
     (mv-let
      (ln state)
      (acl2::print-doc-string-part-mv 1 (cadddr doc-tuple) ""
                                      *html-doc-markup-table*
                                      *html-doc-char-subst-table*
                                      doc-fmt-alist
                                      channel
                                      (car doc-tuple)
                                      :par
                                      undocumented-file
                                      *html-vp*
                                      state)
      (pprogn
       (newline channel state)
       (write-doc-menu doc-tuple doc-alist html-file
                       major-topics-file t nil channel state undocumented-file)
       (acl2::print-doc-string-part 2 (cadddr doc-tuple) ""
                                    *html-doc-markup-table*
                                    *html-doc-char-subst-table*
                                    doc-fmt-alist
                                    channel
                                    (car doc-tuple)
                                    ln ; :par or :par-off
                                    undocumented-file
                                    *html-vp*
                                    state)
       (write-trailer html-file index-file channel state))))))

(mutual-recursion

(defun write-doc-tree-lst
  (doc-trees parent-name level doc-alist html-file major-topics-file index-file
             filename-alist state undocumented-file)
  (cond ((null doc-trees) state)
        (t (let ((filename (cdr (assoc-equal (caar doc-trees) filename-alist))))
             (pprogn
              (if filename
                  (pprogn
                   (if (acl2::f-get-global 'doc-tree-channel state)
                       (acl2::close-output-channel
                        (acl2::f-get-global 'doc-tree-channel state)
                        state)
                     state)
                   (mv-let (channel state)
                     (acl2::open-output-channel filename :character
                                                state)
                     (pprogn
                      (princ$ "<html>" channel state)
                      (newline channel state)
                      (princ$ "<head><title>" channel state)
                      (princ$ filename channel state)
                      (princ$ "  --  " channel state)
                      (princ$ (acl2::f-get-global 'acl2::acl2-version state)
                              channel state)
                      (princ$ "</title></head>" channel state)
                      (newline channel state)
                      (princ$ "<body text=#000000 bgcolor=\"#FFFFFF\">"
                              channel state)
                      (newline channel state)
                      (acl2::f-put-global
                       'doc-tree-channel channel state))))
                state)
              (write-doc-tree (car doc-trees)
                              parent-name level doc-alist html-file
                              major-topics-file
                              index-file
                              filename-alist
                              state
                              undocumented-file)
              (write-doc-tree-lst (cdr doc-trees)
                                  parent-name level doc-alist html-file
                                  major-topics-file
                                  index-file
                                  filename-alist state
                                  undocumented-file))))))

(defun write-doc-tree
  (doc-tree parent-name level doc-alist html-file major-topics-file index-file
            filename-alist state undocumented-file)
  (pprogn (write-a-doc-section doc-tree
                               parent-name
                               level
                               doc-alist
                               html-file
                               major-topics-file
                               index-file
                               (acl2::f-get-global 'doc-tree-channel state)
                               state
                               undocumented-file)
          (write-doc-tree-lst (cddddr doc-tree)
                              (car doc-tree)
                              (1+ level)
                              doc-alist
                              html-file major-topics-file index-file
                              filename-alist
                              state
                              undocumented-file)))

)

(defun html-fmt-alist (doc-trees filename filename-alist acc)
  (cond
   ((null doc-trees) acc)
   (t (let ((filename (or (cdr (assoc-equal (caar doc-trees) filename-alist))
                          filename)))
        (if (null filename)
            (acl2::er acl2::hard 'html-fmt-alist "Something wrong here...")
          (html-fmt-alist
           (cdr doc-trees)
           filename
           filename-alist
           (html-fmt-alist
            (cddddr (car doc-trees))
            filename
            filename-alist
            (cons (list (caar doc-trees)
                        (cons #\p (apply-html-subst-table (caar doc-trees) t))

; Here, and below in default-html-fmt-alist, I used to bind #\A, but I now see no
; reason to do so and thus don't.  Also, in reading the comment in lookup-fmt-alist
; in the main source code, I suggest that I need to bind #\s as well as #\p.  But
; again I see no need and so don't.

;                       (cons #\s ... why?)
;                       (cons #\A ... why?)
                        (cons #\c filename))
                  acc))))))))

(defun write-home-page (html-file spack vsubdir major-topics-file index-file
                                  state undocumented-file)

; When this function is called, (acl2::doc-alist state) is set so that doc-url
; can be used to find any ACL2 documentation topic.

  (mv-let
   (n state)
   (acl2::read-idate state)
   (let* ((date-list (acl2::decode-idate n))
          (day (cadddr date-list))
          (month (nth (1- (car (cddddr date-list)))
                      '("January" "February" "March" "April" "May"
                        "June" "July" "August" "September" "October"
                        "November" "December")))
          (yr (+ 1900 (cadr (cddddr date-list))))
          (warn-href
           (cdr (assoc #\w
                       (cdr (assoc-equal ""
                                         (acl2::doc-fmt-alist state)))))))
     (mv-let
      (channel state)
      (acl2::open-output-channel html-file :character state)
      (pprogn
       (acl2::fms
        acl2::*home-page*
        (append
         (list (cons #\0 (acl2::f-get-global 'acl2::acl2-version state))
              (cons #\1 major-topics-file)
              (cons #\2 index-file)
              (cons #\3 vsubdir)
              (cons #\4 month)
              (cons #\5 day)
              (cons #\6 yr)
              (cons #\7 warn-href))
         (doc-url-lst '(#\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m
                        #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z
                        #\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M
                        #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z)
                      acl2::*home-page-references* spack html-file
                      undocumented-file state))
        channel
        state
        nil)
       (newline channel state)
       (acl2::close-output-channel channel state))))))

(defun write-major-topics (doc-trees doc-alist html-file
                                     major-topics-file index-file state
                                     undocumented-file)

  (mv-let
   (channel state)
   (acl2::open-output-channel major-topics-file :character state)
   (pprogn 
    (acl2::fms "<html>~%<head><title>~sv</title></head>~%~
                <body text=#000000 bgcolor=\"#FFFFFF\">~%~
                <h1>Documentation for ~sv<h1>~%~
                <h2>The <a href=\"acl2-doc.html\">ACL2</a> Documentation is ~
                divided into the following Major Topics<h2>"
               (list (cons #\v (acl2::f-get-global 'acl2::acl2-version state)))
               channel state nil)
            
    (princ$ "<ul>" channel state)
    (write-doc-menu1 (strip-cars doc-trees)
                     doc-alist html-file major-topics-file t nil channel state
                     undocumented-file)
    (princ$ "</ul>" channel state)
    (write-trailer html-file index-file channel state)
    (acl2::close-output-channel channel state))))

; Recall that a doc tuple of of the form
; (node-name section-name menu-items doc-string).
; A doc tree is a node of a similar form, extended by children
; (node-name section-name menu-items doc-string . children)
; where each member of children is a doc tree.  In fact section-name
; is the parent:  so, if the node-name in a doc tuple is the same as
; its section-name, we replace the section-name with "MAJOR-TOPICS".
; The top-level doc tree is
; ("MAJOR-TOPICS" nil <top-level-section-names> "The top level node."
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
; appears in ans before we add it, unless section is "MAJOR-TOPICS".  That way, we are
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
; alist is returned in reverse order, so that "MAJOR-TOPICS" is at the front.  We
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

(defun insert-MAJOR-TOPICS-in-doc-alist (doc-alist ans)
  (cond
   ((null doc-alist)
    (reverse ans))
   ((equal (caar doc-alist) (cadar doc-alist))
    (insert-MAJOR-TOPICS-in-doc-alist
     (cdr doc-alist)
     (cons (list* (caar doc-alist) "MAJOR-TOPICS" (cddar doc-alist))
           ans)))
   (t (insert-MAJOR-TOPICS-in-doc-alist (cdr doc-alist)
                               (cons (car doc-alist) ans)))))

(defun top-doc-trees (doc-alist)
  (cdr (car (expand-section-alist
             (sort-section-alist
              (section-alist
               (insert-MAJOR-TOPICS-in-doc-alist doc-alist nil)
               nil)
              nil)
             nil))))

(defun remove1-assoc (key alist)
  (cond
   ((null alist) nil)
   ((eql key (caar alist))
    (cdr alist))
   (t (cons (car alist) (remove1-assoc key (cdr alist))))))

(defun all-doc-topics (doc-trees acc)

; I have found this a handy function to have around, even though in some past
; versions of the code it isn't used.

  (cond
   ((null doc-trees) acc)
   (t (all-doc-topics (cdr doc-trees)
                      (all-doc-topics (cddddr (car doc-trees))
                                      (cons (caar doc-trees) acc))))))


(defun apply-html-subst-table-to-doc-topic-strings (doc-alist ans)
  (cond ((endp doc-alist) ans)
        (t
         (let ((new-name (apply-html-subst-table (car (car doc-alist)) t)))
           (apply-html-subst-table-to-doc-topic-strings
            (cdr doc-alist)
            (cons (if (symbolp new-name) (symbol-name new-name) new-name)
                  ans))))))

(defun find-all-duplicatesp-equal (lst ans)
  (cond ((endp lst) ans)
        ((acl2::member-equal (car lst) (cdr lst))
         (find-all-duplicatesp-equal (cdr lst) (cons (car lst) ans)))
        (t (find-all-duplicatesp-equal (cdr lst) ans))))

(defun chk-uniqueness-after-applying-subst (spack state)
  (let ((anchor-strings
         (apply-html-subst-table-to-doc-topic-strings
          (doc-alist spack nil state)
          nil)))
    (cond
     ((acl2::no-duplicatesp-equal anchor-strings)
      state)
     (t
      (let ((err
             (acl2::er acl2::hard 'acl2::write-html-file
                       "Duplications appear in the list of all ~
                        document topic names after the names are ~
                        converted to strings and ~
                        apply-html-subst-table is applied.  The list ~
                        of all such duplicated strings is ~x0."
                       (find-all-duplicatesp-equal anchor-strings nil))))
        (declare (ignore err))
        state)))))

(defun get-first-char-xcode (str)

; Imagine the alphabet consisting of the letters #\A through #\Z plus the
; "letter" 'SIGNS and the letter 'ACL2-PC::.  The xcode of a normal letter is
; its char-code, e.g., (char-code #\A) = 65, (char-code #\Z)=90.  The xcode of
; SIGNS is 64 and the xcode of ACL2-PC:: is 91.  We say str "starts with"
; ACL2-PC:: if that is the initial substring.  It starts with a sign if it
; doesn't start with ACL2-PC:: or a normal letter.  We return the xcode of the
; extended letter with which it starts.

  (cond ((acl2::string-matchp '(#\A #\C #\L #\2 #\- #\P #\C #\: #\:)
                              str 0 (length str) nil nil)
         91)
        ((member (char str 0)
                 '(#\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M
                   #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z))
         (char-code (char str 0)))
        ((member (char str 0)
                 '(#\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m
                   #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z))
         (char-code (char-upcase (char str 0))))
        (t 64)))

(defun html-filename (filename n)
  (declare (ignore n))
  ;(if (equal filename "-") "_hyphen_.html"
  (if (acl2::string-matchp '(#\-) filename 0 1 nil nil)
      (acl2::concatenate 
       'acl2::string "_hyphen_"
       (apply-filename-subst-table (coerce (cdr (coerce filename 'list)) 
                                           'string))
       ".html")
      (acl2::concatenate
       'acl2::string
       (apply-filename-subst-table filename)
       ".html")))

(defun xcode-char (xcode)

; Given the xcode of an extended character we return the character.  See
; get-first-char-xcode.

  (cond ((= xcode 64) "Signs")
        ((= xcode 91) "ACL2-PC::")
        (t (coerce (list (code-char xcode)) 'string))))

(defun pair-letter-with-entry (xcode lst acc)

; Lst is the alphabetized list of items (strings) in the index.  We assume that
; first in lst are all those items starting with signs, such as "+" and ">=",
; then come the rest in simple alphabetical order, except for those in the
; ACL2-PC package which are last. Each name in lst will be listed somewhere
; in the index and they will occur in the order listed in lst.  Each index
; entry will have an anchor of the same name in this document.  E.g., the entry
; for REWRITE will be embedded in <A NAME="REWRITE">...</A>.  So <A 
; HREF="#REWRITE">R</A> will be a link in this document that will show a
; highlighted "R" and when you click on it you will go to the index entry for
; REWRITE.  Of course, we need an anchor only for the first entry with a
; given first letter, but it is easier to give ourselves an anchor for every
; entry.

  (cond
   ((> xcode 91) (reverse acc))
   ((null lst)
    (pair-letter-with-entry (1+ xcode) nil
                            (cons (cons (xcode-char xcode) nil) acc)))
   (t (let ((xltr (get-first-char-xcode (car lst))))
        (cond
         ((equal xcode xltr)
          (pair-letter-with-entry (1+ xcode) (cdr lst)
                                  (cons (cons (xcode-char xcode)
                                              (car lst))
                                        acc)))
         ((< xcode xltr)
          (pair-letter-with-entry (1+ xcode) lst
                                  (cons (cons (xcode-char xcode) nil) acc)))
         (t (pair-letter-with-entry xcode (cdr lst) acc)))))))
    
(defun write-html-index-toc1 (alist channel state)

; Alist contains entries of the form ("letter" . "name"), where "letter"
; is usually a single character but might be "ACL2-PC::" or the like.

  (cond
   ((null alist)
    (pprogn (newline channel state)
            (newline channel state)))
   ((null (cdar alist))
    (pprogn (princ$ (caar alist) channel state)
            (princ$ " " channel state)
            (write-html-index-toc1 (cdr alist) channel state)))
   (t (pprogn (princ$ "<A HREF=\"#" channel state)
              (princ$ (caar alist) channel state)
              (princ$ "\">" channel state)
              (princ$ (caar alist) channel state)
              (princ$ "</A> " channel state)
              (write-html-index-toc1 (cdr alist) channel state)))))

(defun write-html-index-toc (toc-alist channel state)

; Toc stands for "table of contents".  The idea is to generate a short listing
; of the letters of the alphabet so that when you click on a letter you get
; sent to that part of the index that starts with that letter.  E.g., clicking
; on R will take you to the indexed topics that begin with the letter R.

; The elements of toc-alist are 
; '(("Signs"     . "*STANDARD-CI*")
;   ("A"         . "ACL2-TUTORIAL")
;   ...
;   ("Z"         . "ZERO-TEST-IDIOMS")
;   ("ACL2-PC::" . "ACL2-PC::="))
; where the cadrs are actually the string names of the first entries in
; lst with the given first (extended) character.

  (pprogn
   (princ$ "<pre>" channel state)
   (newline channel state)
   (write-html-index-toc1 toc-alist channel state)
   (princ$ "</pre>" channel state)))

(defun merge-indexed-names (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((acl2::string-matchp '(#\A #\C #\L #\2 #\- #\P #\C #\: #\:)
                              (car l1) 0 (length (car l1)) nil nil)
         (cond
          ((acl2::string-matchp '(#\A #\C #\L #\2 #\- #\P #\C #\: #\:)
                                (car l2) 0 (length (car l2)) nil nil)
           (cond
            ((acl2::alpha-< (car l1) (car l2))
             (cons (car l1) (merge-indexed-names (cdr l1) l2)))
            (t (cons (car l2) (merge-indexed-names l1 (cdr l2))))))
          (t (cons (car l2) (merge-indexed-names l1 (cdr l2))))))
        ((acl2::string-matchp '(#\A #\C #\L #\2 #\- #\P #\C #\: #\:)
                              (car l2) 0 (length (car l2)) nil nil)
         (cons (car l1) (merge-indexed-names (cdr l1) l2)))
        ((acl2::alpha-< (car l1) (car l2))
         (cons (car l1) (merge-indexed-names (cdr l1) l2)))
        (t (cons (car l2) (merge-indexed-names l1 (cdr l2))))))

(defun merge-sort-indexed-names (l)
  (cond ((null (cdr l)) l)
        (t (merge-indexed-names (merge-sort-indexed-names (acl2::evens l))
                                (merge-sort-indexed-names (acl2::odds l))))))

(defun write-html-index
  (index-file html-file major-topics-file doc-alist state undocumented-file)
  (let* ((indexed-names (merge-sort-indexed-names (strip-cars doc-alist)))
         (toc-alist (pair-letter-with-entry 64 indexed-names nil)))
    (mv-let (channel state)
            (acl2::open-output-channel index-file :character state)
            (pprogn (acl2::fms "<html>~%<head><title>~sv</title></head>~%~
                                <body text=#000000 bgcolor=\"#FFFFFF\">~%"
                               (list (cons #\v
                                           (acl2::f-get-global
                                            'acl2::acl2-version
                                            state)))
                               channel state nil)
                    (write-header "Index" "Index" 1 channel state)
                    (newline channel state)
                    (newline channel state)
                    ;; Print description
                    (acl2::fms
                     "This index lists all documented topics in ACL2, arranged ~
                      into sections.  The first section is devoted to those ~
                      whose names begin with signs (and digits), such as ~
                      *STANDARD-CI* and 1+.  Thereafter we have one section ~
                      for each of the 26 letters of the alphabet.  The last ~
                      section is devoted to those topics in the ACL2-PC ~
                      package.  By clicking on the appropriate entry of the ~
                      line below you can go to the corresponding section of ~
                      the index.~%~%You may use Find to search the ~
                      Index.~%~%We also provide an index based on "
                     nil channel state nil)
                    (princ$ "<a href=\"" channel state)
                    (princ$ major-topics-file channel state)
                    (princ$ "\">" channel state)
                    (princ$ "Major Topics" channel state)
                    (princ$ "</a>." channel state)
                    (newline channel state)
                    (write-html-index-toc toc-alist channel state)
                    (write-doc-menu1 indexed-names
                                     doc-alist html-file
                                     major-topics-file nil
                                     toc-alist
                                     channel state undocumented-file)
                    (newline channel state)
                    (newline channel state)
                    (newline channel state)
                    (write-trailer html-file nil channel state)))))

(mutual-recursion

(defun doc-tree-doc-length (doc-tree acc)
  (doc-tree-doc-length-lst (cddddr doc-tree)
                           (+ acc (length (cadddr doc-tree)))))

(defun doc-tree-doc-length-lst (doc-trees acc)
  (cond ((null doc-trees) acc)
        (t (doc-tree-doc-length-lst (cdr doc-trees)
                                    (doc-tree-doc-length (car doc-trees)
                                                         acc)))))

)

#|
;;; No need to maintain these anymore, since every doctopic now has its 
;;; own filename

(defun html-subsection-filename-alist (subsections)
  (if (null subsections)
      nil
      (cons (cons (car subsections) (html-filename (car subsections) 0))
            (html-subsection-filename-alist (cdr subsections)))))

(defun html-section-filename-alist
  (file-root doc-trees acc counter acc-size max-size)

; When acc-size is nil, it means that we're just now entering this function,
; and we should start a new section.

  (declare (xargs :guard (equal file-root file-root)))
  (cond
   ((null doc-trees) (mv counter acc))

   ;;; added November, 2000, when doc topics began being stored in separate
   ;;; filenames. subsections now need to be put in the alist as well.
   ((not (null (caddr (car doc-trees))))
    (html-section-filename-alist
    file-root
    (cdr doc-trees)
    (append (html-subsection-filename-alist (caddr (car doc-trees)))
            (cons (cons (caar doc-trees)
                        (html-filename (caar doc-trees) counter))
                  acc))
    (1+ counter)
    0
    max-size))

   ;;; the following should now always be true, since I'm making max-size -1
   ((or (null acc-size)
        (<= max-size acc-size))
    (html-section-filename-alist
     file-root
     (cdr doc-trees)
     (cons (cons (caar doc-trees)
                 (html-filename (caar doc-trees) counter))
           acc)
     (1+ counter)
     0
     max-size))

   (t
    (html-section-filename-alist
     file-root (cdr doc-trees)
     acc
     counter
     (doc-tree-doc-length (car doc-trees) acc-size)
     max-size))))

(defun html-filename-alist (file-root doc-trees acc counter max-size)
  (declare (xargs :guard (equal file-root file-root)))
  (cond
   ((null doc-trees) acc)
   ((< max-size (doc-tree-doc-length (car doc-trees) 0))
    ;; then create separate files for some sections
    (mv-let (new-counter new-acc)
            (html-section-filename-alist
             file-root
             (cddddr (car doc-trees))
             (cons (cons (caar doc-trees)
                         (html-filename (caar doc-trees) counter))
                   acc)
             (1+ counter)
             nil
             max-size)
            (html-filename-alist
             file-root (cdr doc-trees) new-acc new-counter max-size)))
   (t (html-filename-alist
       file-root
       (cdr doc-trees)
       (cons (cons (caar doc-trees) (html-filename (caar doc-trees) counter))
             acc)
       (1+ counter)
       max-size))))
|#

(defun html-filename-alist (doctopic-names)
  (if (endp doctopic-names)
      nil
      (cons (cons (car doctopic-names)
                  (html-filename (car doctopic-names) 0))
            (html-filename-alist (cdr doctopic-names)))))

(defun default-html-fmt-alist (doc-alist undocumented-filename acc)
  (cond
   ((null doc-alist) acc)
   (t (default-html-fmt-alist
        (cdr doc-alist)
        undocumented-filename
        (cons (list (caar doc-alist)
                    (cons #\p (apply-html-subst-table (caar doc-alist) t))
;                   (cons #\s ... why?)
;                   (cons #\A ... why?)
                    (cons #\c undocumented-filename))
              acc)))))

(defun maybe-write-html-undocumented-file (undocumented-file state)
  (if undocumented-file
      (mv-let (channel state)
              (acl2::open-output-channel undocumented-file :character state)
              (pprogn (princ$ "<h2>Apparently this topic has not been documented.</h2>"
                              channel state)
                      (newline channel state)))
    state))

(defun write-html-file-fn (file-root spack vsubdir topics home-page-p-orig
                                     undocumented-file state)
  (let ((vsubdir
         (or vsubdir
             (version-subdirectory
              (acl2::f-get-global 'acl2::acl2-version state))))
        
        (home-page-p (or home-page-p-orig (null topics)))
        (undocumented-file (if (eq undocumented-file t)
                               (acl2::string-append file-root
                                                    "-undocumented.html")
                             undocumented-file)))
    (acl2::state-global-let*
     ((acl2::fmt-hard-right-margin 500)
      (acl2::fmt-soft-right-margin 480)
      (doc-tree-channel nil))
     (let* ((html-file (acl2::string-append file-root ".html"))
            (major-topics-file
             (acl2::string-append file-root "-major-topics.html"))
            (index-file
             (acl2::string-append file-root "-index.html"))
            (doc-alist (doc-alist spack topics state))
            (doc-trees (top-doc-trees doc-alist))
            (filename-alist
             (html-filename-alist (all-doc-topics doc-alist nil))))
       (pprogn
        (acl2::set-debugger-enable t)
        (chk-uniqueness-after-applying-subst spack state)
        (acl2::fms "Writing html file ~s0, default package ~p1.~%"
                   (list (cons #\0 html-file)
                         (cons #\1 (acl2::symbol-package-name spack)))
                   (acl2::standard-co state) state nil)
        (acl2::state-global-let*
         ((acl2::doc-fmt-alist
           (html-fmt-alist doc-trees nil filename-alist nil)))

; Now we rebind doc-fmt-alist, adding an entry for the empty string.  This
; string is looked up when we handle ~WARN[] (note the empty string inside the
; brackets).  We have to do it this way because we cannot compute the url for
; |A Tiny Warning Sign| until we've set the doc-fmt-alist as above.
; Originally, we tried to replace the two nils above with this singleton
; initial value but the doc-url failed because the doc-fmt-alist it needs was
; nil.

         (pprogn
          (if (acl2::assoc-equal (html-node-name 'ACL2::|A Tiny Warning Sign|
                                                 spack)
                                 (acl2::doc-fmt-alist state))
              (acl2::f-put-global
               'acl2::doc-fmt-alist
               (cons (cons "" ; For use in ~WARN[] when we lookup ""
                           (list
                            (cons #\w
                                  (doc-url 'ACL2::|A Tiny Warning Sign| spack
                                           html-file nil state))))
                     (acl2::doc-fmt-alist state))
               state)
            state)
          (if home-page-p
              (write-home-page html-file
                               spack vsubdir
                               major-topics-file
                               index-file
                               state
                               (and home-page-p-orig undocumented-file))
            state)
          (write-major-topics doc-trees doc-alist html-file
                              major-topics-file
                              index-file
                              state
                              undocumented-file)
          (write-html-index index-file html-file major-topics-file doc-alist
                            state undocumented-file)
          (maybe-write-html-undocumented-file undocumented-file state)
          (write-doc-tree-lst
           doc-trees "MAJOR-TOPICS" 1 doc-alist html-file major-topics-file
           index-file filename-alist state undocumented-file)
          (princ$ " done." (acl2::standard-co state) state)
          (newline (acl2::standard-co state) state)
          (acl2::value :invisible))))))))

(defmacro acl2::write-html-file (&key
                                 (file '"acl2-doc")
                                 (vsubdir 'nil)
                                 (topics 'nil)
                                 (pkg '"ACL2")
                                 (home-page-p 'nil)
                                 undocumented-file)

; This macro dumps the current ACL2 documentation tree, restricted to the
; indicated topics if that parameter is non-nil, in HTML format in the current
; directory.  If you want to dump the entire tree, just execute
; (acl2::write-html-file).

; File specifies the top-level file, which is the ACL2 home page and is written
; only if topics is nil (the default) or home-page-p is t.  In that case,
; vsubdir specifies the version subdirectory, which is set appropriately by
; default when necessary and can probably be ignored by users.

; Topics is nil by default, meaning that every documented topic (including
; those that come documented with ACL2) should be included.  Otherwise, topics
; is a true list of topic names, e.g., '(FOO BAR "MY-PKG").

; The pkg argument is used much like the current package in the LP
; read-eval-print loop, as follows.  Any topic name in that package will
; correspond to itself, without its package prefix.  But a topic name in
; another package will have the package prefix.  For example, if the topic is
; 'BAR::DO-THIS, then the topic name is "BAR::DO-THIS" except that if however
; pkg is "BAR" then the topic name is "DO-THIS".

; If home-page-p and topics are both nil, then we insist that all topics be
; present under the home page.  Set home-page-p explicitly to t to defeat that
; check (in which case links will go to the undocumented-file; see above).

; If undocumented-file is nil, then it is an error when writing out a link to
; an undocumented doc topics.
; Otherwise, undocumented-file is the name of the file to which undocumented
; topics link, where t is an abbreviation for FILE-undocumented.html.

  (list 'write-html-file-fn
        file
        (list 'quote (acl2::pkg-witness pkg))
        vsubdir
        topics
        home-page-p
        undocumented-file
        'state))
