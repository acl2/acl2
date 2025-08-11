; ACL2 Version 8.6 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2024, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

(set-state-ok t)

(program)

(defun topic-to-url-list (url chars names)
; Url is a url ending in "/", e.g.:
; https://acl2.org/doc/
  (cond ((endp names) nil)
        (t (cons (cons (car chars)
                       (concatenate 'string
                                    url
                                    "index.html?topic="
                                    (symbol-package-name (car names))
                                    "____"
                                    (symbol-name (car names))))
                 (topic-to-url-list url (cdr chars) (cdr names))))))

(defconst *combined-manual*
  "https://www.cs.utexas.edu/users/moore/acl2/v8-6/combined-manual/")

(defconst *bleeding-edge-manual*
  "https://acl2.org/doc/")

(defconst *home-page-references*
  '(tours                               ;;; a
    ACL2-Tutorial                       ;;; b
    releases                            ;;; c
    workshops                           ;;; d
    course-materials                    ;;; e
    books                               ;;; f
    note-8-6                            ;;; g   ; current release notes
    the-method                          ;;; h
    git-quick-start                     ;;; i
    interesting-applications            ;;; j
    acknowledgments                     ;;; k
    real                                ;;; l
    hons-enabled                        ;;; m
    parallelism                         ;;; n
    acl2-doc                            ;;; o
    acl2                                ;;; p
    |A_02Tiny_02Warning_02Sign|         ;;; q
    doc                                 ;;; r
    documentation                       ;;; s
    copyright                           ;;; t
    git-quick-start                     ;;; u
    talks                               ;;; v
    start-here                          ;;; w
    publications                        ;;; x
    mailing-lists                       ;;; y
    installation                        ;;; z
  ))

(defconst *home-page*

; The numeric fmt variables used in the home page are resolved as follows:
; 0 (@ acl2-version)
; 1 [unused; formerly pointed to ACL2-only manual]
; 2 *combined-manual*
; 3 *bleeding-edge-manual*
; 4 build date month, e.g., "January"
; 5 build date day, e.g., 8
; 6 build date year, e.g., 1998

; Alphabetic fmt variables used below are defined in the defconst for
; *home-page-references*, immediately following the one for
; *home-page*.

; Thanks to Keshav Kini for providing various enhancements to this page in
; April, 2018, as follows.

; - The top line.  Keshav explains:

;   This DTD (Document Type Declaration) tells visitors' browsers that the
;   ensuing markup is to be interpreted according to the HTML 4.01 Transitional
;   standard.  The DTD will only need to be changed if browsers stop supporting
;   HTML 4.01 Transitional.  That is unlikely to happen in the foreseeable
;   future, and even if it did, at that point the ACL2 website would need to
;   undergo a major rewrite, so we may consider this DTD to be essentially
;   static.

; - The meta tag.  Keshav explains (and acknowledges that this may be too much
;   information, but it seems harmless to include it all here):

;   This <META> tag indicates the MIME type of and character encoding used by
;   the ensuing file, i.e. that it is a plain text file encoded with the UTF-8
;   character encoding and containing HTML markup.

;   This information is usually sent as a "Content-Type" HTTP header by the web
;   server serving the page, but it seems the UTCS web server only provides the
;   MIME type and not the character encoding.  (This is not unreasonable, since
;   it can be impossible to infer this information automatically for some
;   files.)  Therefore we explicitly declare the Content-Type information
;   within the file itself, using the <META> tag.

;   This may seem backwards, since theoretically, one must already know the
;   Content-Type information (in particular the character encoding information)
;   in order to even read the file and find the <META> tag.  However, since
;   many character encodings (including UTF-8) are backwards compatible with
;   ASCII, browsers will typically tentatively begin reading files for which
;   the character encoding is unknown using the ASCII or Latin-1 encodings, and
;   will then switch to the encoding explicitly specified in the file, if any
;   such specification is found.  Often browsers will use some heuristics to
;   guess the correct character encoding if it is not provided.  Some browsers
;   (notably Firefox but not Chrome) also allow the user to select a character
;   encoding from a menu.  Regardless, the W3 Validator complains if the
;   character encoding isn't specified in some way, so it is wise to do so.

; - Most of the ALT tags were missing.  These have been added, almost entirely
;   using the names suggested by Keshav.

; - Keshav also suggested web validation and provided the link at the bottom of
;   the page.  If you click on the associated icon, you should get a response
;   that "This document was successfully checked as HTML 4.01 Transitional!".

;   NOTES:

;   - Validation may require something like the following, which is added near
;     the top (under the META tag, inside <head>..</head>) at release time.

;     <base href="http://www.cs.utexas.edu/users/moore/acl2/current/acl2-doc.html">

;   - Validation probably won't work when you bring up the home page as a file
;     on your local machine.

          "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\" \"http://www.w3.org/TR/html4/loose.dtd\">

<html>

<head>
    <title>~s0</title>
    <meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\">
</head>

<body text=\"#000000\" bgcolor=\"#FFFFFF\" style=\"font-family:'Verdana'\">

<table>
<tr>
<td>
<img src=\"HTML/acl2-logo-200-134.gif\" align=left alt=\"ACL2 logo\">
</td>
<td>
<center><h1>~s0</h1></center>

ACL2 is a logic and programming language in which you can model
computer systems, together with a tool to help you prove properties
of those models.  \"ACL2\" denotes
\"<b>A</b> <b>C</b>omputational <b>L</b>ogic for <b>A</b>pplicative
<b>C</b>ommon <b>L</b>isp\".<p>

ACL2 is part of the Boyer-Moore family of provers, for which its authors have
received the 2005 <a href=\"http://awards.acm.org/software_system/\">ACM
Software System Award</a>.<p>

</td>
</tr>
</table>
<hr>

<table CELLPADDING=3 align=\"center\">

<tr>
<td>&bull;</td>
<td>
<a href=\"~sw\">Start Here</a> (including <a href=\"~sj\">applications</a>, <a href=\"~sv\">talks</a>, <a href=\"~sa\">tours</a>, and <a href=\"~sb\">tutorials/demos</a>)
</td>

<td>&bull;</td>
<td>
<a href=\"~sd\">ACL2
Workshops</a>, <a
href=\"http://www.cs.utexas.edu/users/moore/acl2/seminar/index.html\">UT Seminar</a>,
and <a href=\"~se\">Course Materials</a>
</td>
<!--

The Workshops entry was added in place of the FAQ entry.

The FAQ was added in place of the one removed by this comment.

At one time we had a link to the tutorials.  But after the publication
of the first book, we decided that we should encourage people to read the
book rather than do the tutorials, which are not elementary enough.
I think we should write some appropriate tutorials.  Meanwhile, this
entry is left blank.

<td align=center valign=MIDDLE>
<a href=\"~sb\"><img src=\"HTML/teacher2.gif\" alt=\"teacher icon\" border=0></a>
</td>
<td>
<a href=\"~sb\">Tutorials (for those who have taken the tours)</a>
</td>
-->

</tr>

<tr>
<td>&bull;</td>
<td>
<a href=\"~sx\">
Publications about ACL2 and Its Applications</a>
</td>

<td>&bull;</td>
<td>
<a href=\"#User's-Manual\">The User's Manual</a>
and <a href=\"http://www.cs.utexas.edu/users/moore/publications/hyper-card.html\">Hyper-Card</a>
</td>
</tr>

<tr>
<td>&bull;</td>
<td>
<a href=\"#Tools\">Community Books: Lemma Libraries and Utilities</a>
</td>

<td>&bull;</td>
<td>
<a href=\"~sy\">Mailing Lists</a>
</td>
</tr>

<tr>
<td>&bull;</td>
<td>
<a href=\"HTML/new.html\">
Recent changes to this page</a>
</td>
<td>&bull;</td>
<td>
<a href=\"~sz\">Obtaining, Installing, and License</a>
</td>

</tr>

<tr>
<td>&bull;</td>
<td>
<a href=\"~sg\">Differences from Version 8.5</a><a href=\"~sq\"> <img
src=\"HTML/twarning.gif\" alt=\"tiny warning icon\"></a>
</td>
<td>&bull;</td>
<td>
<a href=\"~sc\">
Other Releases</a>
</td>
</tr>

</table>

<br>
<center>
<b><a href=\"mailto:kaufmann@cs.utexas.edu\">Matt Kaufmann</a> and <a href=\"mailto:moore@cs.utexas.edu\">J Strother Moore</a></b><br>
<a href=\"http://www.utexas.edu\">University of Texas at Austin</a><br>
~s4 ~f5, ~f6
</center>

<p>

<hr>

<p>

Welcome to the ACL2 home page!  We highlight a few aspects of ACL2:

<ul>

<li><b>Libraries (Books).</b><br>Libraries of <i>books</i> (files containing
definitions and theorems) extend the code that we have written.  In particular,
the distribution tarball includes the <i>community books</i>, which are
contributed and maintained by the members of the ACL2 community.</li>

<li><b><a NAME=\"documentation\">Documentation</a>.</b><br>There is an
extensive user's manual that documents the ACL2 system and many community books.
See <a href=\"#User's-Manual\">below</a> to learn more.</li>

<li><b>License and Copyright.</b><br>ACL2 is freely available under the terms
of the <a href=\"HTML/LICENSE\">LICENSE</a> file distributed with ACL2.  <a
href=\"~st\">License, copyright, and
authorship</a> information is available from the ACL2 <a
href=\"#documentation\">documentation</a>.</li>

<li><b>Extensions.</b><br>The ACL2 distribution includes the following
extensions, which were developed by the individuals shown.

  <ul>
  <li><a href=\"~sl\">ACL2(r)</a><br>
  Support for the real numbers by way of non-standard analysis<br>
  Ruben Gamboa</li>
  <li><a href=\"~sn\">ACL2(p)</a><br>
  Support for parallel evaluation<br>
  David L. Rager</li>
  </ul>

Another extension of ACL2 is the Eclipse-based <a
href=\"http://acl2s.ccs.neu.edu/acl2s/doc/\">ACL2 Sedan</a> (ACL2s).  Unlike
the systems above, ACL2s is distributed and maintained by Pete Manolios and his
research group.  ACL2s comes with a standard executable ACL2 image for Windows,
but it also comes with pre-certified community books and an extension of ACL2
with additional features, including extra automation for termination proofs as
well as counterexample generation.

</ul>

<hr>

<br>
We gratefully acknowledge substantial support from the sources listed in
the <a href=\"~sk\">ACL2 acknowledgments page</a>.

<hr>

<H2><a NAME=\"User's-Manual\">The User's Manual</a></H2>

The <i>ACL2+Books User's Manual</i> is a vast hypertext document.  If you are a
newcomer to ACL2, we do <EM>not</EM> recommend that you wander off into the
full documentation.  Instead start with the <a href=\"~sw\">START-HERE</a>
documentation topic.  Experienced users tend mostly to use the manual as a
reference manual, to look up concepts mentioned in error messages or vaguely
remembered from their past experiences with ACL2.

<p>

That manual not only includes documentation for the ACL2 system, but also
documents many of the <a href=\"#Tools\">community books</a> (libraries).  This
manual, which is written by many authors, is thus more extensive than the ACL2
system, and is thus potentially more useful.  With the exception of the first
bulleted link below, links to the manual on this page will all take you to the
ACL2+Books Manual.

<p>

The following links take you to versions of the manual, which can be
read not only in a Web browser, but also in the <a href=\"~so\">ACL2-Doc Emacs
browser</a> or by using the ACL2 <CODE><a href=\"~sr\">:DOC</a></CODE> command
at the terminal.  See the documentation topic, <CODE><a
href=\"~ss\">DOCUMENTATION</a></CODE>.

<ul>

<li><a href=\"~s2\">ACL2+Books Manual</a> (Version 8.6)</li>

<li><a href=\"~s3\">ACL2+Books Manual</a> (for
<a href=\"~si\">GitHub</a> distributions)</li>

</ul>

<p>

You can build the ACL2+Books Manual locally, as follows, though this will
likely take several minutes or even considerably longer, depending on which
books you have already certified).

<pre>
    cd acl2-sources/books
    # The following uses ccl by default; sbcl is also acceptable.
    make manual ACL2=&lt;path_to_your_ACL2&gt;
</pre>

The resulting ACL2+Books Manual may be accessed by pointing your browser to the
file <code>books/doc/manual/index.html</code> under your ACL2 sources directory.

<p>

<br><hr><br>
<H2><a NAME=\"Tools\">Community Books: Lemma Libraries and Utilities, and How to Contribute</a></H2>

A companion to ACL2 is the library of <em>community books</em>, which have been
developed by many users over the years.  These books contain definitions and
theorems that you might find useful in your models and proofs.  In addition,
some books contain ACL2 tools built by users to help with reasoning,
programming, interfaces, debugging, and testing; see <a
href='http://www.cs.utexas.edu/users/moore/acl2/v8-6/combined-manual/index.html'>
the documentation</a>.  Some relevant papers may be found by following links in
the pages on <a href='~sx'> Books and Papers about ACL2 and Its
Applications</a> and the <a href='~sd'>ACL2 Workshops Series</a>.  The <a
href=\"~sz\">installation instructions</a> explain how to download and install
the community books.

<p>

We strongly encourage users to submit additional books and to improve existing
books.  If you have interest in contributing, there is a <a
href=\"~su\">documentation topic to get you started</a>.  You can also visit
the <code><a href=\"https://github.com/acl2/acl2\">ACL2 System and
Books</a></code> project page on github (just move past the big list of files
to find descriptive text).  Project members are welcome to edit community
books.  In particular, the community book
<code>books/system/doc/acl2-doc.lisp</code> contains the ACL2 system
documentation, and project members are welcome to improve it.

<p>

(Prior to ACL2 Version 7.0 (January, 2015) books were <a
href='http://acl2.org/books-pre-7.0/'>distributed through a different
mechanism</a>.)

<br><hr><br>
<H2><a NAME=\"search\">Searching documentation</a></H2>

The web views of the <a
href=\"http://www.cs.utexas.edu/users/moore/acl2/current/combined-manual/\">ACL2+Books
Manual</a> allow you to search the short strings of the documentation (which
are typically summaries of a line or so).  To search the full content for a
string or regular expression, you may use the Emacs-based <a
href=\"~so\">ACL2-Doc browser</a>.

<br><br>
<hr>
<p><a href=\"https://validator.w3.org/check?uri=referer\"><img src=\"https://www.w3.org/Icons/valid-html401\" alt=\"Valid HTML 4.01 Transitional\" HEIGHT=\"31\" WIDTH=\"88\"></a></p>

</body>
</html>
")

(defun write-home-page (channel state url)

; Url is a url ending in "/", e.g.:
; https://acl2.org/doc/

  (mv-let
   (n state)
   (read-idate state)
   (let* ((date-list (decode-idate n))
          (day (cadddr date-list))
          (month (nth (1- (car (cddddr date-list)))
                      '("January" "February" "March" "April" "May"
                        "June" "July" "August" "September" "October"
                        "November" "December")))
          (yr (+ 1900 (cadr (cddddr date-list)))))
     (pprogn
      (fms
       *home-page*
       (append
        (list (cons #\0 (f-get-global 'acl2-version state))
              ;; (cons #\1 *acl2-user-manual*)
              (cons #\2 *combined-manual*)
              (cons #\3 *bleeding-edge-manual*)
              (cons #\4 month)
              (cons #\5 day)
              (cons #\6 yr))
        (topic-to-url-list
         url
         '(#\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m
           #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z
           #\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M
           #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z)
         *home-page-references*))
       channel
       state
       nil)
      (newline channel state)))))

(defmacro write-home-page-top ()
  '(mv-let (channel state)
           (open-output-channel "home-page.html" :character state)
           (pprogn (set-fmt-hard-right-margin 10000 state)
                   (set-fmt-soft-right-margin 10000 state)
                   (observation 'top-level "Writing home-page.html.")
                   (write-home-page channel
                                    state
                                    *combined-manual*)
                   (close-output-channel channel state))))

;; Deleted *home-page* and *home-page-references* from ld.lisp.

