; ACL2 Version 8.0 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2017, Regents of the University of Texas

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
; Url is a url ending in "/", e.g.,
; http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/ .
  (cond ((endp names) nil)
        (t (cons (cons (car chars)
                       (concatenate 'string
                                    url
                                    "index.html?topic="
                                    (symbol-package-name (car names))
                                    "____"
                                    (symbol-name (car names))))
                 (topic-to-url-list url (cdr chars) (cdr names))))))

(defconst *acl2-user-manual*
  "manual/")

(defconst *combined-manual*
  "http://www.cs.utexas.edu/users/moore/acl2/v8-0/combined-manual/")

(defconst *bleeding-edge-manual*
  "http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/")

(defconst *home-page-references*
  '(|The_02Tours|                       ;;; a
    ACL2-Tutorial                       ;;; b
    events                              ;;; c
    programming                         ;;; d
    rule-classes                        ;;; e
    books                               ;;; f
    note-8-0                            ;;; g   ; current release notes
    the-method                          ;;; h
    introduction-to-the-theorem-prover  ;;; i   ; This is not used right now.
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

; During development, "v" might not be used, so that we can link to the talks
; in the "bleeding edge" manual.  At release time we should use this "v" link
; instead.  See "Talks" below.

    talks                               ;;; v
  ))

(defconst *home-page*

; The numeric fmt variables used in the home page are resolved as follows:
; 0 (@ acl2-version)
; 1 *acl2-user-manual*
; 2 *combined-manual*
; 3 *bleeding-edge-manual*
; 4 build date month, e.g., "January"
; 5 build date day, e.g., 8
; 6 build date year, e.g., 1998

; Alphabetic fmt variables used below are defined in the defconst for
; *home-page-references*, immediately following the one for
; *home-page*.

          "~
<HTML>

<HEAD><TITLE>~s0</TITLE></HEAD>

<BODY TEXT=\"#000000\" BGCOLOR=\"#FFFFFF\" STYLE=\"font-family:'Verdana'\">

<TABLE>
<TR>
<TD>
<IMG SRC=\"HTML/acl2-logo-200-134.gif\" ALIGN=LEFT ALT=\"ACL2\">
</TD>
<TD>
<CENTER><H1>~s0</H1></CENTER>

ACL2 is a logic and programming language in which you can model
computer systems, together with a tool to help you prove properties
of those models.  \"ACL2\" denotes
\"<b>A</b> <b>C</b>omputational <b>L</b>ogic for <b>A</b>pplicative
<b>C</b>ommon <b>L</b>isp\".</P>

ACL2 is part of the Boyer-Moore family of provers, for which its authors have
received the 2005 <A HREF=\"http://awards.acm.org/software_system/\">ACM
Software System Award</A>.<P>

</TD>
</TR>
</TABLE>
<HR>

<TABLE CELLPADDING=3 ALIGN=\"center\">

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"~sa\"><IMG SRC=\"HTML/door02.gif\" BORDER=0></A>
</TD>
<TD>
Start Here: <A HREF=\"~sj\">Applications</A>, <A HREF=\"~sv\">Talks</A>, <A HREF=\"~sa\">Tours</A>, and <A HREF=\"~sb\">Tutorials/Demos</A>
</TD>

<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"http://www.cs.utexas.edu/users/moore/acl2/workshops.html\"><IMG SRC=\"HTML/teacher2.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"http://www.cs.utexas.edu/users/moore/acl2/workshops.html\">ACL2
Workshops, UT Seminar, and Course Materials</A>
</TD>
<!--

The Workshops entry was added in place of the FAQ entry.

The FAQ was added in place of the one removed by this comment.

At one time we had a link to the tutorials.  But after the publication
of the first book, we decided that we should encourage people to read the
book rather than do the tutorials, which are not elementary enough.
I think we should write some appropriate tutorials.  Meanwhile, this
entry is left blank.

<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"~sb\"><IMG SRC=\"HTML/teacher2.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"~sb\">Tutorials (for those who have taken the tours)</A>
</TD>
-->

</TR>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html\">
<IMG SRC=\"HTML/doc03.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html\">
Publications about ACL2 and Its Applications</A>
</TD>

<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"#User's-Manual\"><IMG SRC=\"HTML/info04.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"#User's-Manual\">The User's Manuals</A>
and <A HREF=\"http://www.cs.utexas.edu/users/moore/publications/hyper-card.html\">Hyper-Card</A>
</TD>
</TR>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"#Tools\"><IMG SRC=\"HTML/tools3.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"#Tools\">Community Books: Lemma Libraries and Utilities</A>
</TD>

<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"HTML/installation/misc.html#Addresses\"><IMG SRC=\"HTML/mailbox1.gif\"  BORDER=0></A>
</TD>
<TD>
<A HREF=\"HTML/installation/misc.html#Addresses\">Mailing Lists</A>
</TD>
</TR>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"HTML/new.html\">
<IMG SRC=\"HTML/new04.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"HTML/new.html\">
Recent changes to this page</A>
</TD>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"HTML/installation/installation.html\"><IMG SRC=\"HTML/ftp2.gif\"  BORDER=0></A>
</TD>
<TD>
<A HREF=\"HTML/installation/installation.html\">Obtaining, Installing, and License</A>
</TD>

</TR>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"~sg\"><IMG SRC=\"HTML/note02.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"~sg\">Differences from Version 7.4</A><A HREF=\"~sq\"> <IMG
SRC=\"HTML/twarning.gif\"></A>
</TD>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"HTML/other-releases.html\">
<IMG SRC=\"HTML/file04.gif\"  BORDER=0></A>
</TD>
<TD>
<A HREF=\"HTML/other-releases.html\">
Other Releases</A>
</TD>
</TR>

</TABLE>

<BR>
<CENTER>
<B><A HREF=\"mailto:kaufmann@cs.utexas.edu\">Matt Kaufmann</A> and <A HREF=\"mailto:moore@cs.utexas.edu\">J Strother Moore</A></B><BR>
<A HREF=\"http://www.utexas.edu\">University of Texas at Austin</A><BR>
~s4 ~f5, ~f6
</CENTER>

<P>

<HR>

<p>

Welcome to the ACL2 home page!  We highlight a few aspects of ACL2:

<ul>

<li><b>Libraries (Books).</b><br>Libraries of <i>books</i> (files containing
definitions and theorems) extend the code that we have written.  In particular,
the distribution tarball includes the <i>community books</i>, which are
contributed and maintained by the members of the ACL2 community.</li>

<li><b><A NAME=\"documentation\">Documentation</A>.</b><br>There is an
extensive user's manual for the ACL2 system, and an even more comprehensive
manual that documents not only the ACL2 system but also many community books.
See <A HREF=\"#User's-Manual\">below</A> to learn more.</li>

<li><b>License and Copyright.</b><br>ACL2 is freely available under the terms
of the <a href=\"HTML/LICENSE\">LICENSE</a> file distributed with ACL2.  <a
href=\"~st\">License, copyright, and
authorship</a> information is available from the ACL2 <a
href=\"#documentation\">documentation</a>.</li>

<li><b>Extensions.</b><br>The ACL2 distribution includes the following
extensions, which were developed by the individuals shown.  <b>NOTE:</b>Not
included in this list is what was formerly known as \"ACL2(h)\", because it is
now the default build of ACL2: that is, ACL2 builds are now <a
href=\"~sm\">hons-enabled</a>.  Thanks to Bob Boyer, Warren A. Hunt, Jr., Jared
Davis, and Sol Swords for their contributions; see the <a
href=\"~sk\">acknowledgments</a>.

  <UL>
  <LI><A HREF=\"~sl\">ACL2(r)</A><BR>
  Support for the real numbers by way of non-standard analysis<BR>
  Ruben Gamboa</LI>
  <LI><A HREF=\"~sn\">ACL2(p)</A><BR>
  Support for parallel evaluation<BR>
  David L. Rager</LI>
  </UL>

Another extension of ACL2 is the Eclipse-based <A
HREF=\"http://acl2s.ccs.neu.edu/acl2s/doc/\">ACL2 Sedan</A> (ACL2s).  Unlike
the systems above, ACL2s is distributed and maintained by Pete Manolios and his
research group.  ACL2s comes with a standard executable ACL2 image for Windows,
but it also comes with pre-certified community books and an extension of ACL2
with additional features, including extra automation for termination proofs as
well as counterexample generation.

</UL>

<HR>

<BR>
We gratefully acknowledge substantial support from the following.  (These are
included in a much more complete <A href=\"~sk\">acknowledgments page</A>.)
<UL>
<LI>DARPA</LI>
<LI>National Science Foundation
  <UL>
  <LI>This material is based upon work supported by the National Science
      Foundation under Grant Nos. CCF-1526760, CNS-1525472, CCF-1153558,
      EIA-0303609, CNS-0429591, ISS-0417413, CCF-0945316, and CNS-0910913.</LI>
  <LI>Any opinions, findings and conclusions or recomendations expressed in
      this material are those of the authors and do not necessarily reflect the
      views of the National Science Foundation.</LI>
  </UL></LI>
<LI>Advanced Micro Devices, Inc.</LI>
<LI>ForrestHunt, Inc.</LI>
<LI>Rockwell Collins, Inc.</LI>
<LI>Sun Microsystems, Inc.</LI>
</UL>

<HR>

<H2><A NAME=\"User's-Manual\">The User's Manuals</A></H2>

The <i>ACL2 User's Manual</i> is a vast hypertext document.  If you are a
newcomer to ACL2, we do <EM>not</EM> recommend that you wander off into the
full documentation.  Instead start with the <A HREF=\"~sb\">ACL2-TUTORIAL</A>
documentation topic.  Experienced users tend mostly to use the manual as a
reference manual, to look up concepts mentioned in error messages or vaguely
remembered from their past experiences with ACL2.

<P>

The <i>ACL2+Books Manual</i> includes not only the ACL2 User's Manual, but also
documents many of the <A href=\"#Tools\">community books</A> (libraries).  This
manual, which is written by many authors, is thus more extensive than the ACL2
system, and is thus potentially more useful.  With the exception of the first
bulleted link below, links to the manual on this page will all take you to the
ACL2+Books Manual.

<P>

The following links take you to these two manuals.  The manuals can however be
read not only in a Web browser, but in the <A HREF=\"~so\">ACL2-Doc Emacs
browser</A> or by using the ACL2 <CODE><A HREF=\"~sr\">:DOC</A></CODE> command
at the terminal; see the documentation topic, <CODE><A
HREF=\"~ss\">DOCUMENTATION</A></CODE>.

<ul>

<li><A HREF=\"~s2\">ACL2+Books Manual</A> (Version 8.0)</li>

<li><A HREF=\"~s3\">ACL2+Books Manual</A> (for
\"<A HREF=\"HTML/installation/obtaining-and-installing.html#Bleeding-edge\">bleeding edge</A>\" distributions)</li>

<li><A HREF=\"~s1index.html?topic=ACL2____ACL2\">ACL2 User's Manual</A> (Version 8.0)</li>

</ul>

<P>

Once you have installed ACL2, you can browse the ACL2 User's Manual locally by
viewing a copy of this home page under your ACL2 sources directory at
<CODE>doc/home-page.html</CODE> and following the last link shown above; but
first you will need to run the following command in your ACL2 sources
directory.

<pre>
    make DOC ACL2=&lt;path_to_your_ACL2&gt;
</pre>

<P>

Better yet, you can build the ACL2+Books Manual locally, as follows, though
this will likely take longer (perhaps a half hour or more, depending on which
books you have already certified).

<pre>
    cd acl2-sources/books
    # The following uses ccl by default; sbcl is also acceptable.
    make manual ACL2=&lt;path_to_your_ACL2&gt;
</pre>

The resulting ACL2+Books Manual may be accessed by pointing your browser to the
file <code>books/doc/manual/index.html</code> under your ACL2 sources directory.

<P>

<BR><HR><BR>
<H2><A NAME=\"Tools\">Community Books: Lemma Libraries and Utilities, and How to Contribute</A></H2>

A companion to ACL2 is the library of <em>community books</em>, which have
been developed by many users over the years.  These books contain definitions
and theorems that you might find useful in your models and proofs.  In
addition, some books contain ACL2 reasoning or analysis tools built by users.
The <A HREF=\"HTML/installation/installation.html\">installation instructions</A>
explain how to download and install the community books.

<p>

We strongly encourage users to submit additional books and to improve existing
books.  If you have interest in contributing, there is a <a
href=\"~su\">documentation topic to get you started</a>.  You can also visit
the <code><A HREF=\"https://github.com/acl2/acl2\">ACL2 System and
Books</A></code> project page on github (just move past the big list of files
to find descriptive text).  Project members are welcome to edit community
books.  In particular, the community book
<code>books/system/doc/acl2-doc.lisp</code> contains the ACL2 system
documentation, and project members are welcome to improve it.

<p>

We also distribute a few interface
tools.  For these, see the <A
HREF=\"http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html#Utilities\">Utilities</A>
section of <A HREF=
\"http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html\">
Books and Papers about ACL2 and Its Applications</A>.  Some of the
papers mentioned in that collection contain utilities, scripts, or
ACL2 books for the problem domains in question.

<BR><HR><BR>
<H2><A NAME=\"search\">Searching documentation</A></H2>

The web views of <a href=\"#User's-Manual\">The ACL2 User's Manual</a> and <A
HREF=\"http://www.cs.utexas.edu/users/moore/acl2/current/combined-manual/\">ACL2+Books
Manual</a> allow you to search the short strings of the documentation (which
are typically summaries of a line or so).  To search the full content for a
string or regular expression, you may use the Emacs-based <A
HREF=\"manual/index.html?topic=ACL2____ACL2-DOC\">ACL2-Doc browser</A>.

</BODY>
</HTML>
")

(defun write-home-page (channel state url)

; Url is a url ending in "/", e.g.,
; http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/ .

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
              (cons #\1 *acl2-user-manual*)
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

; We formerly supplied *acl2-user-manual* as the following URL.  However, David
; Hardin reported concern over reaching a broken-link page after following the
; link from the release notes (in the *acl2-user-manual*) to note-7-0-books
; (only in the *combined-manual*).  We have thus decided to use the
; *combined-manual* for all topics, in order to avoid such issues.

                                    *combined-manual*)
                   (close-output-channel channel state))))

;; Deleted *home-page* and *home-page-references* from ld.lisp.

