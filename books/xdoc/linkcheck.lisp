; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "importance") ;; horrible, piggy-back on xtopics because it's easy
(set-state-ok t)
(program)


; (LINKCHECK XTOPICS) --> PAGE
;
; This is a tool for noticing when XDOC links to external web sites become
; broken.  To actually do this, we would need to connect to web sites and parse
; their HTTP responses.  That's nothing we want to try to do in ACL2, of course.
;
; Instead, we are just going to create a very basic web page (which here we
; just return as a string).  The idea is that this web page will summarize all
; of the external links pointing out of each topic.  We can then hand this page
; to an off-the-shelf link checking program.

(defun lc-collect
  (tokens   ; Tokenized version of the post-preprocessing XML
   urls-acc ; Accumulator for the link URLs, a string-listp.
   context  ; Topic name, just for warnings
   )
  "Returns ACC"
  (b* (((when (atom tokens))
        urls-acc)
       (tok1 (car tokens))
       ((unless (opentok-p tok1))
        (lc-collect (cdr tokens) urls-acc context))

       ((when (equal (opentok-name tok1) "a"))
        (b* ((url (cdr (assoc-equal "href" (opentok-atts tok1))))
             ((unless (stringp url))
              (and (xdoc-verbose-p)
                   (cw "; XDOC Warning: In ~x0: <a> with no href='...' part~%"
                       context))
              (lc-collect (cdr tokens) urls-acc context)))
          (lc-collect (cdr tokens)
                      (cons url urls-acc)
                      context)))

       ((when (or (equal (opentok-name tok1) "img")
                  (equal (opentok-name tok1) "icon")))
        (b* ((url (cdr (assoc-equal "src" (opentok-atts tok1))))
             ((unless (stringp url))
              (and (xdoc-verbose-p)
                   (cw "; XDOC Warning: In ~x0: <~s1> with no src='...' part~%"
                       context (opentok-name tok1)))
              (lc-collect (cdr tokens) urls-acc context)))
          (lc-collect (cdr tokens)
                      (cons (str::cat "images/" url) urls-acc)
                      context))))

    (lc-collect (cdr tokens) urls-acc context)))

(defun lc-print-links
  (urls     ; list of urls (strings) we collected
   rchars   ; reverse characters for the page we're writing
   )
  (b* (((when (atom urls))
        rchars)
       (rchars (str::printtree-rconcat "<li><a href=\"" rchars))
       ;; We shouldn't need to encode the URL, because right now it's just the
       ;; raw text from the href='...' part that the user wrote, so it *should*
       ;; already be a valid URL.  BOZO could add a check and warn about this.
       (rchars (str::printtree-rconcat (car urls) rchars))
       (rchars (str::printtree-rconcat "\">" rchars))
       (rchars (simple-html-encode-chars (explode (car urls)) rchars))
       (rchars (str::printtree-rconcat "</a></li>" rchars))
       (rchars (cons #\Newline rchars)))
    (lc-print-links (cdr urls) rchars)))

#||
(str::rchars-to-string
 (lc-print-links '("foo" "bar" "baz") nil))
||#

(defun lc-collect-xtopic
  (xtopic  ; already pre-processed page to gather external links from
   rchars  ; characters for the page we're writing, in reverse order
   )
  ;; returns rchars
  (b* (((xtopic xtopic) xtopic)

       (urls-acc nil)
       (urls-acc (lc-collect xtopic.short-tokens urls-acc (list xtopic.name :short)))
       (urls-acc (lc-collect xtopic.long-tokens urls-acc (list xtopic.name :long)))
       ((unless urls-acc)
        ;; No external links from this topic, don't do anything
        rchars)

       (rchars (str::printtree-rconcat "<p>External links from <b>" rchars))
       (rchars (file-name-mangle xtopic.name rchars))
       (rchars (str::printtree-rconcat "</b></p>" rchars))
       (rchars (cons #\Newline rchars))
       (rchars (str::printtree-rconcat "<ul>" rchars))
       (rchars (cons #\Newline rchars))
       (rchars (lc-print-links (mergesort urls-acc) rchars))
       (rchars (str::printtree-rconcat "</ul>" rchars))
       (rchars (cons #\Newline rchars)))
    rchars))

(defun lc-collect-xtopics (xtopics rchars)
  (b* (((when (atom xtopics))
        rchars)
       (rchars (lc-collect-xtopic (car xtopics) rchars)))
    (lc-collect-xtopics (cdr xtopics) rchars)))

(defun linkcheck (xtopics)
  "Returns the contents of the linkcheck page as a string."
  (b* ((rchars nil)
       (rchars (str::printtree-rconcat
"<html>
<head>
<title>XDOC Link Check</title>
</head>
<body>

<h3>XDOC Link Check</h3>

<p>This is a single web page with the collected external links from your XDOC
topics.  The purpose of this page is to serve as easy way to run an
off-the-shelf link checking program such as.  There are any number of link
checking programs.  You might try:</p>

<ul>

<li>(Firefox) The <a
href=\"https://addons.mozilla.org/en-US/firefox/addon/linkchecker/\">LinkChecker</a>
Addon seems very nice; it just goes through the page you're viewing and turns
good links green.</li>

<li>(Perl) The <a
href=\"http://search.cpan.org/~scop/W3C-LinkChecker-4.81/\">W3C::LinkChecker</a>
Perl module comes with a command-line <a
href=\"http://search.cpan.org/~scop/W3C-LinkChecker-4.81/bin/checklink.pod\">checklink</a>
program.  Installation was just <tt>cpanm W3C::LinkChecker</tt>, and running it
was just <tt>checklink linkcheck.html</tt>.  Unfortunately it respects
<tt>robots.txt</tt>, so it fails to verify many links.</li>

<li>(Ruby) <a href='https://github.com/oscardelben/rawler'>Rawler</a> was easy
to install with <tt>gem install rawler</tt>.  It couldn't process a local file,
so I had to copy my <tt>linkcheck.html</tt> file to the web server and then run
<tt>rawler http://.../linkcheck.html</tt>.  Aside from not following FTP links,
it seemed to work well.</li>

</ul>

<p>There are way more programs than this that check links, so if you can't
easily install the above or don't like them, you might try your operating
system's package manager.</p>

<h3>Links From Each Topic</h3>

" rchars))
       (rchars (lc-collect-xtopics xtopics rchars))
       (rchars (str::printtree-rconcat "
</body>
</html>
" rchars)))
    (str::printtree->str rchars)))


