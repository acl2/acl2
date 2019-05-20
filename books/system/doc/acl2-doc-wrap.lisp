; acl2-doc-wrap.lisp - Loader for the ACL2 Theorem Prover Documentation
; Copyright (C) 2013 Centaur Technology
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

; acl2-doc-wrap.lisp
;
; This is a trivial wrapper for acl2-doc.lisp.  We:
;
;   - Reset the :from information so that each topic thinks it's from the "ACL2
;     sources" instead of from acl2-doc.lisp.
;
;   - Use make-event to save the whole documentation database into a single
;     constant, so we can just slurp in the thing instead of having to process
;     1500 defxdoc forms at include-book time.
;
; This seems very nice: on one machine at Centaur, we can include-book
; acl2-doc-wrap.lisp in 0.58 seconds, whereas using include-book on
; acl2-doc.lisp takes 2.02 seconds (each of these seem consistent).

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

#!XDOC
(local (table xdoc 'doc nil))
(local (include-book "acl2-doc"))

; Need the following constant non-locally for BROKEN-LINK topic, but the above
; include-book is local:
(make-event
 `(defconst *acl2-broken-links-alist*
    ',*acl2-broken-links-alist*))

; The following are redundant with events acl2-doc.lisp, but necessary for
; render-doc-combined.lisp and probably for building the web-based ACL2-only
; manual, too.

(defconst *acl2-url*

; Warning: This event appears identically in acl2-doc.lisp and
; acl2-doc-wrap.lisp.  If you change one, then change the other the same way!

; We use the specific release rather than "current" in the URL, so that those
; who are looking at an older version of ACL2 will see the corresponding
; ACL2+Books Manual at this link.

  "http://www.cs.utexas.edu/users/moore/acl2/v8-2/")

(defconst *installation-url*

; Warning: This event appears identically in acl2-doc.lisp and
; acl2-doc-wrap.lisp.  If you change one, then change the other the same way!

  (concatenate 'string *acl2-url* "HTML/installation/installation.html"))

(defun combined-manual-ref ()

; Warning: This event appears identically in acl2-doc.lisp and
; acl2-doc-wrap.lisp.  If you change one, then change the other the same way!

  (concatenate
   'string
   "<a href='"
   (concatenate 'string *acl2-url* "combined-manual/index.html") ; url
   "'>"
   "ACL2+Books Manual"
   "</a>"))

(defun clhs (url title)

; Warning: This event appears identically in acl2-doc.lisp and
; acl2-doc-wrap.lisp.  If you change one, then change the other the same way!

  (declare (xargs :guard (and (or (not url)
                                  (stringp url))
                              (stringp title))))
  (concatenate 'string
               "<a href='http://www.lispworks.com/documentation/HyperSpec/"
               (or url "")
               "'>" title "</a>"))

#!XDOC
(local
 (defun change-topic-origins
   (from    ; new origin string to use, e.g., "ACL2 Sources"
    topics  ; list of xdoc topics to modify
    )
   (declare (xargs :mode :program))
   (if (atom topics)
       nil
     (cons (acons :from from (remove1-assoc :from (car topics)))
           (change-topic-origins from (cdr topics))))))

(make-event
 ;; This constant is used in acl2-manual.lisp to ensure that we are only
 ;; writing the topics from this file.  Because of our use of make-event,
 ;; this will be written into the .cert file.
 (let* ((topics (xdoc::get-xdoc-table (w state)))
        (topics (xdoc::change-topic-origins "ACL2 Sources" topics)))
   `(defconst *acl2-sources-xdoc-topics*
      ',topics)))

; This installs the fixed up documentation into the xdoc table, in a way that
; should play nicely with any other books.
(table xdoc::xdoc 'xdoc::doc
       (append (xdoc::get-xdoc-table world)
               *acl2-sources-xdoc-topics*))


;; Tell xdoc where the tours graphics live
(make-event
 (let* ((acl2/          (f-get-global 'acl2-sources-dir state))
        (acl2/graphics/ (extend-pathname acl2/ "graphics" state)))
   (value
    `(xdoc::add-resource-directory "tours" ,acl2/graphics/))))
