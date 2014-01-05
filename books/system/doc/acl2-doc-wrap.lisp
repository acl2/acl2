; acl2-doc-wrap.lisp - Loader for the ACL2 Theorem Prover Documentation
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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

(defconst *combined-manual-url*
  "http://www.cs.utexas.edu/users/moore/acl2/current/combined-manual/")

(defconst *combined-manual-link*
  (concatenate 'string
               "<a href='"
               *combined-manual-url*
               "'>"
               *combined-manual-url*
               "</a>"))

(defun clhs (url title)
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
     (cons (acons :from from (delete-assoc :from (car topics)))
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
