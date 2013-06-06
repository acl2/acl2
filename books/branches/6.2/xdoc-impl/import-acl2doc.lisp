; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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

(in-package "ACL2") ;; So the acl2 topic comes from the acl2 package.
(include-book "write-acl2-xdoc")
(program)

(defdoc broken-link
  ;; Keep topic name in sync with write-acl2-xdoc.lisp
  ":Doc-Section Documentation
Placeholder for undocumented topics~/

This topic is used as a placeholder in XDOC when an imported ACL2
documentation topic (~pl[documentation]) topic, written in the classic
~il[doc-string] format, links to an underfined topic.~/~/")

#||

;; To test broken-link handling, uncomment this and regenerate the manual.  We
;; should be warned about the broken links, and they should take us to the
;; broken-link topic.

(defdoc broken-link-test
  ":Doc-Section broken-link
Test of broken links.  IL: ~il[test-broken-link]. ILC: ~ilc[test-broken-link].
L: ~l[test-broken-link].  PL: ~pl[test-broken-link]~/

This is a silly topic intended to test our linking to missing documentation.

IL: ~il[test-broken-link]
ILC: ~ilc[test-broken-link]
L: ~l[test-broken-link]
PL: ~pl[test-broken-link]~/~/")

||#

; Initial import of acl2 system documentation.  We do this before including any
; books other than the basic portcullis, because we don't want any libraries
; loaded when we import the system-level documentation.
;
; One other minor fixup: In ACL2, a top-level topic has a parent of itself.  We
; change all such top-level topics so that they have a parent of acl2::acl2.

#!XDOC
(progn
  (defun remove-alist-key (key x)
    (cond ((atom x)
           nil)
          ((atom (car x))
           (remove-alist-key key (cdr x)))
          ((equal (caar x) key)
           (remove-alist-key key (cdr x)))
          (t
           (cons (car x) (remove-alist-key key (cdr x))))))

  (defun change-self-parent-to-acl2 (topic)
    (let ((name    (cdr (assoc :name topic)))
          (parents (cdr (assoc :parents topic))))
      (if (member name parents)
          (acons :parents
                 (cons 'acl2::acl2 (remove-equal name parents))
                 (remove-alist-key :parents topic))
        topic)))

  (defun change-self-parents-to-acl2 (topics)
    (if (atom topics)
        nil
      (cons (change-self-parent-to-acl2 (car topics))
            (change-self-parents-to-acl2 (cdr topics)))))

  (defun all-topic-names (topics)
    (if (atom topics)
        nil
      (cons (cdr (assoc :name (car topics)))
            (all-topic-names (cdr topics)))))

  (defun remove-topics-by-name (topics names)
    (cond ((atom topics)
           nil)
          ((member (cdr (assoc :name (car topics))) names)
           (remove-topics-by-name (cdr topics) names))
          (t
           (cons (car topics) (remove-topics-by-name (cdr topics) names)))))

  (make-event
   (mv-let (er val state)
     (time$ (acl2::write-xdoc-alist)
            :msg "; Importing ground-zero acl2 :doc topics: ~st sec, ~sa bytes~%"
            :mintime 1)
     (declare (ignore er val))
     (let* ((topics (acl2::f-get-global 'acl2::xdoc-alist state))
            (topics (change-self-parents-to-acl2 topics))
            (names  (all-topic-names topics)))
       (value `(progn
                 (defconst *acl2-ground-zero-names* ',names)
                 (defconst *acl2-ground-zero-topics* ',topics)))))))

(include-book "../xdoc/base")
(include-book "tools/bstar" :dir :system)

#!XDOC
;; Actually install the ground-zero topics
(table xdoc 'doc

; Something subtle about this is, what do we do if there is both an ACL2 :doc
; topic and an XDOC topic?
;
; Originally we appended the *acl2-ground-zero-topics* to (get-xdoc-table
; world), which meant that built-in ACL2 documentation "won" and overwrote the
; xdoc documentation.  But when I documented the system/io.lisp book, I found
; that this wasn't what I wanted, because it meant stupid tiny little
; placeholder documentation for things like read-char$ was overwriting the much
; nicer XDOC documentation for it.
;
; Arguably we should do some kind of smart merge, but, well, this *is* xdoc
; after all.  So I'm just going to say ACL2 loses, and if someone cares enough
; to come up with something better, power to them.

       (append (get-xdoc-table world)
               *acl2-ground-zero-topics*))

(defxdoc acl2
  :short "Documentation for the <a
  href=\"http://www.cs.utexas.edu/users/moore/acl2\">ACL2 Theorem Prover</a>."
  :long "<p>This is a parent topic for <see topic=\"@(url documentation)\">ACL2
documentation</see> that is written in the classic @(see doc-string)
format.</p>")


#!XDOC
(defmacro import-acl2doc ()
  ;; This is for refreshing the documentation to reflect topics documented in
  ;; libraries.  We throw away any ACL2-system topics that we've already had
  ;; added to the xdoc table.
  `(make-event
    (mv-let (er val state)
      (time$ (acl2::write-xdoc-alist :skip-topics *acl2-ground-zero-names*)
             :msg "~|; Importing acl2 :doc topics: ~st sec, ~sa bytes~%"
             :mintime 1)
      (declare (ignore er val))
      (let* ((topics (acl2::f-get-global 'acl2::xdoc-alist state))
             ;(topics (time$ (remove-topics-by-name topics *acl2-ground-zero-names*)))
             )
        (value `(table xdoc 'doc
                       (append ',topics (get-xdoc-table world))))))))


; see bookdoc.lsp

#!XDOC
(defmacro maybe-import-bookdoc ()
  `(make-event
    (b* (((when (cdr (assoc 'bookdoc-loaded (table-alist 'xdoc (w state)))))
          ;; (cw "~|; Already loaded bookdoc.dat.~%")
          (value `(value-triple :invisible)))
         (path (acl2::extend-pathname *xdoc-impl-dir* "bookdoc.dat" state))
         ((mv channel state) (open-input-channel path :object state))
         ((when (not channel))
          (cw "~|XDOC Note: unable to load bookdoc.dat.  For more complete ~
            documentation, you may wish to run 'make bookdoc.dat' in ~
            acl2/books/xdoc.~%~%")
          (value `(value-triple :invisible)))
         ((mv state new-topics)
          (time$
           ;; bookdoc.lsp always writes the topics relative to the ACL2
           ;; package, so we need to be sure to read them in that way.
           (b* (((mv & & state) (acl2::set-current-package "ACL2" state))
                ((mv & book-topics state)
                 (read-object channel state))
                (state (close-input-channel channel state))
                (curr-topics (get-xdoc-table (w state)))
                (book-names (all-topic-names book-topics))
                (curr-names (all-topic-names curr-topics))
                (dont-want  (intersection-equal book-names curr-names))
                (book-keep  (remove-topics-by-name book-topics dont-want))
                (new-topics (append book-keep curr-topics)))
             (mv state new-topics))
           :msg "~|; Loading bookdoc.dat: ~st sec, ~sa bytes.~%"
           :mintime 1/2)))
      (value `(progn
                (table xdoc 'doc ',new-topics)
                (table xdoc 'bookdoc-loaded t))))))


