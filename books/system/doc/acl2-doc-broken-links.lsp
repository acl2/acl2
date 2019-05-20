; Copyright (C) 2019, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; To use this file, start up ACL2 and evaluate the following form.

; (ld ; linebreak to avoid any possible confusion by the dependency scanner
;  "system/doc/acl2-doc-broken-links.lsp" :dir :system)

; The output will conclude with an alist that is the intended value of the
; constant *acl2-broken-links-alist*, defined in acl2-doc.lisp.  (Indeed, these
; events were created by modifying a comment originally in that definition.)
; It is then advisable to update *acl2-broken-links-alist* accordingly.

(include-book ; break line to avoid confusing dependency scanner
  "system/doc/acl2-doc" :dir :system)

 (make-event
 ; This make-event form is adapted from acl2-doc-wrap.lisp.

  ;; This constant is used in acl2-manual.lisp to ensure that we are only
  ;; writing the topics from this file.  Because of our use of make-event,
  ;; this will be written into the .cert file.
  (let ((topics (xdoc::get-xdoc-table (w state))))
    `(defconst *acl2-sources-xdoc-topics-prelim*
       ',topics)))

(include-book ; break line to avoid confusing dependency scanner
  "xdoc/importance" :dir :system)

(include-book ; break line to avoid confusing dependency scanner
  "xdoc/save" :dir :system)

(set-state-ok t)
(program)

#!xdoc
(defun my-xtopics (topics state)
; This is largely based on save-json-files in books/xdoc/save-fancy.lisp.
  (b* ((topics0 (force-missing-parents
                 (maybe-add-top-topic
                  (normalize-parents-list
                   (clean-topics topics)))))
       (topics-fal (topics-fal topics0))
       ((mv preproc-topics state)
        (preprocess-transform-topics topics0 topics-fal state))
       ((mv xtopics state)
        (xtopics-from-topics preproc-topics state)))
    (value xtopics)))

(make-event
 (b* #!xdoc (((er xtopics)
              (my-xtopics acl2::*acl2-sources-xdoc-topics-prelim* state))
             (links-fal (make-links-fal xtopics))
             (keys-fal  (make-fast-alist
                         (pairlis$ (make-keys (xtopiclist->names xtopics))
                                   nil)))
             (broken (find-broken-links links-fal keys-fal))
             (names (strip-cars broken)))
     (value `(defconst *acl2-broken-links-mangled-names* ',xdoc::names))))

(defun topic-source-alist (keys all-topics)
  (cond ((endp all-topics) nil)
        (t (let* ((topic (car all-topics))
                  (name (cdr (assoc-eq :name topic)))
                  (key (xdoc::make-key name)))
             (cond ((member-equal key keys)
                    (cons (list name (cdr (assoc-eq :from topic)))
                          (topic-source-alist keys (cdr all-topics))))
                   (t (topic-source-alist keys (cdr all-topics))))))))

; WARNING: Unless doc/top.lisp is certified, the following will build manual/
; under the current directory and will also build
; books/system/doc/rendered-doc-combined.lsp!  (Presumably that could be
; avoided with a little effort.)  Something like the following could work
; instead of the following include-book, but we would need to define more
; packages than just those in books/doc/top.acl2:
; (serialize-read "/Users/kaufmann/acl2/devel/books/centaur/xdoc.sao")
(include-book ; break line to avoid confusing dependency scanner
; This can take awhile (but probably less than a half hour)
 "doc/top" :dir :system)

(defun acl2-broken-links-alist (state)
  (merge-sort-lexorder
   (topic-source-alist *acl2-broken-links-mangled-names*
                       (xdoc::get-xdoc-table (w state)))))

; Finally, compare the value, V, of the following to what is below.  But note
; that V may contain some entries with value "Current Interactive Session",
; which should be replaced with a more appropriate string, e.g., the file
; found by going to the entry's topic in the online combined manual.
(acl2-broken-links-alist state)
