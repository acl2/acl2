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

; save.lisp
;
; This file defines the XDOC functions for running the preprocessor and saving
; XML files.  Note that the save-topics command we introduce cannot actually be
; used unless the oslib/mkdir book is loaded first.  This is automatically
; handled by the "save" macro in top.lisp.

(in-package "XDOC")
(include-book "prepare-topic")
(include-book "oslib/catpath" :dir :system)
(include-book "oslib/copy-logic" :dir :system)
(include-book "oslib/rmtree-logic" :dir :system)
(set-state-ok t)
(program)

(defun clean-topics-aux (x seen-fal)
  ;; Remove topics we've already seen.
  (b* (((when (atom x))
        (fast-alist-free seen-fal)
        nil)
       (topic1 (car x))
       (name1  (cdr (assoc :name topic1)))
       (lookup (hons-get name1 seen-fal))
       ((when (and lookup
                   ;; Special hack: don't bother reporting that we're dropping
                   ;; something that is literally identical to what we've seen
                   ;; before.
                   (not (equal topic1 (cdr lookup)))))
        (cw "~|WARNING: dropping shadowed topic for ~x0.~%" name1)
        (clean-topics-aux (cdr x) seen-fal))
       (seen-fal (hons-acons name1 topic1 seen-fal)))
    (cons topic1 (clean-topics-aux (cdr x) seen-fal))))

(defun clean-topics (x)
  (clean-topics-aux x (len x)))

; --------------------- File Copying ----------------------------

;; (defun stupid-copy-file-aux (in out state)

;; ; In, out are channels.  Copy from in to out, one byte at a time.

;;   (b* (((mv byte state) (read-byte$ in state))
;;        ((unless byte)
;;         state)
;;        (state (write-byte$ byte out state)))
;;     (stupid-copy-file-aux in out state)))

;; (defun stupid-copy-file (src dest state)

;; ; A stupid file copy routine, so we can copy our style files, etc.  We avoid
;; ; using "system" because of memory problems with forking on huge images.

;;   (b* (((mv in state)  (open-input-channel src :byte state))
;;        ((mv out state) (open-output-channel dest :byte state))
;;        (state          (stupid-copy-file-aux in out state))
;;        (state          (close-input-channel in state))
;;        (state          (close-output-channel out state)))
;;       state))

;; (defun stupid-copy-files (srcdir filenames destdir state)
;;   (b* (((when (atom filenames))
;;         state)
;;        (srcfile  (oslib::catpath srcdir (car filenames)))
;;        (destfile (oslib::catpath destdir (car filenames)))
;;        (state    (stupid-copy-file srcfile destfile state)))
;;     (stupid-copy-files srcdir (cdr filenames) destdir state)))



; ---------------- Hierarchical Index Generation ----------------

(defun normalize-parents (x)

; Given an xdoc entry, remove duplicate parents and self-parents.

  (let* ((name    (cdr (assoc :name x)))
         (parents (cdr (assoc :parents x)))
         (orig    parents)
         (parents (if (member-equal name parents)
                      (prog2$
                       (cw "; xdoc note: removing self-referencing :parents entry for ~x0.~%" name)
                       (remove-equal name parents))
                    parents))
         (parents (if (no-duplicatesp-equal parents)
                      parents
                    (prog2$
                     (cw "; xdoc note: removing duplicate :parents for ~x0.~%" name)
                     (remove-duplicates-equal parents)))))
    (if (equal parents orig)
        x
      (acons :parents parents x))))

(defun force-missing-parents (all-topics)
  ;; Assumes the topics have been normalized.
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        nil)
       (topic   (car all-topics))
       (name    (cdr (assoc :name topic)))
       (parents (cdr (assoc :parents topic)))
       ((when (or (equal name 'acl2::top)
                  (consp parents)))
        (cons topic (force-missing-parents (cdr all-topics))))
       (- (cw "Missing parents: forcing ~x0 to be a child of ~x1.~%" name 'missing-parents))
       (new-topic
        (cons (cons :parents '(missing-parents))
              topic)))
    (cons new-topic (force-missing-parents (cdr all-topics)))))

(defun normalize-parents-list (x)

; Clean up parents throughout all xdoc topics.

  (if (atom x)
      nil
    (cons (normalize-parents (car x))
          (normalize-parents-list (cdr x)))))

(defun maybe-add-top-topic (all-topics)

; We do it this way, rather than starting off with a top topic built in, to
; ensure that the user's choice of a top topic wins.

  (if (find-topic 'acl2::top all-topics)
      all-topics
    (cons
     (list (cons :name 'acl2::top)
           (cons :base-pkg (acl2::pkg-witness "ACL2"))
           (cons :parents nil)
           (cons :short "XDOC Manual -- Top Topic")
           (cons :long "<p>This is the default top topic for an @(see xdoc)
           manual.</p>

<p>You may wish to customize this page.  The usual way to do this is to issue
an @(see xdoc::defxdoc) command immediately before your @(see xdoc::save)
command, along the following lines:</p>

@({
    (defxdoc acl2::top
      :short \"your short text here\"
      :long \"your long description here.\")
})

<p>Your topic should then automatically overwrite this default page.</p>")
           (cons :from "[books]/xdoc/save-classic.lisp"))
     all-topics)))

(defun find-roots (x)

; Gather names of all doc topics which have no parents.

  (if (atom x)
      nil
    (if (not (cdr  (assoc :parents (car x))))
        (cons (cdr (assoc :name (car x)))
              (find-roots (cdr x)))
      (find-roots (cdr x)))))

(defun find-orphaned-topics-1 (child parents topics-fal acc)
  ;; Returns an alist of (CHILD . MISSING-PARENT)
  (cond ((atom parents)
         acc)
        ((hons-get (car parents) topics-fal)
         (find-orphaned-topics-1 child (cdr parents) topics-fal acc))
        (t
         (find-orphaned-topics-1 child (cdr parents) topics-fal
                                 (cons (cons child (car parents))
                                       acc)))))

(defun find-orphaned-topics (x topics-fal acc)
  (b* (((when (atom x))
        acc)
       (child   (cdr (assoc :name (car x))))
       (parents (cdr (assoc :parents (car x))))
       (acc     (find-orphaned-topics-1 child parents topics-fal acc)))
    (find-orphaned-topics (cdr x) topics-fal acc)))


;; (mutual-recursion

;;  (defun make-hierarchy-aux (path dir topics-fal index-pkg all id expand-level acc state)

;; ; - Path is our current location in the hierarchy, and is used to avoid loops.
;; ;   (The first element in path is the current topic we are on.)
;; ;
;; ; - Index-pkg is just used for symbol printing.
;; ;
;; ; - All is the list of all xdoc documentation topics.
;; ;
;; ; - ID is a number that we assign to this topic entry for hiding with
;; ;   JavaScript.  (We don't use names because the topics might be repeated under
;; ;   different parents).
;; ;
;; ; - Expand-level is how deep to expand topics, generally 1 by default.
;; ;
;; ; - Acc is the character list we are building.
;; ;
;; ; We return (MV ACC-PRIME ID-PRIME STATE)

;;    (b* ((name     (car path))
;;         (id-chars (list* #\t #\o #\p #\i #\c #\- (explode-atom id 10)))
;;         (depth    (len path))
;;         (children (find-children name all))
;;         (kind     (cond ((not children) "leaf")
;;                         ((< depth expand-level) "show")
;;                         (t "hide")))

;;         ((when    (member-equal name (cdr path)))
;;          (prog2$
;;           (er hard? 'make-hierarchy "Circular topic hierarchy.  Path is ~x0.~%" path)
;;           (mv acc id state)))

;;         (topic (find-topic name all))
;;         (short    (cdr (assoc :short topic)))
;;         (base-pkg (cdr (assoc :base-pkg topic)))

;;         (acc (str::revappend-chars "<hindex topic=\"" acc))
;;         (acc (file-name-mangle name acc))
;;         (acc (str::revappend-chars "\" id=\"" acc))
;;         (acc (revappend id-chars acc))
;;         (acc (str::revappend-chars "\" kind=\"" acc))
;;         (acc (str::revappend-chars kind acc))
;;         (acc (str::revappend-chars "\">" acc))
;;         (acc (cons #\Newline acc))

;;         (acc (str::revappend-chars "<hindex_name>" acc))
;;         (acc (sym-mangle-cap name index-pkg acc))
;;         (acc (str::revappend-chars "</hindex_name>" acc))
;;         (acc (cons #\Newline acc))

;;         (acc (str::revappend-chars "<hindex_short id=\"" acc))
;;         (acc (revappend id-chars acc))
;;         (acc (str::revappend-chars "\">" acc))
;;         ((mv acc state) (preprocess-main short name dir topics-fal nil base-pkg state acc))
;;         (acc (str::revappend-chars "</hindex_short>" acc))

;;         (acc (str::revappend-chars "<hindex_children id=\"" acc))
;;         (acc (revappend id-chars acc))
;;         (acc (str::revappend-chars "\" kind=\"" acc))
;;         (acc (str::revappend-chars kind acc))
;;         (acc (str::revappend-chars "\">" acc))
;;         (acc (cons #\Newline acc))

;;         (id   (+ id 1))
;;         ((mv acc id state)
;;          (make-hierarchy-list-aux children path dir topics-fal index-pkg all id expand-level acc state))
;;         (acc (str::revappend-chars "</hindex_children>" acc))
;;         (acc (str::revappend-chars "</hindex>" acc))
;;         (acc (cons #\Newline acc)))
;;        (mv acc id state)))

;;  (defun make-hierarchy-list-aux (children path dir topics-fal index-pkg all id expand-level acc state)

;; ; - Children are the children of this path.
;; ; - Path is our current location in the hierarchy.

;;    (if (atom children)
;;        (mv acc id state)
;;      (b* (((mv acc id state)
;;            (make-hierarchy-aux (cons (car children) path) dir topics-fal index-pkg all id
;;                                expand-level acc state))
;;           ((mv acc id state)
;;            (make-hierarchy-list-aux (cdr children) path dir topics-fal index-pkg all id
;;                                     expand-level acc state)))
;;          (mv acc id state)))))


;; (defun save-hierarchy (x dir topics-fal index-pkg expand-level state)

;; ; X is all topics.  We assume all parents are normalized.

;;   (b* ((roots (mergesort (find-roots x)))
;;        (acc   nil)
;;        (acc   (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
;;        (acc   (cons #\Newline acc))
;;        (acc   (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xml-topic-index.xsl\"?>" acc))
;;        (acc   (cons #\Newline acc))
;;        (acc   (str::revappend-chars *xml-entity-stuff* acc))
;;        (acc   (str::revappend-chars "<page>" acc))
;;        (acc   (cons #\Newline acc))
;;        (acc   (str::revappend-chars "<hindex_root>" acc))
;;        (acc   (cons #\Newline acc))
;;        ((mv acc & state) (make-hierarchy-list-aux roots nil dir topics-fal index-pkg x 0
;;                                                   expand-level acc state))
;;        (acc   (str::revappend-chars "</hindex_root>" acc))
;;        (acc   (cons #\Newline acc))
;;        (acc   (str::revappend-chars "</page>" acc))
;;        (acc   (cons #\Newline acc))
;;        (filename (oslib::catpath dir "topics.xml"))
;;        ((mv channel state) (open-output-channel filename :character state))
;;        (state (princ$ (str::rchars-to-string acc) channel state))
;;        (state (close-output-channel channel state)))
;;       state))



;; (defun save-index (x dir topics-fal index-pkg state)

;; ; Write index.xml for the whole list of all topics.

;;   (b* ((acc nil)
;;        (acc (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
;;        (acc (cons #\Newline acc))
;;        (acc (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xml-full-index.xsl\"?>" acc))
;;        (acc (cons #\Newline acc))
;;        (acc   (str::revappend-chars *xml-entity-stuff* acc))
;;        (acc (str::revappend-chars "<page>" acc))
;;        (acc (cons #\Newline acc))
;;        ((mv acc state) (index-topics x "Full Index" dir topics-fal index-pkg state acc))
;;        (acc (str::revappend-chars "</page>" acc))
;;        (filename (oslib::catpath dir "index.xml"))
;;        ((mv channel state) (open-output-channel filename :character state))
;;        (state (princ$ (str::rchars-to-string acc) channel state))
;;        (state (close-output-channel channel state)))
;;       state))




; -------------------- Making Topic Pages -----------------------

;; (defun save-topic (x all-topics dir topics-fal state)
;;   (b* ((name               (cdr (assoc :name x)))
;;        (-                  (cw "Saving ~s0::~s1.~%" (symbol-package-name name) (symbol-name name)))
;;        ((mv text state)    (preprocess-topic x all-topics dir topics-fal
;;                                              nil ;; leave autolinking enabled
;;                                              state))
;;        (filename           (str::cat (str::rchars-to-string
;;                                       (file-name-mangle name nil))
;;                                      ".xml"))
;;        (fullpath           (oslib::catpath dir filename))
;;        ((mv channel state) (open-output-channel fullpath :character state))
;;        (state              (princ$ text channel state))
;;        (state              (close-output-channel channel state)))
;;       state))

;; (defun save-topics-aux (x all-topics dir topics-fal state)
;;   (if (atom x)
;;       state
;;     (let ((state (save-topic (car x) all-topics dir topics-fal state)))
;;       (save-topics-aux (cdr x) all-topics dir topics-fal state))))



;; (defun save-success-file (ntopics dir state)
;;   (b* ((file           (oslib::catpath dir "success.txt"))
;;        ((mv out state) (open-output-channel file :character state))
;;        ((mv & state)   (fmt "Successfully wrote ~x0 topics.~%~%"
;;                             (list (cons #\0 ntopics))
;;                             out state nil))
;;        (state          (close-output-channel out state)))
;;       state))

;; (defun prepare-dir (dir state)
;;   (b* (((unless (stringp dir))
;;         (prog2$ (er hard? 'prepare-dir "Dir must be a string, but is: ~x0.~%" dir)
;;                 state))
;;        (- (cw "; Preparing directory ~s0.~%" dir))
;;        (dir/xml     (oslib::catpath dir "xml"))
;;        (state       (oslib::mkdir! dir))
;;        (state       (oslib::mkdir! dir/xml))

;;        (dir-system   (acl2::f-get-global 'acl2::system-books-dir state))
;;        (xdoc-dir     (oslib::catpath dir-system "xdoc"))
;;        (xdoc/classic (oslib::catpath xdoc-dir "classic"))

;;        ;; We copy classic/Makefile-trans to dir/Makefile.  The "-trans" part of
;;        ;; its name is just to prevent people from thinking they can type "make"
;;        ;; in the classic directory to accomplish anything.
;;        (Makefile-trans (oslib::catpath xdoc/classic "Makefile-trans"))
;;        (Makefile-out   (oslib::catpath dir "Makefile"))
;;        (state   (stupid-copy-file Makefile-trans Makefile-out state))
;;        (state   (stupid-copy-files xdoc/classic
;;                                    (list "xdoc.css"
;;                                          "xdoc.js"
;;                                          "plus.png"
;;                                          "minus.png"
;;                                          "leaf.png"
;;                                          "text-topic.xsl"
;;                                          "html-core.xsl"
;;                                          "html-topic.xsl"
;;                                          "html-full-index.xsl"
;;                                          "html-brief-index.xsl"
;;                                          "html-topic-index.xsl"
;;                                          "xml-topic.xsl"
;;                                          "xml-topic-index.xsl"
;;                                          "xml-full-index.xsl")
;;                                    dir/xml state))
;;        (state   (stupid-copy-files xdoc/classic
;;                                    (list "frames2.html"
;;                                          "frames3.html"
;;                                          "preview.html")
;;                                    dir state))
;;        (state   (stupid-copy-files xdoc/classic
;;                                    *acl2-graphics*
;;                                    dir/xml state)))
;;     state))

;; (defun save-topics (x dir index-pkg expand-level state)
;;   (b* ((state (prepare-dir dir state))
;;        (dir   (oslib::catpath dir "xml"))
;;        (x     (clean-topics x))
;;        (- (cw "; Processing ~x0 topics.~%" (len x)))
;;        ;; Note: generate the index after the topic files, so that
;;        ;; errors in short messages will be seen there.
;;        (x      (time$ (normalize-parents-list x)
;;                       :msg "; Normalizing parents: ~st sec, ~sa bytes~%"
;;                       :mintime 1/2))
;;        (topics-fal (time$ (topics-fal x)
;;                           :msg "; Generating topics fal: ~st sec, ~sa bytes~%"
;;                           :mintime 1/2))
;;        (state  (time$ (save-topics-aux x x dir topics-fal state)
;;                       :msg "; Saving topics: ~st sec, ~sa bytes~%"
;;                       :mintime 1/2))
;;        (state  (time$ (save-index x dir topics-fal index-pkg state)
;;                       :msg "; Saving flat index: ~st sec, ~sa bytes~%"
;;                       :mintime 1/2))
;;        (state  (time$ (save-hierarchy x dir topics-fal index-pkg expand-level state)
;;                       :msg "; Saving hierarchical index: ~st sec, ~sa bytes~%"))
;;        (orphans (find-orphaned-topics x topics-fal nil))
;;        (-       (fast-alist-free topics-fal))
;;        (state   (save-success-file (len x) dir state)))
;;     (or (not orphans)
;;         (cw "~|~%WARNING: found topics with non-existent parents:~%~x0~%These ~
;;              topics may only show up in the index pages.~%~%" orphans))
;;     state))

