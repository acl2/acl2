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

; save.lisp
;
; This file defines the XDOC functions for running the preprocessor and saving
; XML files.  Note that the save-topics command we introduce cannot actually be
; used unless the mkdir-raw book is loaded first.  This is automatically handled
; by the "save" macro in top.lisp.

(in-package "XDOC")
(include-book "mkdir")
(include-book "../xdoc/base")
(include-book "preprocess")
(include-book "parse-xml")
(include-book "sort")
(set-state-ok t)

(defun cw-princ$ (str)
  ;; Same as princ$ to *standard-co*, but doesn't require state.
  (declare (xargs :guard t))
  (mbe :logic nil
       :exec
       (wormhole 'cw-raw-wormhole
                 '(lambda (whs) whs)
                 nil
                 `(let ((state (princ$ ',str *standard-co* state)))
                    (value :q))
                 :ld-prompt nil
                 :ld-pre-eval-print nil
                 :ld-post-eval-print nil
                 :ld-verbose nil)))

(program)


; --------------------- File Copying ----------------------------

(defun stupid-copy-file-aux (in out state)

; In, out are channels.  Copy from in to out, one byte at a time.

  (mv-let (byte state)
          (read-byte$ in state)
          (if (not byte)
              state
            (let ((state (write-byte$ byte out state)))
              (stupid-copy-file-aux in out state)))))

(defun stupid-copy-file (src dest state)

; A stupid file copy routine, so we can copy our style files, etc.  We avoid
; using "system" because of memory problems with forking on huge images.

  (b* (((mv in state)  (open-input-channel src :byte state))
       ((mv out state) (open-output-channel dest :byte state))
       (state          (stupid-copy-file-aux in out state))
       (state          (close-input-channel in state))
       (state          (close-output-channel out state)))
      state))

(defun stupid-copy-files (srcdir filenames destdir state)
  (if (atom filenames)
      state
    (b* ((srcfile  (acl2::extend-pathname srcdir (car filenames) state))
         (destfile (acl2::extend-pathname destdir (car filenames) state))
         (state    (stupid-copy-file srcfile destfile state)))
        (stupid-copy-files srcdir (cdr filenames) destdir state))))



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

(defun normalize-parents-list (x)

; Clean up parents throughout all xdoc topics.

  (if (atom x)
      nil
    (cons (normalize-parents (car x))
          (normalize-parents-list (cdr x)))))

(defun find-roots (x)

; Gather names of all doc topics which have no parents.

  (if (atom x)
      nil
    (if (not (cdr  (assoc :parents (car x))))
        (cons (cdr (assoc :name (car x)))
              (find-roots (cdr x)))
      (find-roots (cdr x)))))

(defun find-children-aux (par x)

; Gather names of all xdoc topics in x which have parent par.  I.e., this finds
; the immediate children.

  (if (atom x)
      nil
    (if (member-equal par (cdr (assoc :parents (car x))))
        (cons (cdr (assoc :name (car x)))
              (find-children-aux par (cdr x)))
      (find-children-aux par (cdr x)))))

(defun find-children (par x)

; Gather names of immediate children topics and sort them.

  (mergesort (find-children-aux par x)))


(defun gather-topic-names (x)
  (if (atom x)
      nil
    (cons (cdr (assoc :name (car x)))
          (gather-topic-names (cdr x)))))

(defun topics-fal (x)
  (make-fast-alist (pairlis$ (gather-topic-names x) nil)))


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



(mutual-recursion

 (defun make-hierarchy-aux (path dir topics-fal index-pkg all id expand-level acc state)

; - Path is our current location in the hierarchy, and is used to avoid loops.
;   (The first element in path is the current topic we are on.)
;
; - Index-pkg is just used for symbol printing.
;
; - All is the list of all xdoc documentation topics.
;
; - ID is a number that we assign to this topic entry for hiding with
;   JavaScript.  (We don't use names because the topics might be repeated under
;   different parents).
;
; - Expand-level is how deep to expand topics, generally 1 by default.
;
; - Acc is the character list we are building.
;
; We return (MV ACC-PRIME ID-PRIME STATE)

   (b* ((name     (car path))
        (id-chars (list* #\t #\o #\p #\i #\c #\- (explode-atom id 10)))
        (depth    (len path))
        (children (find-children name all))
        (kind     (cond ((not children) "leaf")
                        ((< depth expand-level) "show")
                        (t "hide")))

        ((when    (member-equal name (cdr path)))
         (prog2$
          (er hard? 'make-hierarchy "Circular topic hierarchy.  Path is ~x0.~%" path)
          (mv acc id state)))

        (topic (find-topic name all))
        (short    (cdr (assoc :short topic)))
        (base-pkg (cdr (assoc :base-pkg topic)))

        (acc (str::revappend-chars "<hindex topic=\"" acc))
        (acc (file-name-mangle name acc))
        (acc (str::revappend-chars "\" id=\"" acc))
        (acc (revappend id-chars acc))
        (acc (str::revappend-chars "\" kind=\"" acc))
        (acc (str::revappend-chars kind acc))
        (acc (str::revappend-chars "\">" acc))
        (acc (cons #\Newline acc))

        (acc (str::revappend-chars "<hindex_name>" acc))
        (acc (sym-mangle-cap name index-pkg acc))
        (acc (str::revappend-chars "</hindex_name>" acc))
        (acc (cons #\Newline acc))

        (acc (str::revappend-chars "<hindex_short id=\"" acc))
        (acc (revappend id-chars acc))
        (acc (str::revappend-chars "\">" acc))
        ((mv acc state) (preprocess-main short dir topics-fal base-pkg state acc))
        (acc (str::revappend-chars "</hindex_short>" acc))

        (acc (str::revappend-chars "<hindex_children id=\"" acc))
        (acc (revappend id-chars acc))
        (acc (str::revappend-chars "\" kind=\"" acc))
        (acc (str::revappend-chars kind acc))
        (acc (str::revappend-chars "\">" acc))
        (acc (cons #\Newline acc))

        (id   (+ id 1))
        ((mv acc id state)
         (make-hierarchy-list-aux children path dir topics-fal index-pkg all id expand-level acc state))
        (acc (str::revappend-chars "</hindex_children>" acc))
        (acc (str::revappend-chars "</hindex>" acc))
        (acc (cons #\Newline acc)))
       (mv acc id state)))

 (defun make-hierarchy-list-aux (children path dir topics-fal index-pkg all id expand-level acc state)

; - Children are the children of this path.
; - Path is our current location in the hierarchy.

   (if (atom children)
       (mv acc id state)
     (b* (((mv acc id state)
           (make-hierarchy-aux (cons (car children) path) dir topics-fal index-pkg all id
                               expand-level acc state))
          ((mv acc id state)
           (make-hierarchy-list-aux (cdr children) path dir topics-fal index-pkg all id
                                    expand-level acc state)))
         (mv acc id state)))))

(defun save-hierarchy (x dir topics-fal index-pkg expand-level state)

; X is all topics.  We assume all parents are normalized.

  (b* ((roots (mergesort (find-roots x)))
       (acc   nil)
       (acc   (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xml-topic-index.xsl\"?>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<page>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<hindex_root>" acc))
       (acc   (cons #\Newline acc))
       ((mv acc & state) (make-hierarchy-list-aux roots nil dir topics-fal index-pkg x 0
                                                  expand-level acc state))
       (acc   (str::revappend-chars "</hindex_root>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "</page>" acc))
       (acc   (cons #\Newline acc))
       (filename (acl2::extend-pathname dir "topics.xml" state))
       ((mv channel state) (open-output-channel filename :character state))
       (state (princ$ (reverse (coerce acc 'string)) channel state))
       (state (close-output-channel channel state)))
      state))




; ------------------ Making Flat Indexes ------------------------

(defun index-add-topic (x dir topics-fal index-pkg state acc)

; X is a single topic entry in the xdoc table.  Index-pkg says the base package
; for symbols seen frmo the index.

  (b* ((name     (cdr (assoc :name x)))
       (short    (cdr (assoc :short x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (acc   (str::revappend-chars "<index_entry>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<index_head><see topic=\"" acc))
       (acc   (file-name-mangle name acc))
       (acc   (str::revappend-chars "\">" acc))
       (acc   (sym-mangle-cap name index-pkg acc))
       (acc   (str::revappend-chars "</see>" acc))
       (acc   (str::revappend-chars "</index_head>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "<index_body>" acc))
       (acc   (cons #\Newline acc))
       ((mv acc state) (preprocess-main short dir topics-fal base-pkg state acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "</index_body>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "</index_entry>" acc))
       (acc   (cons #\Newline acc)))
      (mv acc state)))

(defun index-add-topics (x dir topics-fal index-pkg state acc)

; X is a list of topics.  Index-pkg says the base package for these symbols.

  (if (atom x)
      (mv acc state)
    (b* (((mv acc state) (index-add-topic (car x) dir topics-fal index-pkg state acc)))
        (index-add-topics (cdr x) dir topics-fal index-pkg state acc))))

(defun index-topics (x title dir topics-fal index-pkg state acc)

; X is a list of topics.  Generate <index>...</index> for these topics and
; add to acc.

  (b* ((acc (str::revappend-chars "<index title=\"" acc))
       (acc (str::revappend-chars title acc))
       (acc (str::revappend-chars "\">" acc))
       (acc (cons #\Newline acc))
       ((mv acc state) (index-add-topics x dir topics-fal index-pkg state acc))
       (acc (str::revappend-chars "</index>" acc))
       (acc (cons #\Newline acc)))
      (mv acc state)))

(defun save-index (x dir topics-fal index-pkg state)

; Write index.xml for the whole list of all topics.

  (b* ((acc nil)
       (acc (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xml-full-index.xsl\"?>" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "<page>" acc))
       (acc (cons #\Newline acc))
       ((mv acc state) (index-topics x "Full Index" dir topics-fal index-pkg state acc))
       (acc (str::revappend-chars "</page>" acc))
       (filename (acl2::extend-pathname dir "index.xml" state))
       ((mv channel state) (open-output-channel filename :character state))
       (state (princ$ (reverse (coerce acc 'string)) channel state))
       (state (close-output-channel channel state)))
      state))




; -------------------- Making Topic Pages -----------------------

(defun add-parents (parents base-pkg acc)
  (if (atom parents)
      acc
    (let* ((acc (str::revappend-chars "<parent topic=\"" acc))
           (acc (file-name-mangle (car parents) acc))
           (acc (str::revappend-chars "\">" acc))
           (acc (sym-mangle-cap (car parents) base-pkg acc))
           (acc (str::revappend-chars "</parent>" acc))
           (acc (cons #\Newline acc)))
      (add-parents (cdr parents) base-pkg acc))))

(defun gather-topics (names all-topics)

; Given a list of topic names, get their entries from the list of all topics.

  (cond ((atom all-topics)
         nil)
        ((member (cdr (assoc :name (car all-topics))) names)
         (cons (car all-topics)
               (gather-topics names (cdr all-topics))))
        (t
         (gather-topics names (cdr all-topics)))))


(defun preprocess-topic (x all-topics dir topics-fal state)
  (b* ((name     (cdr (assoc :name x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (short    (or (cdr (assoc :short x)) ""))
       (long     (or (cdr (assoc :long x)) ""))
       (parents  (cdr (assoc :parents x)))
       ((unless (symbolp name))
        (mv (er hard? 'preprocess-topic "Name is not a string: ~x0.~%" x)
            state))
       ((unless (symbolp base-pkg))
        (mv (er hard? 'preprocess-topic "Base-pkg is not a symbol: ~x0.~%" base-pkg)
            state))
       ((unless (symbol-listp parents))
        (mv (er hard? 'preprocess-topic "Parents are not a symbol-listp: ~x0.~%" x)
            state))
       ((unless (stringp short))
        (mv (er hard? 'preprocess-topic "Short is not a string: ~x0.~%" x)
            state))
       ((unless (stringp long))
        (mv (er hard? 'preprocess-topic "Long is not a string: ~x0.~%" x)
            state))
       (acc    nil)
       (acc    (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xml-topic.xsl\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<page>" acc))
       (acc    (str::revappend-chars "<topic name=\"" acc))
       (acc    (sym-mangle-cap name base-pkg acc))
       (acc    (str::revappend-chars "\">" acc))
       (acc    (cons #\Newline acc))
       (acc    (add-parents parents base-pkg acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<short>" acc))

       ;; Previously: ((mv acc state) (preprocess-main short dir base-pkg state acc))

       ((mv short-acc state) (preprocess-main short dir topics-fal base-pkg state nil))
       (short-str  (reverse (coerce short-acc 'string)))
       (acc        (append short-acc acc))
       ((mv err &) (parse-xml short-str))
       (- (or (not err)
              (acl2::progn$
               (cw "~|~%WARNING: problem with :short in topic ~x0:~%" name)
               (cw-princ$ err)
               (cw "~%~%"))))

       (acc    (str::revappend-chars "</short>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<long>" acc))

       ;; Previously: ((mv acc state) (preprocess-main long dir base-pkg state acc))
       ((mv long-acc state) (preprocess-main long dir topics-fal base-pkg state nil))
       (long-str (reverse (coerce long-acc 'string)))
       (acc      (append long-acc acc))
       ((mv err &) (parse-xml long-str))
       (- (or (not err)
              (acl2::progn$
               (cw "~|~%WARNING: problem with :long in topic ~x0:~%" name)
               (cw-princ$ err)
               (cw "~%~%"))))

       (acc    (str::revappend-chars "</long>" acc))
       (acc    (cons #\Newline acc))

       (children (find-children name all-topics))
       (topics   (gather-topics children all-topics))

       ((mv acc state) (if (not topics)
                           (mv acc state)
                         (index-topics topics "Subtopics" dir topics-fal base-pkg state acc)))

       (acc    (str::revappend-chars "</topic>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "</page>" acc))
       (acc    (cons #\Newline acc)))
      (mv (reverse (coerce acc 'string)) state)))

(defun save-topic (x all-topics dir topics-fal state)
  (b* ((name               (cdr (assoc :name x)))
       (-                  (cw "Saving ~s0::~s1.~%" (symbol-package-name name) (symbol-name name)))
       ((mv text state)    (preprocess-topic x all-topics dir topics-fal state))
       (filename           (concatenate 'string
                                        (reverse (coerce (file-name-mangle name nil) 'string))
                                        ".xml"))
       (fullpath           (acl2::extend-pathname dir filename state))
       ((mv channel state) (open-output-channel fullpath :character state))
       (state              (princ$ text channel state))
       (state              (close-output-channel channel state)))
      state))

(defun save-topics-aux (x all-topics dir topics-fal state)
  (if (atom x)
      state
    (let ((state (save-topic (car x) all-topics dir topics-fal state)))
      (save-topics-aux (cdr x) all-topics dir topics-fal state))))



(defun save-success-file (ntopics dir state)
  (b* ((file           (acl2::extend-pathname dir "success.txt" state))
       ((mv out state) (open-output-channel file :character state))
       ((mv & state)   (fmt "Successfully wrote ~x0 topics.~%~%"
                            (list (cons #\0 ntopics))
                            out state nil))
       (state          (close-output-channel out state)))
      state))

(defun prepare-dir (dir state)
  (b* (((unless (stringp dir))
        (prog2$ (er hard? 'prepare-dir "Dir must be a string, but is: ~x0.~%" dir)
                state))
       (- (cw "; Preparing directory ~s0.~%" dir))
       (dir/xml     (acl2::extend-pathname dir "xml" state))
       (state       (mkdir dir state))
       (state       (mkdir dir/xml state))

;;       (dir/support (acl2::extend-pathname dir "support" state))
;;       (state       (mkdir dir/support state))

       (xdoc/support (acl2::extend-pathname *xdoc-dir* "support" state))

       ;; We copy support/Makefile-trans to dir/Makefile.  The "-trans" part of
       ;; its name is just to prevent people from thinking they can type "make"
       ;; in the support directory to accomplish anything.
       (Makefile-trans (acl2::extend-pathname xdoc/support "Makefile-trans" state))
       (Makefile-out   (acl2::extend-pathname dir "Makefile" state))
       (state   (stupid-copy-file Makefile-trans Makefile-out state))

       (state   (stupid-copy-files xdoc/support
                                   (list "xdoc.css"
                                         "xdoc.js"
                                         "plus.png"
                                         "minus.png"
                                         "leaf.png"
                                         "text-topic.xsl"
                                         "html-core.xsl"
                                         "html-topic.xsl"
                                         "html-full-index.xsl"
                                         "html-brief-index.xsl"
                                         "html-topic-index.xsl"
                                         "xml-topic.xsl"
                                         "xml-topic-index.xsl"
                                         "xml-full-index.xsl")
                                   dir/xml state))
       (state   (stupid-copy-files xdoc/support
                                   (list "frames2.html"
                                         "frames3.html"
                                         "preview.html")
                                   dir state)))
    state))

(defun save-topics (x dir index-pkg expand-level state)
  (b* ((state (prepare-dir dir state))
       (dir   (acl2::extend-pathname dir "xml" state))
       (- (cw "; Processing ~x0 topics.~%" (len x)))
       ;; Note: generate the index after the topic files, so that
       ;; errors in short messages will be seen there.
       (x      (time$ (normalize-parents-list x)
                      :msg "; Normalizing parents: ~st sec, ~sa bytes~%"
                      :mintime 1/2))
       (topics-fal (time$ (topics-fal x)
                          :msg "; Generating topics fal: ~st sec, ~sa bytes~%"
                          :mintime 1/2))
       (state  (time$ (save-topics-aux x x dir topics-fal state)
                      :msg "; Saving topics: ~st sec, ~sa bytes~%"
                      :mintime 1/2))
       (state  (time$ (save-index x dir topics-fal index-pkg state)
                      :msg "; Saving flat index: ~st sec, ~sa bytes~%"
                      :mintime 1/2))
       (state  (time$ (save-hierarchy x dir topics-fal index-pkg expand-level state)
                      :msg "; Saving hierarchical index: ~st sec, ~sa bytes~%"))
       (orphans (find-orphaned-topics x topics-fal nil))
       (-       (fast-alist-free topics-fal))
       (state   (save-success-file (len x) dir state)))
    (or (not orphans)
        (cw "~|~%WARNING: found topics with non-existent parents:~%~x0~%These ~
             topics may only show up in the index pages.~%~%" orphans))
    state))

