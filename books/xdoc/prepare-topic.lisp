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
(include-book "base")
(include-book "std/osets/top" :dir :system)
(include-book "preprocess")
(include-book "parse-xml")
(program)
(set-state-ok t)

(defun find-children-aux (par x)

; Gather names of all xdoc topics in x which have parent par.  I.e., this finds
; the immediate children.

  (b* (((when (atom x))
        nil)
       ((when (member par (cdr (assoc :parents (car x)))))
        (cons (cdr (assoc :name (car x)))
              (find-children-aux par (cdr x)))))
    (find-children-aux par (cdr x))))

(defun find-children (par x)

; Gather names of immediate children topics and sort them.

  (mergesort (find-children-aux par x)))


(defconst *xml-entity-stuff*
  "<!DOCTYPE xdoc [
  <!ENTITY mdash \"&#8212;\">
  <!ENTITY rarr \"&#8594;\">
  <!ENTITY nbsp \"&#160;\">
  <!ENTITY lsquo \"&#8216;\">
  <!ENTITY rsquo \"&#8217;\">
  <!ENTITY ldquo \"&#8220;\">
  <!ENTITY rdquo \"&#8221;\">
]>
")

(defun gather-topic-names (x)
  (if (atom x)
      nil
    (cons (cdr (assoc :name (car x)))
          (gather-topic-names (cdr x)))))

(defun topics-fal (x)
  (make-fast-alist (pairlis$ (gather-topic-names x) x)))


; ------------------ Making Flat Indexes ------------------------

(defun index-add-topic (x topics-fal index-pkg state acc)

; X is a single topic entry in the xdoc table.  Index-pkg says the base package
; for symbols seen from the index.

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
       ((mv acc state) (preprocess-main short name topics-fal base-pkg state acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "</index_body>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::revappend-chars "</index_entry>" acc))
       (acc   (cons #\Newline acc)))
      (mv acc state)))

(defun index-add-topics (x topics-fal index-pkg state acc)

; X is a list of topics.  Index-pkg says the base package for these symbols.

  (b* (((when (atom x))
        (mv acc state))
       ((mv acc state)
        (index-add-topic (car x) topics-fal index-pkg state acc)))
    (index-add-topics (cdr x) topics-fal index-pkg state acc)))

(defun index-topics (x title topics-fal index-pkg state acc)

; X is a list of topics.  Generate <index>...</index> for these topics and
; add to acc.

  (b* ((acc (str::revappend-chars "<index title=\"" acc))
       (acc (str::revappend-chars title acc))
       (acc (str::revappend-chars "\">" acc))
       (acc (cons #\Newline acc))
       ((mv acc state) (index-add-topics x topics-fal index-pkg state acc))
       (acc (str::revappend-chars "</index>" acc))
       (acc (cons #\Newline acc)))
      (mv acc state)))

(defun add-parents (parents base-pkg acc)
  (b* (((when (atom parents))
        acc)
       (acc (str::revappend-chars "<parent topic=\"" acc))
       (acc (file-name-mangle (car parents) acc))
       (acc (str::revappend-chars "\">" acc))
       (acc (sym-mangle-cap (car parents) base-pkg acc))
       (acc (str::revappend-chars "</parent>" acc))
       (acc (cons #\Newline acc)))
    (add-parents (cdr parents) base-pkg acc)))

(defun gather-topics (names topics-fal)

; Given a list of topic names, get their entries.  Requires that all topics
; exist!

  (b* (((when (atom names))
        nil)
       (look (hons-get (car names) topics-fal))
       ((unless look)
        (er hard? 'gather-topics "Failed to find topic ~x0." (car names))))
    (cons (cdr look)
          (gather-topics (cdr names) topics-fal))))

(defun check-topic-syntax (x)
  (b* ((name     (cdr (assoc :name x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (short    (or (cdr (assoc :short x)) ""))
       (long     (or (cdr (assoc :long x)) ""))
       (parents  (cdr (assoc :parents x)))
       (suborder (cdr (assoc :suborder x)))
       ((unless (symbolp name))
        (er hard? 'check-topic-wellformed "Name is not a symbol: ~x0" x))
       ((unless (symbolp base-pkg))
        (er hard? 'check-topic-wellformed "Base-pkg is not a symbol: ~x0" x))
       ((unless (symbol-listp parents))
        (er hard? 'check-topic-wellformed "Parents are not a symbol-listp: ~x0" x))
       ((unless (stringp short))
        (er hard? 'check-topic-wellformed "Short is not a string or nil: ~x0" x))
       ((unless (stringp long))
        (er hard? 'check-topic-wellformed "Long is not a string or nil: ~x0" x))
       ((unless (symbol-listp suborder))
        (er hard? 'check-topic-wellformed "Suborder is not a symbol-listp: ~x0" x)))
    t))

(defun apply-suborder (suborder children-names)
  ;; should return some permutation of children-names
  (cond ((atom suborder)
         children-names)
        ((member (car suborder) children-names)
         (cons (car suborder)
               (apply-suborder (cdr suborder)
                               (remove (car suborder) children-names))))
        (t
         (apply-suborder (cdr suborder) children-names))))

(defun preprocess-topic (x all-topics topics-fal disable-autolinking-p state)
  (b* ((- (check-topic-syntax x))
       (name     (cdr (assoc :name x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (short    (or (cdr (assoc :short x)) ""))
       (long     (or (cdr (assoc :long x)) ""))
       (parents  (cdr (assoc :parents x)))
       (suborder (cdr (assoc :suborder x)))

       (acc    nil)
       (acc    (str::revappend-chars "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<?xml-stylesheet type=\"text/xsl\" href=\"xml-topic.xsl\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars *xml-entity-stuff* acc))
       (acc    (str::revappend-chars "<page>" acc))
       (acc    (str::revappend-chars "<topic name=\"" acc))
       (acc    (sym-mangle-cap name base-pkg acc))
       (acc    (str::revappend-chars "\">" acc))
       (acc    (cons #\Newline acc))
       (acc    (add-parents parents base-pkg acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<short>" acc))

       ((mv short-acc state)
        (preprocess-main short name
                         (if disable-autolinking-p
                             nil
                           topics-fal)
                         base-pkg state nil))
       (short-str  (str::rchars-to-string short-acc))

       ((mv err &) (parse-xml short-str))
       (state
        (if (and err (xdoc-verbose-p))
            (pprogn
               (fms "~|~%WARNING: problem with :short in topic ~x0:~%"
                    (list (cons #\0 name))
                    *standard-co* state nil)
               (princ$ err *standard-co* state)
               (fms "~%~%" nil *standard-co* state nil))
          state))

       (acc (b* (((unless err)
                  (append short-acc acc))
                 (acc (str::revappend-chars "<b>Markup error in :short: </b><code>" acc))
                 (acc (simple-html-encode-str err 0 (length err) acc))
                 (acc (str::revappend-chars "</code>" acc)))
              acc))

       (acc    (str::revappend-chars "</short>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "<long>" acc))

       ((mv long-acc state)
        (preprocess-main long name
                         (if disable-autolinking-p
                             nil
                           topics-fal)
                         base-pkg state nil))
       (long-str (str::rchars-to-string long-acc))
       ((mv err &) (parse-xml long-str))

       (state
        (if (and err (xdoc-verbose-p))
            (pprogn
               (fms "~|~%WARNING: problem with :long in topic ~x0:~%"
                    (list (cons #\0 name))
                    *standard-co* state nil)
               (princ$ err *standard-co* state)
               (fms "~%~%" nil *standard-co* state nil))
          state))

       (acc (b* (((unless err)
                  (append long-acc acc))
                 (acc (str::revappend-chars "<h3>Markup error in :long</h3><code>" acc))
                 (acc (simple-html-encode-str err 0 (length err) acc))
                 (acc (str::revappend-chars "</code>" acc)))
              acc))

       (acc    (str::revappend-chars "</long>" acc))
       (acc    (cons #\Newline acc))

       (children-names
        ;; note: all children-names are known to be existing topics, since
        ;; otherwise we wouldn't have found them.  topics mentioned in
        ;; suborder, however, may not exist
        (find-children name all-topics))
       (- (and (xdoc-verbose-p)
               (not (subsetp suborder children-names))
               (cw "~|~%WARNING: in topic ~x0, subtopic order mentions topics that ~
                    are not children: ~&1.~%"
                   name (set-difference$ suborder children-names))))
       (children-names
        ;; this returns a permutation of the original children-names, so they
        ;; must all exist
        (apply-suborder suborder children-names))
       (children-topics
        ;; safe to call gather-topics because we know all children-names exist.
        (gather-topics children-names topics-fal))
       ((mv acc state)
        (if (not children-topics)
            (mv acc state)
          (index-topics children-topics "Subtopics" topics-fal base-pkg state acc)))

       (acc    (str::revappend-chars "</topic>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::revappend-chars "</page>" acc))
       (acc    (cons #\Newline acc)))
      (mv (str::rchars-to-string acc) state)))
