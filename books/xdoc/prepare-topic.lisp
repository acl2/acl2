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
(include-book "xdoc-error")
(program)
(set-state-ok t)

(defun find-children-aux (par topics acc)

; At the top level, gather names of all xdoc topics in topics which have parent
; par.  I.e., this finds the immediate children.  In general, we accumulate
; those child names into acc; so at the top level, the child names will appear
; in the result in the reverse order from how they appear as names in topics.

  (cond ((atom topics)
         acc)
        ((member-eq par (cdr (assoc-eq :parents (car topics))))
         (find-children-aux par
                            (cdr topics)
                            (cons (cdr (assoc-eq :name (car topics)))
                                  acc)))
        (t
         (find-children-aux par (cdr topics) acc))))

(defun suborder-indicates-chronological-p (suborder)

; Returns true if and only if we are to list children in the order in which
; they were defined, rather than alphabetically.

  (if (consp suborder)
      (cdr (last suborder))
    suborder))

(defun find-children (par all-topics suborder)

; Gather names of immediate children topics and sort them.  Suborder is used
; for deciding whether to sort alphabetically or by order of appearance in
; all-topics (last ones first, where if a name is duplicated then its most
; recent appearance in all-topics (i.e., closest to the front of the list) is
; the significant one).

; Note that defxdoc (actually defxdoc-fn) pushes a new entry on the front of
; the xdoc table fetched by get-xdoc-table, which is called by all-xdoc-topics
; (in xdoc/defxdoc-raw-impl.lsp), which is called by the xdoc macro in
; xdoc/top.lisp.  Presumably other utilities, not just defxdoc, also push new
; topics on the front of the xdoc table.  So we assume that all-topics has the
; most recent entries at the front.

  (let ((children-names ; ordered as per comment above on "name is duplicated"
         (find-children-aux par all-topics nil)))
    (cond ((suborder-indicates-chronological-p suborder)
           (remove-duplicates-eq children-names))
          (t (mergesort children-names)))))

(defconst *xml-entity-stuff*
  "<!DOCTYPE xdoc [
  <!ENTITY ndash \"&#8211;\">
  <!ENTITY mdash \"&#8212;\">
  <!ENTITY rarr \"&#8594;\">
  <!ENTITY nbsp \"&#160;\">
  <!ENTITY lsquo \"&#8216;\">
  <!ENTITY rsquo \"&#8217;\">
  <!ENTITY ldquo \"&#8220;\">
  <!ENTITY rdquo \"&#8221;\">
]>
")


; ------------------ Making Flat Indexes ------------------------

(defun index-add-topic (x topics-fal disable-autolinking-p index-pkg state acc)

; X is a single topic entry in the xdoc table.  Index-pkg says the base package
; for symbols seen from the index.

  (b* ((name     (cdr (assoc :name x)))
       (short    (cdr (assoc :short x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (acc   (str::printtree-rconcat "<index_entry>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::printtree-rconcat "<index_head><see topic=\"" acc))
       (acc   (file-name-mangle name acc))
       (acc   (str::printtree-rconcat "\">" acc))
       (acc   (sym-mangle-cap name index-pkg nil acc))
       (acc   (str::printtree-rconcat "</see>" acc))
       (acc   (str::printtree-rconcat "</index_head>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::printtree-rconcat "<index_body>" acc))
       (acc   (cons #\Newline acc))
       ((mv acc state)
        (preprocess-main short name topics-fal disable-autolinking-p base-pkg
                         state acc))
       (acc   (cons #\Newline acc))
       (acc   (str::printtree-rconcat "</index_body>" acc))
       (acc   (cons #\Newline acc))
       (acc   (str::printtree-rconcat "</index_entry>" acc))
       (acc   (cons #\Newline acc)))
      (mv acc state)))

(defun index-add-topics (x topics-fal disable-autolinking-p index-pkg state
                           acc)

; X is a list of topics.  Index-pkg says the base package for these symbols.

  (b* (((when (atom x))
        (mv acc state))
       ((mv acc state)
        (index-add-topic (car x) topics-fal disable-autolinking-p index-pkg
                         state acc)))
    (index-add-topics (cdr x) topics-fal disable-autolinking-p index-pkg state
                      acc)))

(defun index-topics (x title topics-fal disable-autolinking-p index-pkg state
                       acc)

; X is a list of topics.  Generate <index>...</index> for these topics and
; add to acc.

  (b* ((acc (str::printtree-rconcat "<index title=\"" acc))
       (acc (str::printtree-rconcat title acc))
       (acc (str::printtree-rconcat "\">" acc))
       (acc (cons #\Newline acc))
       ((mv acc state) (index-add-topics x topics-fal disable-autolinking-p
                                         index-pkg state acc))
       (acc (str::printtree-rconcat "</index>" acc))
       (acc (cons #\Newline acc)))
      (mv acc state)))

(defun add-parents (parents base-pkg acc)
  (b* (((when (atom parents))
        acc)
       (acc (str::printtree-rconcat "<parent topic=\"" acc))
       (acc (file-name-mangle (car parents) acc))
       (acc (str::printtree-rconcat "\">" acc))
       (acc (sym-mangle-cap (car parents) base-pkg nil acc))
       (acc (str::printtree-rconcat "</parent>" acc))
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
       (ctx 'check-topic-syntax)
       ((unless (symbolp name))
        (er hard? ctx "Name is not a symbol: ~x0" x))
       ((unless (symbolp base-pkg))
        (er hard? ctx "Base-pkg is not a symbol: ~x0" x))
       ((unless (symbol-listp parents))
        (er hard? ctx "Parents are not a symbol-listp: ~x0" x))
       ((unless (stringp short))
        (er hard? ctx "Short is not a string or nil: ~x0" x))
       ((unless (stringp long))
        (er hard? ctx "Long is not a string or nil: ~x0" x))
       ((unless (symbol-listp (fix-true-list suborder)))
        (er hard? ctx "Suborder list contains a non-symbol: ~x0" x)))
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

(defun gentle-subsetp-eq (x y)

; This is just subsetp-eq, except that x need not be a true-list.

  (cond ((atom x) t)
        ((member-eq (car x) y)
         (gentle-subsetp-eq (cdr x) y))
        (t nil)))

(defun preprocess-topic (x all-topics topics-fal disable-autolinking-p state)
  (b* ((- (check-topic-syntax x))
       (name     (cdr (assoc :name x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (short    (or (cdr (assoc :short x)) ""))
       (long     (or (cdr (assoc :long x)) ""))
       (parents  (cdr (assoc :parents x)))
       (suborder (cdr (assoc :suborder x)))

       (acc    nil)
       (acc    (str::printtree-rconcat "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::printtree-rconcat "<?xml-stylesheet type=\"text/xsl\" href=\"xml-topic.xsl\"?>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::printtree-rconcat *xml-entity-stuff* acc))
       (acc    (str::printtree-rconcat "<page>" acc))
       (acc    (str::printtree-rconcat "<topic name=\"" acc))
       (acc    (sym-mangle-cap name base-pkg nil acc))
       (acc    (str::printtree-rconcat "\">" acc))
       (acc    (cons #\Newline acc))
       (acc    (add-parents parents base-pkg acc))
       (acc    (cons #\Newline acc))
       (acc    (str::printtree-rconcat "<short>" acc))

       ((mv short-acc state)
        (preprocess-main short name
                         topics-fal disable-autolinking-p
                         base-pkg state nil))
       (short-str  (str::printtree->str short-acc))

       ((mv err &) (parse-xml short-str))
       (state
        (if (and err (xdoc-verbose-p))
            (pprogn

; The following message formerly started with "WARNING" instead of "; xdoc
; error".  But we want to be consistent with the macro xdoc-error, to make it
; easy for users to search for a single string in the error log, namely, "xdoc
; error".  For the user, the difference between parsing errors and preprocessor
; errors seems small, not worth requiring searching for two different things.

             (prog2$ (note-xdoc-error) state)
             (fms "~|~%; xdoc error: problem with :short in topic ~x0:~%"
                  (list (cons #\0 name))
                  *standard-co* state nil) 
             (princ$ err *standard-co* state)
             (fms "~%~%" nil *standard-co* state nil))
          state))

       (acc (b* (((unless err)
                  (str::printtree-rconcat short-acc acc))
                 (acc (str::printtree-rconcat "<b>Markup error in :short: </b><code>" acc))
                 (acc (simple-html-encode-str err 0 (length err) acc))
                 (acc (str::printtree-rconcat "</code>" acc)))
              acc))

       (acc    (str::printtree-rconcat "</short>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::printtree-rconcat "<long>" acc))

       ((mv long-acc state)
        (preprocess-main long name
                         topics-fal disable-autolinking-p
                         base-pkg state nil))
       (long-str (str::printtree->str long-acc))
       ((mv err &) (parse-xml long-str))

       (state
        (if (and err (xdoc-verbose-p))
            (pprogn
             (prog2$ (note-xdoc-error) state)
; See comment above regarding the use of "; xdoc error" instead of "WARNING"
; just below.
             (fms "~|~%; xdoc error: problem with :long in topic ~x0:~%"
                  (list (cons #\0 name))
                  *standard-co* state nil)
             (princ$ err *standard-co* state)
             (fms "~%~%" nil *standard-co* state nil))
          state))

       (acc (b* (((unless err)
                  (str::printtree-rconcat long-acc acc))
                 (acc (str::printtree-rconcat "<h3>Markup error in :long</h3><code>" acc))
                 (acc (simple-html-encode-str err 0 (length err) acc))
                 (acc (str::printtree-rconcat "</code>" acc)))
              acc))

       (acc    (str::printtree-rconcat "</long>" acc))
       (acc    (cons #\Newline acc))

       (children-names
        ;; note: all children-names are known to be existing topics, since
        ;; otherwise we wouldn't have found them.  topics mentioned in
        ;; suborder, however, may not exist
        (find-children name all-topics suborder))
       (- (and (xdoc-verbose-p)
               (not (gentle-subsetp-eq suborder children-names))
               (cw "~|~%WARNING: in topic ~x0, subtopic order mentions topics that ~
                    are not children: ~&1.~%"
                   name (set-difference$ (fix-true-list suborder) children-names))))
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
          (index-topics children-topics "Subtopics"
                        topics-fal disable-autolinking-p
                        base-pkg state acc)))
       (acc    (str::printtree-rconcat "</topic>" acc))
       (acc    (cons #\Newline acc))
       (acc    (str::printtree-rconcat "</page>" acc))
       (acc    (cons #\Newline acc)))
      (mv (str::printtree->str acc) state)))
