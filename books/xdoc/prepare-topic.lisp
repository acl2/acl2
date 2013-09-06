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

(in-package "XDOC")
(include-book "base")
(include-book "sort")
(include-book "preprocess")
(include-book "parse-xml")
(program)
(set-state-ok t)

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


(defconst *xml-entity-stuff*
  "<!DOCTYPE xdoc [
  <!ENTITY mdash \"&#8212;\">
  <!ENTITY rarr \"&#8594;\">
  <!ENTITY nbsp \"&#160;\">
]>
")


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
        (preprocess-main short dir topics-fal base-pkg state nil))
       (short-str  (str::rchars-to-string short-acc))

       ((mv err &) (parse-xml short-str))
       (state
        (if err
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

       ((mv long-acc state) (preprocess-main long dir topics-fal base-pkg state nil))
       (long-str (str::rchars-to-string long-acc))
       ((mv err &) (parse-xml long-str))

       (state
        (if err
            (pprogn
               (fms "~|~%WARNING: problem with :long in topic ~x0:~%"
                    (list (cons #\0 name))
                    *standard-co* state nil)
               (princ$ err *standard-co* state)
               (fms "~%~%" nil *standard-co* state nil))
          state))

       (acc (b* (((unless err)
                  (append long-acc acc))
                 (acc (str::revappend-chars "<h3>Markup error in :long</h3></code>" acc))
                 (acc (simple-html-encode-str err 0 (length err) acc))
                 (acc (str::revappend-chars "</code>" acc)))
              acc))

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
      (mv (str::rchars-to-string acc) state)))