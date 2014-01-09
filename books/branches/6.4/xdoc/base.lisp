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

; base.lisp -- This file is only intended mainly to avoid a circular dependence
; between top.lisp and topics.lisp.  Ordinary users should include top.lisp
; instead.

(in-package "XDOC")
(set-state-ok t)

(table xdoc 'doc nil)
(table xdoc 'default-parents nil)
(table xdoc 'post-defxdoc-event nil)

(defun get-xdoc-table (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'doc (table-alist 'xdoc world))))

(defmacro set-default-parents (&rest parents)
  `(table xdoc 'default-parents
          (let ((parents ',parents))
            (cond ((symbol-listp parents)
                   parents)
                  ((and (consp parents)
                        (atom (cdr parents))
                        (symbol-listp (car parents)))
                   (car parents))
                  (t
                   (er hard? 'set-default-parents
                       "Expected a symbol-listp, but found ~x0" parents))))))

(defun get-default-parents (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'default-parents (table-alist 'xdoc world))))

(defun guard-for-defxdoc (name parents short long)
  (declare (xargs :guard t))
  (and (or (symbolp name)
           (cw "name is not a symbol!~%"))
       (or (symbol-listp parents)
           (cw ":parents are not a symbol list~%"))
       (or (not short)
           (stringp short)
           (cw ":short is not a string (or nil)~%"))
       (or (not long)
           (stringp long)
           (cw ":long is not a string (or nil)~%"))))

(defun normalize-bookname (bookname state)
  (let* ((dir-system (acl2::f-get-global 'acl2::system-books-dir state))
         (lds        (length dir-system)))
    ;; Eventually we could do something fancier to support
    ;; add-include-book-dirs, but this is probably fine for the Community
    ;; Books, at least.
    (if (and (stringp dir-system)
             (stringp bookname)
             (<= lds (length bookname))
             (equal dir-system (subseq bookname 0 lds)))
        (concatenate 'string "[books]/"
                     (subseq bookname lds nil))
      bookname)))

(defmacro defxdoc (name &key parents short long)
  (declare (xargs :guard (guard-for-defxdoc name parents short long)))
  `(with-output :off (event summary)
    (make-event
     (let* ((world (w state))
            (pkg   (acl2::f-get-global 'acl2::current-package state))
            (info  (acl2::f-get-global 'acl2::certify-book-info state))
            (bookname (if info
                          (acl2::access acl2::certify-book-info info :full-book-name)
                        "Current Interactive Session"))
            (bookname (normalize-bookname bookname state))
            (parents (or ',parents (get-default-parents (w state))))
            (entry (list (cons :name ',name)
                         (cons :base-pkg (acl2::pkg-witness pkg))
                         (cons :parents parents)
                         (cons :short ',short)
                         (cons :long ',long)
                         (cons :from bookname)))
            (table-event
             `(table xdoc 'doc
                     (cons ',entry (get-xdoc-table world))))
            (post-event
             (cdr (assoc-eq 'post-defxdoc-event (table-alist 'xdoc world)))))
       `(progn
          ,table-event
          ,@(and post-event (list post-event))
          (value-triple '(defxdoc ,',name)))))))

(defun defxdoc-raw-fn (name parents short long)
  (declare (xargs :guard t)
           (ignore name parents short long))
  (er hard? 'defxdoc-raw-fn
      "Under-the-hood definition of defxdoc-raw-fn not installed.  You ~
       probably need to load the defxdoc-raw book."))

(defmacro defxdoc-raw (name &key parents short long)
  (declare (xargs :guard (guard-for-defxdoc name parents short long)))
  `(defxdoc-raw-fn ',name ',parents ',short ',long))

(defun find-topic (name x)
  (declare (xargs :mode :program))

; Look up a particular topic by name in the list of topics.

  (if (atom x)
      nil
    (if (equal (cdr (assoc :name (car x))) name)
        (car x)
      (find-topic name (cdr x)))))
