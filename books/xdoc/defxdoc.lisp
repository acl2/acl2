; XDOC Documentation System for ACL2
; Copyright (C) 2009 Centaur Technology
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "XDOC")

(table xdoc 'doc nil)

(defun get-xdoc-table (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'doc (table-alist 'xdoc world))))

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

(defmacro defxdoc (name &key parents short long)
  (declare (xargs :guard (guard-for-defxdoc name parents short long)))
  `(make-event
    (let* ((pkg   (acl2::f-get-global 'current-package state))
           (entry (list (cons :name ',name)
                        (cons :base-pkg (acl2::pkg-witness pkg))
                        (cons :parents ',parents)
                        (cons :short ',short)
                        (cons :long ',long))))
     `(table xdoc 'doc
             (cons ',entry (get-xdoc-table world))))))

(defun defxdoc-raw-fn (name parents short long)
  (declare (xargs :guard t)
           (ignore name parents short long))
  (er hard? 'defxdoc-raw-fn
      "Under-the-hood definition of defxdoc-raw-fn not installed.  You ~
       probably need to load the defxdoc-raw book."))

(defmacro defxdoc-raw (name &key parents short long)
  (declare (xargs :guard (guard-for-defxdoc name parents short long)))
  `(defxdoc-raw-fn ',name ',parents ',short ',long))

