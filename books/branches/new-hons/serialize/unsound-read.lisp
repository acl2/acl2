; Serializing ACL2 Objects
; Copyright (C) 2009-2010 Centaur Technology
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

(in-package "SERIALIZE")
(include-book "serialize" :ttags (:serialize))

(defttag :unsound-read)

; We use this stub in the logical definition, so that you can't
; directly reason about the value of unsound-read.

(defstub unsound-read-fn-logical-def (filename honsp verbosep)
  t)

(defun unsound-read-fn (filename honsp verbosep)
  (declare (xargs :guard (and (stringp filename)
                              (member-eq honsp '(t nil :static))
                              (booleanp verbosep))))
  (prog2$
   (er hard? 'unsound-read-fn "Raw-lisp definition not installed??")
   (unsound-read-fn-logical-def filename honsp verbosep)))

(defmacro unsound-read (filename &key honsp verbosep)
  `(unsound-read-fn ,filename ,honsp ,verbosep))

(ACL2::progn!
 (set-raw-mode t)
 (unless (eq (get-global 'ACL2::host-lisp state) :gcl)
   (let ((f (compile-file (ACL2::extend-pathname (cbd) "unsound-read-raw.lsp" state))))
     (ACL2::load-compiled f))))
