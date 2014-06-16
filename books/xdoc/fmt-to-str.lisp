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


; fmt-to-str.lisp -- alternative to fmt-to-string with narrower margins
; and downcased symbols

(in-package "XDOC")
(include-book "tools/bstar" :dir :system)
(include-book "std/strings/pretty-program" :dir :system)
(include-book "str")
(set-state-ok t)
(program)

(defun fmt-to-str (x base-pkg)
  ;; Use ACL2's fancy new string-printing stuff to do pretty-printing
  (b* ((config (str::make-printconfig :hard-right-margin 68
                                      :print-lowercase t
                                      :home-package base-pkg)))
    (str::pretty x :config config)))

(defun fmt-and-encode-to-acc (x base-pkg acc)
  (b* ((str (fmt-to-str x base-pkg))
       (acc (simple-html-encode-str str 0 (length str) acc)))
    acc))

