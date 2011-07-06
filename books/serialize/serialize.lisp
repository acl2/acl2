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

(include-book "tools/include-raw" :dir :system)
;; (depends-on "serialize-raw.lsp")


(make-event
 (prog2$
  (cw "Note: the serialize/serialize book is deprecated; see :doc ~
       serialize-deprecated for details.~%")
  '(value-triple :invisible))
 :check-expansion t)

(defdoc serialize-deprecated
  ":Doc-Section serialize
Why serialize/serialize is deprecated and its replacement~/

Serialize has been improved and moved into the ACL2 sources (currently in the
Hons extension) so that it can be used to write certificate files and so forth.
Generally you should stop using serialize::read and serialize::write, and
instead use the new functions serialize-read and serialize-write, which are
built into ACL2.

Compatibility Notes!

As part of this migration, the file format has been slightly changed to improve
compression and to allow for the \"smart\" restoration of honses.

 - The new ACL2 serialize-read function can still read files that are produced
   by serialize::write.

 - The new ACL2 serialize-write function produces files that are NOT compatible
   with serialize::read.  You will get \"magic number\" errors if you try to
   load these files with serialize::read.

The unsound-read book is still useful, and it has been adjusted so that it uses
the new, built-in ACL2 routines, and can read either format.~/~/")


(defttag :serialize)

(remove-untouchable 'read-acl2-oracle t)

(defun read-fn (filename honsp verbosep state)
  (declare (xargs :guard (and (stringp filename)
                              (member-eq honsp '(t nil :static))
                              (booleanp verbosep)
                              (state-p state))
                  :stobjs state)
           (ignore filename honsp verbosep))
  (prog2$
   (er hard? 'read-fn "Raw-lisp definition not installed??")
   (mv-let (erp val state)
           (read-acl2-oracle state)
           (declare (ignore erp))
           (mv val state))))

(defun write-fn (filename obj verbosep symbol-table-size number-table-size
                          string-table-size cons-table-size package-table-size
                          state)
  (declare (xargs :guard (and (stringp filename)
                              (booleanp verbosep)
                              (or (not symbol-table-size)
                                  (posp symbol-table-size))
                              (or (not number-table-size)
                                  (posp number-table-size))
                              (or (not string-table-size)
                                  (posp string-table-size))
                              (or (not cons-table-size)
                                  (posp cons-table-size))
                              (or (not package-table-size)
                                  (posp package-table-size))
                              (state-p state))
                  :stobjs state)
           (ignore filename obj verbosep symbol-table-size number-table-size
                   string-table-size cons-table-size package-table-size))
  (prog2$
   (er hard? 'write-fn "Raw-lisp definition not installed??")
   (mv-let (erp val state)
           (read-acl2-oracle state)
           (declare (ignore erp val))
           state)))

(push-untouchable 'read-acl2-oracle t)

(defmacro read (filename &key honsp verbosep)
  `(read-fn ,filename ,honsp ,verbosep state))

(defmacro write (filename obj &key
                          verbosep
                          symbol-table-size
                          number-table-size
                          string-table-size
                          cons-table-size
                          package-table-size)
  `(write-fn ,filename ,obj ,verbosep ,symbol-table-size ,number-table-size
             ,string-table-size ,cons-table-size ,package-table-size
             state))

(ACL2::include-raw "serialize-raw.lsp")

;; (make-event
;;  (mv-let (erp val state)
;;    (ACL2::progn!
;;     (set-raw-mode t)
;;     (unless (eq (get-global 'ACL2::host-lisp state) :gcl)
;;       (let ((f (namestring
;;                 (compile-file (ACL2::extend-pathname (cbd) "serialize-raw.lsp"
;;                                                      state)))))
;;         (assign serialize-raw-compiled-file f))))
;;    (declare (ignore erp val))
;;    (ACL2::value `(ACL2::progn!
;;                   (set-raw-mode t)
;;                   (ACL2::load-compiled ,(@ serialize-raw-compiled-file))))))
