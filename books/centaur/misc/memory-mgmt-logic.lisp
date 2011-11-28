; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

; memory-mgmt-logic.lisp
;
; Note: This book should be included in conjunction with memory-mgmt-raw.lisp;
; otherwise, these functions won't do much of anything interesting.

(in-package "ACL2")

(defun hons-analyze-memory (slowp)
  (declare (xargs :guard t)
           (ignore slowp))
  (er hard? 'hons-analyze-memory "Raw lisp definition not installed?"))

(defun maybe-wash-memory-fn (n clear)
  (declare (xargs :guard t)
           (ignore n clear))
  (cw "maybe-wash-memory is defined under the hood~%"))

(defmacro maybe-wash-memory (n &optional clear)
  `(maybe-wash-memory-fn ,n ,clear))

(add-macro-alias maybe-wash-memory maybe-wash-memory-fn)


(defun set-max-mem (n)

; On CCL, this basically means, "try to stay within about N gigabytes of memory."
;
; The cert.pl build system scans for calls of set-max-mem.  Loosely speaking, if
; a book contains somethign like:
;
;   (value-triple (set-max-mem (* 4 (expt 2 30))))
;
; Then a memory limit of 4 GB (plus some padding) will be placed on the job.
; This limit is probably ignored unless you are using a clustering system like
; PBS.
;
; NOTE: A perl script is going to parse this, so for this to work you can't
; just use an arbitrary Lisp expression here.  Explicitly supported expressions
; are: (* n (expt 2 30)) and (expt 2 n).

  (declare (xargs :guard t)
           (ignore n))
  (cw "set-max-mem is defined under the hood~%"))


(defun print-rwx-size ()
  (declare (xargs :guard t))
  (cw "print-rwx-size is defined under the hood~%"))


(defun last-chance-wash-memory-fn ()
  (declare (xargs :guard t))
  ;; Sol: I removed this printing because in certain places I use BDD functions
  ;; without loading the -raw book, and if it prints this line each time it's
  ;; messy.
  ;; (cw "last-chance-wash-memory is defined under the hood~%")
  nil)

(defmacro last-chance-wash-memory ()
  `(last-chance-wash-memory-fn))

(add-macro-alias last-chance-wash-memory last-chance-wash-memory-fn)


(defund set-max-time (minutes)

; In ACL2, this does nothing.
;
; The cert.pl build system scans for calls of set-max-time.  Loosely speaking,
; if a book contains something like:
;
;   (value-triple (set-max-time 10))
;
; Then this means a time limit of 10 minutes should be put on the job.  This
; time limit is probably ignored unless you are using a clustering system like
; PBS.  We generally use a time limit of 3 hours as the default, so that we
; only need to include a set-max-time command in books that take a really long
; time to certify.
;
; NOTE: A perl script is going to parse this directive, so the argument should
; typically be a constant number, rather than any kind of complex expression.
; It also needs to be on the same line as the set-max-time call, etc.
;
; We generally interpret this as, "There's no way this book should ever take
; longer than 10 minutes, so just kill the job if it hasn't finished within
; that amount of time."

  (declare (xargs :guard t)
           (ignore minutes))
  nil)


(in-theory (disable maybe-wash-memory
                    (maybe-wash-memory)
                    (:type-prescription maybe-wash-memory-fn)
                    last-chance-wash-memory
                    (last-chance-wash-memory)
                    (:type-prescription last-chance-wash-memory-fn)
                    set-max-mem
                    (set-max-mem)
                    (:type-prescription set-max-mem)))

