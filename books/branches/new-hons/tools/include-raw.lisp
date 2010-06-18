; Include raw Lisp files in ACL2 books
; Copyright (C) 2010 Centaur Technology
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
; Original authors: Jared Davis and Sol Swords <{jared,sswords}@centtech.com>


(in-package "ACL2")

(defttag include-raw)

(progn!
 (set-raw-mode t)
 
 (defun raw-compile (name state)
   (compile-file
    (extend-pathname (cbd) name state))
   nil)

 (defun raw-load (name state)
   (let* ((fname (extend-pathname (cbd) name state))
          (compiled-fname (compile-file-pathname fname)))
     (handler-case
      (load compiled-fname)
      (error (condition)
             (format t "Compiled file ~a failed to load; loading uncompiled ~a.~%Message: ~a~%"
                     (namestring compiled-fname)
                     fname condition)
             (load fname))))))


(defmacro include-raw (fname)
  ":doc-section miscellaneous
Include a raw Lisp file in an ACL2 book, with compilation~/

Note:  You must have a TTAG defined in order to use this macro.

Usage: (include-raw ``my-raw-lisp-file.lsp'')

The path of the raw Lisp file must be given relative to the book containing the
include-raw form.

The raw Lisp file will be compiled and loaded when the containing book is
certified.  When including the book, the compiled file will be loaded if
possible, otherwise the original file will be loaded instead. ~/~/"
  `(make-event
    (mv-let (erp val state)
      ;; This progn!, including the compilation of the file to be loaded,
      ;; will only happen during make-event expansion; that is, during
      ;; certification, top-level evaluation, or uncertified inclusion (any
      ;; other situations?)  Is this correct behavior?
      ;;  - It is intentional that this _does_ happen during
      ;; certification, which seems like a good time to compile files
      ;; associated with the book being certified; in particular, hopefully
      ;; the same book is not being certified multiple times simultaneously.
      ;;  - It is intentional that this does _not_ happen during
      ;; certified inclusion, because this may interfere with parallel
      ;; certification: certifications of several files may simultaneously
      ;; include the containing book and try to compile the file, stomping
      ;; over each other's output.  Furthermore, if the book is certified,
      ;; then the compiled file should already exist.
      ;;  - In top-level evaluation/uncertified inclusion, it seems like a
      ;; toss-up.  We prefer to perform the compilation to ensure the
      ;; compiled file exists, so that compiled code is loaded and
      ;; subsequent performance (in Lisps that don't compile automatically)
      ;; is similar to that obtained by loading the certified book.
      (progn!
       (set-raw-mode t)
       (raw-compile ,fname state))
      (declare (ignore erp val))
      (value '(progn!
               (set-raw-mode t)
               (raw-load ,fname state)
               (value-triple ,fname))))))

